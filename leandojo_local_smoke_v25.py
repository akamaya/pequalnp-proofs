"""LeanDojo-v2 v25: per-request Strata reasoning budget, configurable API timeout and output cap; v24 search retained."""
import argparse
from collections import Counter
import difflib
import hashlib
import math
import pickle
import subprocess
import unicodedata
import json
import os
import re
import time
import textwrap
import threading
from datetime import datetime
import urllib.request
import urllib.error
from pathlib import Path

import pantograph.server as ps
from pantograph.expr import Site
from pantograph.server import TacticFailure, ExprError
from pantograph.message import ServerError
from lean_dojo_v2.prover.base_prover import BaseProver
from pantograph.search import SearchResult


SUGGESTION = re.compile(r"\b(?:exact|apply|simp|simp_all|rw|aesop|omega|linarith|norm_num|ring|fun_prop|positivity|grind)\?")


def first_tactic(code):
    """Extract a conservative first tactic, not a general Lean parser.

    Preserve nested ``by`` and induction/match bodies, but discard later
    sibling tactics and constructor bullets. Ambiguous syntax is still
    subject to Lean validation.
    """
    lines = code.splitlines()
    if not lines or lines[0].startswith(('(', '·', 'case ', 'next =>')):
        return None
    head = lines[0]
    # For common atomic tactics, an inline sequencing operator marks the
    # next step. Do not split arbitrary terms, comments or nested syntax.
    if re.match(r'^(?:intro|intros|rintro|constructor|left|right|rw|simp|norm_num|omega|ring|linarith|nlinarith)\b', head):
        depth = 0
        quoted = False
        escaped = False
        for i, ch in enumerate(head):
            if quoted:
                if escaped:
                    escaped = False
                elif ch == '\\':
                    escaped = True
                elif ch == '"':
                    quoted = False
                continue
            if ch == '"':
                quoted = True
            elif head.startswith(('--', '/-'), i):
                break
            elif ch in '([{⟨':
                depth += 1
            elif ch in ')]}⟩':
                depth -= 1
            elif depth == 0 and (ch == ';' or head.startswith('<;>', i)):
                return head[:i].rstrip()
    keep = [head]
    for line in lines[1:]:
        stripped = line.lstrip()
        # A bullet/case after a simple goal-splitting tactic is a sibling,
        # not part of that tactic. Keep alternatives of induction/cases.
        if stripped.startswith(('·', 'case ', 'next =>')) and re.match(
            r'^(?:constructor|left|right|apply|refine|intro|intros|rintro)\b', head
        ) and not re.search(r'\bby\s*$', head):
            break
        if not stripped or line[0].isspace() or line.startswith(('|', ']', ')', '}')):
            keep.append(line)
        else:
            break
    return '\n'.join(keep).rstrip()


# A syntax guard, not a sandbox: only use a trusted local model and Lean environment.
FENCE = re.compile(r'^[ \t]*```[ \t]*(?:lean(?:[ \t]*4)?)?[ \t]*\r?\n(.*?)^[ \t]*```[ \t]*$', re.M | re.S | re.I)
FORBIDDEN = re.compile(r'\b(?:sorry|admit|native_decide|sorryAx|run_tac|run_elab|eval_tac|unsafe)\b')
DECLARATION = re.compile(r'(?m)^\s*(?:```|###|theorem\b|lemma\b|example\b|import\b|namespace\b|end\b|#\w+)')
TACTIC_START = re.compile(r'^(?:intro[s]?|rintro|rename_i|exact(?:_mod_cast)?|apply|refine|have|let|show|change|rw|erw|rewrite|simp(?:_all|_only)?|simpa|dsimp|unfold|fold|omega|linarith|nlinarith|norm_num|norm_cast|push_cast|ring(?:_nf)?|aesop|grind|decide|rfl|assumption|contradiction|exfalso|by_contra!?|by_cases|cases|rcases|obtain|induction|constructor|left|right|use|exists|subst|specialize|revert|clear|generalize|congr|ext|funext|calc|first|try|repeat|all_goals|any_goals|focus|classical|infer_instance|positivity|tauto|trivial|convert|split|fin_cases|interval_cases|set|suffices|filter_upwards|gcongr|bound|norm_num1|push_neg|not_iff|exact\?|apply\?|simp\?|simp_all\?)\b')


def strip_thought(text):
    text = re.sub(r'<think>.*?</think>', '', text, flags=re.S | re.I).strip()
    # Never interpret an unterminated thinking section as a tactic.
    m = re.search(r'<think>', text, re.I)
    return (text[:m.start()].strip(), True) if m else (text, False)


def extract_diagnosed(text, stepwise=False, max_chars=4000, max_lines=24):
    """Return candidate, reason, and optional conservative prefix; Lean validates it."""
    text, unfinished = strip_thought(text)
    if not text:
        return None, 'unfinished_think' if unfinished else 'empty_content', None
    fences = FENCE.findall(text)
    if '```' in text and not fences:
        return None, 'unclosed_or_invalid_fence', None
    code = textwrap.dedent(fences[-1] if fences else text).strip()
    decl = re.search(r'(?m)^\s*(?:theorem|lemma|example)\b', code)
    if decl:
        match = re.search(r':=\s*by\b', code[decl.start():])
        if not match:
            return None, 'declaration_without_body', None
        code = code[decl.start()+match.end():]
    elif re.match(r'^by\b', code):
        code = re.sub(r'^by\b', '', code, count=1)
    if code.startswith(' ') and not code.startswith('  ') and '\n' in code:
        code = code.lstrip(' ')
    code = textwrap.dedent(code).strip()
    if not code:
        return None, 'empty_code', None
    if FORBIDDEN.search(code):
        return None, 'forbidden_token', None
    if DECLARATION.search(code):
        return None, 'non_tactic_declaration', None
    if not fences and not TACTIC_START.match(code) and not code.startswith('('):
        return None, 'not_tactic_text', None
    # Remove only our standard parenthesized sequence wrapper if supplied.
    if code.startswith('(\n') and code.endswith('\n)'):
        code = textwrap.dedent(code[2:-2]).strip()
    def valid_atomic_prefix():
        prefix = first_tactic(code)
        if not prefix or prefix == code or FORBIDDEN.search(prefix) or DECLARATION.search(prefix):
            return None
        if SUGGESTION.search(prefix):
            return None
        return wrap_tactic(prefix) if len(prefix) <= max_chars and len(prefix.splitlines()) <= max_lines else None
    prefix = valid_atomic_prefix()
    if stepwise:
        code = first_tactic(code)
        if not code:
            return None, 'no_atomic_prefix', None
        prefix = None
    if SUGGESTION.search(code):
        # Pantograph TryThis is safe only as a standalone tactic.
        if not (len(code.splitlines()) == 1 and SUGGESTION.match(code) and not re.search(r';|<;>|\b(?:first|try|repeat)\b', code)):
            return (prefix, 'compound_suggestion_prefix', None) if prefix else (None, 'compound_suggestion', None)
    if len(code) > max_chars or len(code.splitlines()) > max_lines:
        return (prefix, 'oversized_prefix', None) if prefix else (None, 'oversized_block', None)
    return wrap_tactic(code), 'ok', prefix


def wrap_tactic(code):
    return '(\n' + textwrap.indent(code, '  ') + '\n)' if '\n' in code else code


def extract_tactic(text, stepwise=False):
    return extract_diagnosed(text, stepwise=stepwise)[0]


def receive_chat(response, show=False, stats=None):
    """Read OpenAI SSE; also accept ordinary JSON from non-streaming servers."""
    if 'text/event-stream' not in response.headers.get('Content-Type', '').lower():
        result = json.load(response)
        choice = result['choices'][0]
        msg = choice['message']
        reasoning = msg.get('reasoning_content') or msg.get('reasoning') or ''
        if stats is not None:
            stats['reasoning_chars'] = len(reasoning) if isinstance(reasoning, str) else 0
        if show and reasoning:
            print('[reasoning]', reasoning, flush=True)
        return msg.get('content') or '', choice.get('finish_reason'), result.get('usage')
    parts = []
    finish = None
    usage = None
    phase = None
    done = False
    for raw in response:
        line = raw.decode('utf-8').strip()
        if not line.startswith('data:'):
            continue
        data = line[5:].strip()
        if data == '[DONE]':
            done = True
            break
        chunk = json.loads(data)
        if chunk.get('error'):
            raise RuntimeError(str(chunk['error']))
        if chunk.get('usage') is not None:
            usage = chunk['usage']
        if not chunk.get('choices'):
            continue
        choice = chunk['choices'][0]
        delta = choice.get('delta') or {}
        for kind, value in [('reasoning', delta.get('reasoning_content') or delta.get('reasoning')), ('content', delta.get('content'))]:
            if not isinstance(value, str) or not value:
                continue
            if kind == 'content':
                parts.append(value)
            elif stats is not None:
                stats['reasoning_chars'] = stats.get('reasoning_chars', 0) + len(value)
            if show:
                if phase != kind:
                    print('\n[' + kind + '] ', end='', flush=True)
                    phase = kind
                print(value, end='', flush=True)
        if choice.get('finish_reason') is not None:
            finish = choice['finish_reason']
    if show:
        print(flush=True)
    if not done and finish is None:
        raise RuntimeError('Incomplete SSE response')
    return ''.join(parts), finish, usage


def state_signature(state):
    """Conservative visible-state fingerprint, excluding internal state/goal IDs.

    Preserve local declaration order, names and pretty-printed types/values.
    Sorting goals makes mere reordering count as no visible progress.
    This is a heuristic, not a proof of semantic equivalence.
    """
    return tuple(sorted(str(g).strip() for g in state.goals))


def heartbeat_timeout(exc):
    """Recognize only Lean's reported deterministic heartbeat exhaustion.
    Do not downgrade transport errors, crashes or arbitrary ServerErrors.
    """
    message = str(exc).lower()
    return ('deterministic' in message and 'timeout' in message
            and ('maximum number of heartbeats' in message or 'maxheartbeats' in message))


def display_goal(goal):
    """Keep the actual target and local types, omit only bank proof values.
    Ordinary let-bound data and the raw state signature are left intact.
    """
    variables = getattr(goal, 'variables', None)
    target = getattr(goal, 'target', None)
    if variables is None or not isinstance(target, str):
        return str(goal)
    if not any(getattr(x, 'name', '') and x.name.startswith('ld_mem_') and getattr(x, 'v', None)
               for x in variables):
        return str(goal)
    head = f"case {goal.name}\n" if getattr(goal, 'name', None) else ""
    locals_ = [f"{x.name} : {x.t}" if getattr(x, 'name', '') and x.name.startswith('ld_mem_')
               else str(x) for x in variables]
    mode = getattr(getattr(goal, 'mode', None), 'name', '')
    return head + '\n'.join(locals_) + ('\n| ' if mode == 'CONV' else '\n⊢ ') + target


RAG_BRANCH = re.compile(r"  \| \(apply ([\w'.]+) <;> \(first \| assumption \| rfl \| omega\)\)")


def rag_batch_names(tactic):
    """Recognize only the exact harness-generated batch syntax."""
    lines = str(tactic).splitlines()
    if len(lines) < 2 or lines[0] != 'first':
        return []
    matches = [RAG_BRANCH.fullmatch(line) for line in lines[1:]]
    return [m.group(1) for m in matches] if all(matches) else []


def budgeted_rag_tactic(name, budget):
    # Separate Pantograph calls avoid spending the entire shared first-batch
    # budget on one bad candidate. done ensures no partial proof is accepted.
    return (f'set_option maxHeartbeats {budget} in\n'
            f'  apply {name} <;> (first | assumption | rfl | omega)\n'
            '  done')


class FeedbackServer(ps.Server):
    """Observe search calls and record actual Lean transitions for replay."""
    prover = None
    replaying = False

    def goal_start(self, *args, **kwargs):
        state = super().goal_start(*args, **kwargs)
        if not self.replaying:
            self.paths = {state.state_id: ()}
            self.ancestors = {state.state_id: frozenset([state_signature(state)])}
            self.solved_path = None
            if self.prover is not None:
                self.prover.paths = self.paths
        return state

    rag_mode = 'isolated'
    rag_budgets = (10000, 50000, 200000)
    rag_retry_top = 2

    def try_rag_batch(self, state, tactic, names, site, kwargs):
        pending = list(names)
        last = None
        for stage, budget in enumerate(self.rag_budgets):
            timed_out = []
            for name in pending:
                if self.prover is not None:
                    self.prover.check_budget(check_calls=False)
                trial = budgeted_rag_tactic(name, budget)
                start = time.monotonic()
                try:
                    result = self.goal_tactic(state, trial, **kwargs)
                except TacticFailure as exc:
                    last = exc
                    timeout = heartbeat_timeout(exc)
                    print(f'[RAG TRIAL] {name} budget={budget} '
                          f'outcome={"timeout" if timeout else "failed"} '
                          f'wall={time.monotonic()-start:.3f}s', flush=True)
                    if timeout:
                        timed_out.append(name)
                else:
                    print(f'[RAG TRIAL] {name} budget={budget} outcome=success '
                          f'wall={time.monotonic()-start:.3f}s', flush=True)
                    return result
            pending = timed_out[:self.rag_retry_top]
            if not pending:
                break
        message = f'RAG candidate trials exhausted; last error: {last}'
        if self.prover is not None:
            self.prover.feedback[(state.state_id, site.goal_id, str(tactic))] = message[:3000]
            self.prover.local_failures[local_failure_key(display_goal(state.goals[site.goal_id]), str(tactic))] = message[:2000]
        raise TacticFailure(message)

    def goal_tactic(self, state, tactic, *args, **kwargs):
        # BaseProver supplies auto_resume=False, which can hide unsolved siblings.
        # Keep its goal choice, but explicitly request automatic continuation.
        if args:
            if len(args) != 1 or "site" in kwargs:
                raise RuntimeError("Unexpected goal_tactic arguments")
            site = args[0]
        else:
            site = kwargs.get("site", Site())
        site = Site(goal_id=site.goal_id, auto_resume=True)
        args, kwargs = (), {**kwargs, "site": site}
        if not self.replaying and self.rag_mode == 'isolated':
            names = rag_batch_names(tactic)
            if names:
                return self.try_rag_batch(state, tactic, names, site, kwargs)
        if not self.replaying:
            print(f'[TACTIC state={state.state_id}, goal={site.goal_id}]\n{tactic}', flush=True)
        try:
            try:
                result = super().goal_tactic(state, tactic, *args, **kwargs)
            except ServerError as exc:
                if self.replaying or not heartbeat_timeout(exc):
                    raise
                # Pantograph reported an error for this tactic, not a lost
                # connection. Retain the parent state for upstream search.
                print('[LEAN TIMEOUT] heartbeat limit; rejecting tactic', flush=True)
                raise TacticFailure(f'Lean heartbeat timeout: {exc}') from exc
            if not result.goals:
                try:
                    if self.goal_root(result) is None:
                        raise TacticFailure("Empty active goals but no complete proof root")
                except ExprError as exc:
                    raise TacticFailure(f"Incomplete or invalid root: {exc}") from exc
            if not self.replaying:
                if state.state_id not in self.paths:
                    raise RuntimeError(f'Unrecorded parent state {state.state_id}')
                previous = self.ancestors[state.state_id]
                signature = state_signature(result)
                if result.goals and signature in previous:
                    raise TacticFailure("NO PROGRESS: visible goals and hypotheses match a previous state on this path. Try a different tactic.")
                path = self.paths[state.state_id] + ((tactic, args, dict(kwargs)),)
                self.paths[result.state_id] = path
                self.ancestors[result.state_id] = previous | {signature}
                if not result.goals:
                    self.solved_path = path
                if self.prover is not None and self.prover.trace_path is not None:
                    record = {'state': result.state_id, 'parent': state.state_id,
                              'goal_id': site.goal_id, 'tactic': str(tactic),
                              'goals': [str(g) for g in result.goals],
                              'elapsed': time.monotonic()-self.prover.started}
                    with self.prover.trace_path.open('a', encoding='utf-8') as trace:
                        trace.write(json.dumps(record, ensure_ascii=False)+'\n')
                print(f'[LEAN] OK; remaining goals={len(result.goals)}', flush=True)
                for i, goal in enumerate(result.goals[:2]):
                    preview = display_goal(goal)
                    # Never truncate away the target after a long context.
                    if len(preview) > 1800:
                        target = goal_target(preview)
                        head = preview.partition('⊢')[0]
                        preview = head[:1200] + (' ... [context truncated]\n' if len(head) > 1200 else '') + '\n⊢ ' + target
                    print(f'[GOAL {i}] {preview}', flush=True)
                if len(result.goals) > 2:
                    print(f'[GOAL] {len(result.goals)-2} additional goals', flush=True)
            return result
        except TacticFailure as exc:
            if self.prover is not None:
                self.prover.feedback[(state.state_id, site.goal_id, str(tactic))] = str(exc)[:3000]
                if not self.replaying:
                    self.prover.local_failures[local_failure_key(display_goal(state.goals[site.goal_id]), str(tactic))] = str(exc)[:2000]
            print('[LEAN] FAILED:', str(exc)[:600], flush=True)
            raise


class ProjectRAG:
    """Use the saved LeanDojo index with a virtual file importing the same modules
    as the Pantograph session. No premise/vector is added or re-embedded.
    """
    def __init__(self, index, imports, target, k=15, threads=8):
        import torch
        from lean_dojo_v2.lean_dojo import Pos
        from lean_dojo_v2.lean_agent.common import File
        from lean_dojo_v2.lean_agent.retrieval.model import PremiseRetriever
        if not index.is_file():
            raise FileNotFoundError(index)
        if k < 1 or threads < 1:
            raise ValueError('RAG k and threads must be positive')
        self.torch = torch
        torch.set_num_threads(threads)
        self.pos = Pos(1, 1)
        self.target = target or '__local_smoke__'
        self.k = k
        self.cache = {}
        self.queries = 0
        start = time.monotonic()
        print(f'[RAG] loading trusted local index: {index}', flush=True)
        self.model = PremiseRetriever.load_hf(
            'kaiyuy/leandojo-lean4-retriever-byt5-small', 512, torch.device('cpu'))
        self.model.load_corpus(str(index))
        corpus = self.model.corpus
        if self.model.embeddings_staled or self.model.corpus_embeddings is None:
            raise RuntimeError('Expected a saved, already indexed corpus')
        if tuple(self.model.corpus_embeddings.shape) != (len(corpus), self.model.embedding_size):
            raise RuntimeError('Saved embedding shape does not match corpus/model')
        graph = corpus.transitive_dep_graph
        accessible_files = set()
        for module in imports:
            path = module.replace('.', '/') + '.lean'
            if path not in corpus:
                if module == 'PEqualNP' or module.startswith('PEqualNP.'):
                    raise RuntimeError(f'Project import missing from RAG index: {module}')
                print(f'[RAG] external import not indexed: {module}', flush=True)
                continue
            accessible_files.add(path)
            accessible_files.update(corpus.get_dependencies(path))
        self.path = '__local_rag_query__.lean'
        if self.path in graph:
            raise RuntimeError('Virtual query path already exists in corpus')
        graph.add_node(self.path, file=File(path=self.path, premises=[]))
        # This graph is already transitively closed. Add the full import closure.
        for path in sorted(accessible_files):
            graph.add_edge(self.path, path)
        accessible = corpus.get_accessible_premises(self.path, self.pos)
        if target and any(p.full_name == target for p in accessible):
            raise RuntimeError(f'Target theorem is already accessible in indexed imports: {target}')
        self.k = min(k, len(accessible))
        print(f'[RAG] ready in {time.monotonic()-start:.2f}s; indexed={len(corpus)}, accessible={len(accessible)}, top-k={self.k}', flush=True)

    def context(self, goal):
        if not self.k:
            return ''
        if goal in self.cache:
            return self.cache[goal]
        if '⊢' not in goal:
            raise ValueError('RAG query is missing Lean goal marker')
        start = time.monotonic()
        with self.torch.no_grad():
            premises, scores = self.model.retrieve([goal], [self.path], [self.target], [self.pos], self.k)
        self.queries += 1
        lines = []
        print(f'[RAG #{self.queries}] {time.monotonic()-start:.3f}s; candidates={len(premises[0])}', flush=True)
        for i, (premise, score) in enumerate(zip(premises[0], scores[0]), 1):
            if premise.full_name == self.target:
                raise RuntimeError('Target theorem leaked into RAG result')
            print(f'  {i:2d}. {score:.5f} {premise.full_name}', flush=True)
            code = premise.code
            if len(code) > 2000:
                code = code[:2000] + ' [declaration truncated]'
            lines.append(f'{i}. {premise.full_name}\n{code}')
        context = ('\n\nRetrieved project declarations (use the fully qualified names; '
                   'short names in declaration text may be relative to their source namespace). '
                   'They are hints, not guaranteed applicable; do not invent names.\n' + '\n\n'.join(lines))
        self.cache[goal] = context
        return context



MODEL_NAME = 'kaiyuy/leandojo-lean4-retriever-byt5-small'


def candidate_tactics(text, stepwise=False, limit=3, closed_only=False, diagnostics=None):
    """Complete blocks are alternatives; optional prefix is tried only after blocks."""
    counts = diagnostics if diagnostics is not None else Counter()
    text, unfinished = strip_thought(text)
    if unfinished:
        counts['unfinished_think'] += 1
    blocks = FENCE.findall(text)
    if not blocks:
        if closed_only:
            counts['truncated_no_closed_block'] += 1
            return []
        if not text:
            if not unfinished:
                counts['empty_content'] += 1
            return []
        if '```' in text:
            counts['unclosed_or_invalid_fence'] += 1
            return []
        blocks = [text]
    elif text.count('```') % 2:
        counts['trailing_incomplete_fence'] += 1
    results, prefixes = [], []
    for block in blocks:
        # Re-wrap a recognized fence so unfamiliar but valid Lean tactics are
        # accepted from explicit code, not from arbitrary natural language.
        source = '```lean\n' + block.rstrip() + '\n```' if FENCE.search(text) else block
        tactic, reason, prefix = extract_diagnosed(source, stepwise=stepwise)
        if reason != 'ok':
            counts[reason] += 1
        if tactic:
            if tactic in results:
                counts['duplicate_in_response'] += 1
            else:
                results.append(tactic)
        if prefix and prefix != tactic and prefix not in prefixes:
            prefixes.append(prefix)
    return (results + [p for p in prefixes if p not in results])[:limit]


# Namespace and lexical signals supplement, not replace, embedding scores.
PROJECT_REF = re.compile(r"\bPEqualNP(?:\.[A-Za-z_][\w']*){1,}")
DOMAIN_STOP = {'pequalnp','outside','defs','of','the','and','or','iff','eq','le','lt','to','in','at','is','on','left','right','nat','fin','bool','true','false','size','card'}


def domain_words(text):
    text = re.sub(r'([a-z0-9])([A-Z])', r'\1 \2', text)
    return set(re.findall(r'[A-Za-z][A-Za-z0-9]*', text.lower())) - DOMAIN_STOP


def project_refs(goal):
    return set(PROJECT_REF.findall(goal))


def domain_rank(name, refs, words):
    namespaces = {r.rsplit('.',1)[0] for r in refs}
    same = any(n != 'PEqualNP' and name.startswith(n+'.') for n in namespaces)
    overlap = len(domain_words(name) & words)
    return (int(same), min(overlap, 6))


def rerank_hits(hits, refs, words):
    def key(item):
        score, premise = item
        same, overlap = domain_rank(premise.full_name, refs, words)
        # Only a moderate additive boost, with original score as tie-break.
        return (score + 0.08*same + 0.015*overlap, score, premise.full_name)
    return sorted(hits, key=key, reverse=True)


def name_key(name):
    return unicodedata.normalize('NFKC', name).lower().rstrip("'0123456789")


def unknown_names(errors):
    return list(dict.fromkeys(re.findall(r"Unknown (?:identifier|constant) `([^`]+)`", errors)))


class LiveNames:
    """Read-only validation against the exact Pantograph environment."""
    def __init__(self, server, target=None):
        self.server = server
        self.target = target
        raw = set(server.env_catalog())
        # Pantograph 4.35/4.36 REPL toCompactSymbolName prepends one
        # ConstantInfo kind character (a/d/t/o/q/i/c/r), with no separator.
        # Detect the format using core symbols, not the first letter of each
        # arbitrary name (which would corrupt a plain-name catalog).
        if 'tNat.add_comm' in raw and 'iNat' in raw:
            self.catalog = {n[1:] for n in raw if len(n) > 1 and n[0] in 'adtoqicr'}
            self.theorem_names = {n[1:] for n in raw if n.startswith('t') and len(n)>1}
            fmt = 'compact-kind-prefix'
        elif 'Nat.add_comm' in raw and 'Nat' in raw:
            self.catalog = raw
            self.theorem_names = None
            fmt = 'plain'
        else:
            raise RuntimeError(f'Unrecognized Lean catalog format; sample={sorted(raw)[:5]!r}')
        if not {'Nat.add_comm', 'Nat'}.issubset(self.catalog):
            raise RuntimeError('Lean catalog failed core-symbol validation')
        if target and target in self.catalog:
            raise RuntimeError(f'Target theorem already exists in active Lean environment: {target}')
        self.cache = {}
        self.families = None
        print(f'[ENV] catalog constants={len(self.catalog)} format={fmt}', flush=True)
        if not self.inspect('Nat.add_comm'):
            raise RuntimeError('Lean catalog self-test failed: env.inspect Nat.add_comm')
        print('[ENV] self-test OK: Nat.add_comm', flush=True)

    def resolve(self, name):
        # AST names may have a spurious leading namespace. Try only suffixes
        # that actually exist; do not infer arbitrary renames.
        parts = name.split('.')
        candidates = [name] if name in self.catalog else [
            '.'.join(parts[i:]) for i in range(1, len(parts))
            if '.'.join(parts[i:]) in self.catalog]
        if len(candidates) != 1 or candidates[0] == self.target:
            return None
        return candidates[0]

    def inspect(self, name):
        if name == self.target or name not in self.catalog:
            return None
        if name not in self.cache:
            # env_inspect validates exact name; use the live type rather than
            # the possibly misqualified declaration text from the AST.
            try:
                data = self.server.env_inspect(name)
                pp = data.get('type', {}).get('pp')
                self.cache[name] = pp if isinstance(pp, str) and pp.strip() else None
            except ps.ServerError:
                self.cache[name] = None
        return self.cache[name]

    def similar(self, name, limit=4):
        if self.families is None:
            self.families = {}
            for n in sorted(self.catalog):
                if n.startswith('_private.') or n == self.target:
                    continue
                self.families.setdefault(name_key(n.split('.')[-1]), []).append(n)
        direct = self.resolve(name)
        hits = ([direct] if direct else []) + self.families.get(name_key(name.split('.')[-1]), [])
        # Exact qualification first, then short names, then other namespaces.
        hits = sorted(set(hits), key=lambda n: (n != direct, name_key(n) != name_key(name), n.count('.'), len(n), n))
        return [(n, pp) for n in hits[:limit] if (pp := self.inspect(n))]


def rw_prefixes(tactic):
    """Only flat rw [rules]; don't reinterpret nested tactics or locations."""
    tactic = unwrap_single_rw(tactic)
    m = re.fullmatch(r'rw\s*\[(.*)\]', tactic.strip(), re.S)
    if not m or '--' in tactic or '/-' in tactic:
        return []
    body = m.group(1)
    parts, stack, start, quote, escape = [], [], 0, False, False
    for i, ch in enumerate(body):
        if quote:
            if escape: escape = False
            elif ch == '\\': escape = True
            elif ch == '"': quote = False
        elif ch == '"': quote = True
        elif ch in '([{⟨': stack.append(ch)
        elif ch in ')]}⟩':
            if not stack or '([{⟨'.index(stack.pop()) != ')]}⟩'.index(ch): return []
        elif ch == ',' and not stack:
            parts.append(body[start:i].strip()); start = i+1
    if quote or stack: return []
    parts.append(body[start:].strip())
    if len(parts) < 2 or not all(parts): return []
    # Prefer a short prefix that can survive an early failing rule.
    counts = dict.fromkeys(n for n in (len(parts)-1, len(parts)//2, 2, 1) if 0 < n < len(parts))
    return ['rw [' + ', '.join(parts[:n]) + ']' for n in counts]


def repair_unknown_tactic(tactic, error, live, limit=2):
    """Retry simple rw/apply/exact with one explicitly rejected name replaced.

    Match only the spelling family, not arbitrary semantically related names.
    Lean still validates the entire candidate. Do not edit nested code,
    quoted identifiers, strings, comments or multi-tactic scripts.
    """
    tactic = unwrap_single_rw(tactic)
    if tactic.startswith('rw') and '\n' in tactic and not re.search(r'\bby\s*\n', tactic):
        tactic = ' '.join(tactic.splitlines())
    if live is None or not re.match(r'^(?:rw\s*\[|exact\s+|apply\s+|refine\s+)', tactic):
        return []
    if any(x in tactic for x in ('\n', '"', '«', '--', '/-', ';', '<;>')):
        return []
    out = []
    for name in unknown_names(error):
        if not re.fullmatch(r"[\w'.]+", name):
            continue
        pattern = re.compile(r"(?<![\w'.])" + re.escape(name) + r"(?![\w'.])")
        if not pattern.search(tactic):
            continue
        for real, _ in live.similar(name, limit=8):
            if real == name or name_key(real.split('.')[-1]) != name_key(name.split('.')[-1]):
                continue
            if not re.fullmatch(r"[\w'.]+", real):
                continue
            candidate = pattern.sub(lambda _: real, tactic)
            if candidate != tactic and candidate not in out:
                out.append(candidate)
            if len(out) >= limit:
                return out
    return out



def repair_type_mismatch(tactic, error):
    """Bounded syntactic recovery. Lean validates every new candidate."""
    if 'Application type mismatch' not in error and 'Type mismatch' not in error:
        return []
    if any(c in tactic for c in ('\n', '"', '«', '--', '/-', ';', '<;>')):
        return []
    out = []
    # In an explicitly supplied equivalence application, try the other direction.
    m = re.match(r'^(?:exact|refine)\s+\([^;]+\)\.(mp|mpr)(?=\s)', tactic)
    if m:
        other = 'mpr' if m.group(1) == 'mp' else 'mp'
        out.append(tactic[:m.start(1)] + other + tactic[m.end(1):])
    # A rejected last component of an anonymous constructor is an independent
    # obligation. Preserve the witness; replace only a named/explicit argument
    # that the actual diagnostic identifies. Do not guess a new witness.
    m = re.fullmatch(r'(?:exact|refine)\s+⟨(.+)⟩', tactic.strip())
    if not m:
        return out
    body = m.group(1)
    parts, stack, start = [], [], 0
    for i, ch in enumerate(body):
        if ch in '([{⟨':
            stack.append(ch)
        elif ch in ')]}⟩':
            if not stack or '([{⟨'.index(stack.pop()) != ')]}⟩'.index(ch):
                return out
        elif ch == ',' and not stack:
            parts.append(body[start:i].strip())
            start = i + 1
    if stack:
        return out
    parts.append(body[start:].strip())
    # TacticFailure may format a Message repr (literal backslash-n).
    diagnostic = error.replace('\\n', '\n')
    rejected = re.search(r'The argument\s*\n\s*(.*?)\s*\n\s*(?:has type|has type\b)', diagnostic, re.S)
    if rejected and len(parts) >= 2 and all(parts):
        bad = rejected.group(1).strip()
        for i in range(1, len(parts)):
            if parts[i] == bad and parts[i] != '?_':
                candidate = parts[:]
                candidate[i] = '?_'
                out.append('refine ⟨' + ', '.join(candidate) + '⟩')
    return list(dict.fromkeys(out))[:2]


def big_operator_family(goal):
    """Conservative hint from the selected conclusion, not local hypotheses."""
    target = goal_target(goal)
    if ('∑' in target) == ('∏' in target):
        return None
    return 'sum' if '∑' in target else 'prod'


def operator_counterparts(goal, names, live, limit=5):
    """Supplement vector hits with existing additive/multiplicative names.

    This is lexical retrieval, not an assertion that the statements are
    equivalent. Only exact, live theorem names are admitted; Lean still checks
    every tactic. Do not guess when both big operators occur in the goal.
    """
    family = big_operator_family(goal)
    if family is None or live is None or limit <= 0:
        return []
    opposite = 'prod' if family == 'sum' else 'sum'
    seen = set(names)
    out = []
    for name in names:
        prefix, sep, base = name.rpartition('.')
        if not sep or not base.startswith(opposite + '_'):
            continue
        tail = base[len(opposite):]
        variants = []
        # The neutral elements of multiplication and addition differ.
        if (opposite, tail) == ('prod', '_eq_one'):
            variants.append('_eq_zero')
        if (opposite, tail) == ('sum', '_eq_zero'):
            variants.append('_eq_one')
        variants.append(tail)
        for suffix in variants:
            candidate = prefix + '.' + family + suffix
            if (candidate in seen or candidate == live.target
                    or candidate.startswith('_private.') or candidate not in live.catalog
                    or (live.theorem_names is not None and candidate not in live.theorem_names)):
                continue
            pp = live.inspect(candidate)
            if pp:
                seen.add(candidate)
                out.append((candidate, pp, name))
                if len(out) >= limit:
                    return out
    return out


def rag_closing_tactic(goal, retrieved, live, limit=5):
    """Try a small set of retrieved theorems with standard Lean tactics.

    The batch must close the selected goal; an apply that creates obligations
    is accepted only if assumption/rfl/omega closes all of them. No answer
    theorem names or goal-specific rules are embedded.
    """
    if limit <= 0 or live is None or not retrieved:
        return None
    target = goal_target(goal)
    # Notation-aware lexical tie-breaking on the *conclusion* helps when the
    # embedding ranking is dominated by a long hypothesis.
    normalized = target.replace('∑', ' sum ').replace('∏', ' prod ').replace('^', ' pow ')
    normalized = normalized.replace('≤', ' le ').replace('<', ' lt ').replace('=', ' eq ')
    words = set(re.findall(r'[A-Za-z][A-Za-z0-9]*', normalized.lower()))
    stop = {'of','the','and','or','iff','eq','le','lt','to','in','at','is','on','left','right'}
    candidates = []
    refs = project_refs(goal)
    domain = domain_words(goal)
    family = big_operator_family(goal)
    for i, name in enumerate(re.findall(r'(?m)^\d+\.\s+([^\s:]+)\s+:', retrieved)):
        if not re.fullmatch(r"[\w'.]+", name) or name.startswith('_private.') or name == live.target:
            continue
        if live.theorem_names is not None and name not in live.theorem_names:
            continue
        if name not in live.catalog:
            continue
        pieces = set(re.findall(r'[A-Za-z][A-Za-z0-9]*', name.lower()))
        overlap = len((pieces - stop) & words)
        # Do not let a product-only lemma displace a sum lemma (or vice
        # versa). Keep unrelated lemmas eligible rather than hard-filtering.
        opposite = 'prod' if family == 'sum' else 'sum'
        mismatch = int(family is not None and opposite in pieces and family not in pieces)
        same, related = domain_rank(name, refs, domain)
        candidates.append((mismatch, -overlap, -same, -related if same else 0, i, name))
    names = [row[-1] for row in sorted(candidates)[:limit]]
    if not names:
        return None
    # Each branch rolls back if any of its new goals fails. Never return a
    # partial apply merely because it changed the goal.
    return 'first\n' + '\n'.join(
        '  | (apply ' + name + ' <;> (first | assumption | rfl | omega))'
        for name in names
    )


def has_forall_goal(goal):
    # Only introduce a visibly universal goal, not arbitrary implications.
    return bool(re.search(r'(?m)^\s*⊢\s*∀', goal))



def goal_target(goal):
    """The displayed conclusion, excluding potentially very long hypotheses."""
    _, sep, tail = goal.partition('⊢')
    return tail.strip() if sep else goal.strip()


def inaccessible_rename(goal):
    """Rename inaccessible locals through Lean's rename_i, never cite † names.

    Only recognize simple printed local declaration lines. Lean validates
    the generated tactic, including ordering; do not rewrite goal text.
    """
    before, sep, _ = goal.partition('⊢')
    if not sep:
        return None
    locals_ = []
    for line in before.splitlines():
        m = re.match(r"^\s*([^\s:]+)\s*:\s+", line)
        if m:
            locals_.append(m.group(1))
    hidden = [n for n in locals_ if '✝' in n]
    if not hidden:
        return None
    used = set(locals_)
    new = []
    for i, name in enumerate(hidden, 1):
        base = name.split('✝', 1)[0]
        if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", base) or base == '_':
            base = 'local'
        # Avoid keyword/reserved-name ambiguity, even if the base is simple.
        name = 'ld_' + base
        j = 1
        while name in used:
            j += 1
            name = 'ld_' + base + '_' + str(j)
        used.add(name)
        new.append(name)
    return 'rename_i ' + ' '.join(new)


def retrieval_views(goal):
    """Add a conclusion-only query if the full context risks truncation."""
    conclusion = goal_target(goal)
    views = [goal, '⊢ ' + conclusion] if len(goal.encode('utf-8')) > 380 and '⊢' in goal else [goal]
    refs = sorted(project_refs(goal))
    if refs and len(views) > 1:
        views.append('\n'.join(refs[:16]) + '\n⊢ ' + conclusion)
    return views


def unwrap_single_rw(tactic):
    """Unwrap our own multiline formatting for a single rw, not a block."""
    text = tactic.strip()
    if text.startswith('(\n') and text.endswith('\n)'):
        body = textwrap.dedent(text[2:-2]).strip()
        # Only allow a single list of rules; rw_prefixes checks balanced syntax.
        if re.fullmatch(r'rw\s*\[.*\]', body, re.S):
            return body
    return text


class ShardedRAG(ProjectRAG):
    """Reuse LeanDojo's encoder and nearest-premise routine across immutable shards.

    Mathlib shards are used only with an explicit umbrella import Mathlib. For
    other imports, the project corpus's existing dependency closure is used;
    never assume the whole Mathlib library is accessible from a narrow import.
    """
    def __init__(self, index, imports, target, k, threads, mathlib_dir, project):
        super().__init__(index, imports, target, k, threads)
        self.request_k = k
        self.project_slots = 12
        self.project_theorems = None
        self.project_corpus = self.model.corpus
        self.project_emb = self.model.corpus_embeddings
        self.shards = {}
        self.mathlib_dir = mathlib_dir
        self.project = project
        self.enabled_mathlib = 'Mathlib' in imports
        self.manifest_checked = False
        self.manifest_groups = []
        self.manifest_hashes = {}
        self.mathlib_modules = set()
        self.bad_shards = set()
        self.names = {}
        self.live = None
        self._register_names(self.project_corpus, self.path)
        self.refresh()

    def _register_names(self, corpus, path):
        for premise in corpus.get_accessible_premises(path, self.pos):
            if premise.full_name != self.target:
                self.names.setdefault(premise.full_name, premise)

    def refresh(self):
        if not self.enabled_mathlib or not self.mathlib_dir.is_dir():
            return
        mp = self.mathlib_dir / 'manifest.json'
        if not mp.is_file():
            return
        if not self.manifest_checked:
            manifest = json.loads(mp.read_text(encoding='utf-8'))
            pkg = self.project / '.lake/packages/mathlib'
            head = subprocess.check_output(['git','-C',str(pkg),'rev-parse','HEAD'], text=True).strip()
            toolchain = (self.project/'lean-toolchain').read_text().strip()
            if (manifest.get('model'), manifest.get('seq_len'), manifest.get('dtype'), manifest.get('mathlib_commit'), manifest.get('toolchain')) != (MODEL_NAME,512,'float32',head,toolchain):
                raise RuntimeError('Mathlib index manifest does not match current model/Mathlib/toolchain')
            self.manifest_groups = manifest.get('groups',[])
            self.manifest_hashes = manifest.get('source_hashes',{})
            umbrella = (pkg/'Mathlib.lean').read_text(encoding='utf-8')
            # Direct imports are sufficient for safety; omit any module not
            # explicitly listed by the umbrella file rather than guessing.
            self.mathlib_modules = {'Mathlib'} | set(re.findall(r'(?m)^\s*(?:(?:public|private)\s+)?import\s+(?:all\s+)?(Mathlib(?:\.[\w]+)+)\s*(?:--[^\n]*)?$',umbrella))
            print(f'[RAG] Mathlib umbrella direct imports={len(self.mathlib_modules)-1}',flush=True)
            self.manifest_checked = True
        from lean_dojo_v2.lean_agent.common import File
        added = 0
        for marker in sorted(self.mathlib_dir.glob('shard-*/done.json')):
            folder = marker.parent
            if folder in self.shards or folder in self.bad_shards:
                continue
            try:
                meta = json.loads(marker.read_text())
                with (folder/'indexed_corpus.pickle').open('rb') as fp:
                    indexed = pickle.load(fp)  # trusted locally built pickle only
                corpus, emb = indexed.corpus, indexed.embeddings
                if tuple(emb.shape) != (len(corpus), self.model.embedding_size) or len(corpus) != meta['premises']:
                    raise ValueError('embedding shape/count mismatch')
                rows = [json.loads(line) for line in (folder/'modules.jsonl').read_text().splitlines() if line.strip()]
                files = {r['path'] for r in rows}
                shard_no = int(folder.name.split('-')[-1])
                expected = {'.lake/packages/mathlib/'+rel for rel in self.manifest_groups[shard_no]}
                if files != expected:
                    raise ValueError('shard members do not match manifest')
                graph = corpus.transitive_dep_graph
                if len(files) != meta['files'] or files != set(graph.nodes):
                    raise ValueError('module metadata mismatch')
                for row in rows:
                    rel = row['module'].replace('.', '/') + '.lean'
                    if row['path'] != '.lake/packages/mathlib/' + rel or not (self.project/'.lake/packages/mathlib/.lake/build/lib/lean'/Path(rel).with_suffix('.olean')).is_file():
                        raise ValueError('not a built Mathlib module')
                    src = self.project / row['path']
                    if hashlib.sha256(src.read_bytes()).hexdigest() != self.manifest_hashes.get(rel):
                        raise ValueError('Mathlib source differs from index manifest')
                if any(p.full_name == self.target for p in corpus.all_premises):
                    raise RuntimeError('Target theorem found in Mathlib shard')
                graph.add_node(self.path, file=File(path=self.path, premises=[]))
                for row in rows:
                    if row['module'] in self.mathlib_modules:
                        graph.add_edge(self.path, row['path'])
                n = len(corpus.get_accessible_premises(self.path,self.pos))
                if not n:
                    self.shards[folder] = (corpus,emb,0)
                    continue
                self._register_names(corpus,self.path)
                self.shards[folder] = (corpus,emb,n)
                added += 1
            except Exception as exc:
                self.bad_shards.add(folder)
                print(f'[RAG] shard skipped {folder.name}: {exc}',flush=True)
        if added:
            self.cache.clear()
            print(f'[RAG] Mathlib complete shards={len(self.shards)} accessible={sum(x[2] for x in self.shards.values())}',flush=True)

    def corrections(self, errors):
        out = []
        if self.live is None:
            raise RuntimeError('Live environment validation has not been initialized')
        for name in unknown_names(errors):
            for match, pp in self.live.similar(name):
                line = f'{name} -> {match} : {pp[:700]}'
                if line not in out: out.append(line)
        return '\n'.join(out[:8])

    def context(self, goal):
        self.refresh()
        if goal in self.cache:
            return self.cache[goal]
        from lean_dojo_v2.lean_agent.common import Context
        contexts = [Context(self.path,self.target,self.pos,view) for view in retrieval_views(goal)]
        start = time.monotonic()
        with self.torch.no_grad():
            tokens = self.model.tokenizer([ctx.serialize() for ctx in contexts],padding='longest',max_length=self.model.max_seq_len,truncation=True,return_tensors='pt')
            vec = self.model._encode(tokens.input_ids.to(self.model.device),tokens.attention_mask.to(self.model.device))
            def nearest(corpus, emb, n):
                if not n: return []
                ps_, scores = corpus.get_nearest_premises(emb.to(device=vec.device,dtype=vec.dtype),contexts,vec,min(self.request_k,n))
                return [(float(score),p) for pp,ss in zip(ps_,scores) for p,score in zip(pp,ss) if p.full_name != self.target]
            project_hits = nearest(self.project_corpus,self.project_emb,self.k)
            math_hits = []
            for corpus,emb,n in self.shards.values():
                math_hits.extend(nearest(corpus,emb,n))
        if self.live is None:
            raise RuntimeError('Live environment validation has not been initialized')
        refs = project_refs(goal)
        words = domain_words(goal)
        project_slots = min(self.request_k, self.project_slots) if refs else 0
        chosen, seen, dropped = [], set(), []
        def add(name, score, source):
            real = self.live.resolve(name)
            if not real:
                dropped.append(f'{name}: not uniquely resolvable')
                return False
            if real in seen:
                return False
            pp = self.live.inspect(real)
            if not pp:
                dropped.append(f'{real}: env.inspect failed')
                return False
            if real != name:
                print(f'[RAG NAME] {name} -> {real}', flush=True)
            seen.add(real)
            chosen.append((score,real,pp,source))
            return True
        # Reserve project slots only for goals that actually mention PEqualNP.
        # Give direct live definitions a small quota, leaving room for lemmas.
        direct_limit = min(4, project_slots//3)
        for name in sorted(refs, key=lambda n: (-len(domain_words(n) & domain_words(goal_target(goal))), n)):
            if len(chosen) >= direct_limit:
                break
            add(name, None, 'direct')
        # A few related live theorems may not be indexed yet. They must share
        # a relevant namespace and lexical signal; never use an unavailable theorem.
        if self.project_theorems is None:
            self.project_theorems = sorted(n for n in (self.live.theorem_names or ())
                if n.startswith('PEqualNP.') and n != self.target)
        lexical = [(domain_rank(n,refs,words),n) for n in self.project_theorems] if refs else []
        lexical = sorted((r,n) for r,n in lexical if r[0] and r[1] >= 2)
        lexical_limit = min(project_slots, len(chosen)+min(4, project_slots//3))
        for _, name in reversed(lexical):
            if len(chosen) >= lexical_limit:
                break
            add(name, None, 'namespace')
        project_sorted = rerank_hits(project_hits, refs, words)
        if project_slots:
            for score, p in project_sorted:
                if len(chosen) >= project_slots: break
                if p.full_name.startswith('PEqualNP.'):
                    add(p.full_name, score, 'project')
        for score, p in rerank_hits(project_hits+math_hits, refs, words):
            if len(chosen) >= self.request_k: break
            add(p.full_name, score, 'project' if p.full_name.startswith('PEqualNP.') else 'mathlib')
        if dropped:
            print(f'[RAG DROP] total={len(dropped)}; examples: ' + '; '.join(dropped[:3]), flush=True)
        self.queries += 1
        project_count = sum(n.startswith('PEqualNP.') for _,n,_,_ in chosen)
        print(f'[RAG #{self.queries}] {time.monotonic()-start:.3f}s; candidates={len(chosen)}; project={project_count}; views={len(contexts)}; Mathlib shards={len(self.shards)}',flush=True)
        lines=[]
        for i,(score,name,pp,source) in enumerate(chosen,1):
            label = f'{score:.5f}' if score is not None else source
            print(f'  {i:2d}. {label} {name}',flush=True)
            lines.append(f'{i}. {name} : {pp[:1200]}')
        # Separate lexical additions from embedding scores. They are verified
        # against the active environment, even if not yet embedded in a shard.
        extra = operator_counterparts(goal, [name for _, name, _, _ in chosen], self.live)
        for name, pp, source in extra:
            print(f'[RAG LEXICAL] {source} -> {name}', flush=True)
            lines.append(f'{len(lines)+1}. {name} : {pp[:1200]}')
        result='\n\nRetrieved declarations (names and types checked in the active Lean environment; applicability is not guaranteed):\n'+'\n\n'.join(lines) if lines else ''
        self.cache[goal]=result
        return result



def load_lemma_bank(path):
    """Read explicit, locally trusted lemma data, not the target proof source."""
    data = json.loads(Path(path).expanduser().read_text(encoding='utf-8'))
    if not isinstance(data, list) or len(data) > 32:
        raise ValueError('Lemma bank must be a JSON list of at most 32 entries')
    entries = []
    names = set()
    for item in data:
        name, goal, steps = item['name'], item['goal'], item['tactics']
        if not isinstance(name, str) or not re.fullmatch(r'ld_mem_[A-Za-z0-9_]+', name) or name in names:
            raise ValueError(f'Invalid or duplicate lemma name: {name!r}')
        if not isinstance(goal, str) or not goal.strip() or not isinstance(steps, list) or not steps:
            raise ValueError(f'Invalid lemma entry: {name}')
        if any(not isinstance(step, str) or not step.strip() for step in steps):
            raise ValueError(f'Invalid lemma tactics: {name}')
        if any(re.search(r'\b(sorry|admit|native_decide|sorryAx)\b', x) for x in [goal, *steps]):
            raise ValueError(f'Forbidden proof placeholder: {name}')
        names.add(name)
        entries.append((name, goal, steps))
    return entries


def bank_tactic(name, goal, steps):
    body = '\n'.join(textwrap.indent(step, '  ') for step in steps)
    # A lambda binder is an ordinary hypothesis, not a local definition
    # containing the (potentially huge) proof term. The proof is still supplied
    # as the argument and checked by Lean.
    return f'refine (fun ({name} : ({goal})) => ?_) (by\n{body}\n)'


def verify_lemma_bank(server, entries, target_goal):
    """Check exact injection and actual use in isolation; no external declaration."""
    verified = []
    old = server.replaying
    server.replaying = True
    try:
        for name, goal, steps in entries:
            if ' '.join(goal.split()) == ' '.join(target_goal.split()):
                raise ValueError(f'Bank entry equals the target goal: {name}')
            # Prove the lemma itself through the injected hypothesis, so the
            # replay cannot simply discard an unused proof argument.
            g = server.goal_start(goal)
            g = server.goal_tactic(g, bank_tactic(name, goal, steps), site=Site(goal_id=0, auto_resume=True))
            if len(g.goals) != 1:
                raise RuntimeError(f'Bank entry left extra goals: {name}')
            local = [x for x in g.goals[0].variables if x.name == name]
            if len(local) != 1 or getattr(local[0], 'v', None):
                raise RuntimeError(f'Bank helper is not an opaque local hypothesis: {name}')
            g = server.goal_tactic(g, f'exact {name}', site=Site(goal_id=0, auto_resume=True))
            if g.goals or server.goal_root(g) is None:
                raise RuntimeError(f'Bank entry did not verify: {name}')
            verified.append((name, goal, steps))
            print(f'[BANK] verified opaque helper {name}', flush=True)
    finally:
        server.replaying = old
    return verified


def local_failure_key(goal, tactic):
    # Exact pretty-printed local state only; not a semantic identity claim.
    return (goal.strip(), tactic.strip())


def make_chat_payload(model, prompt, temperature, max_tokens, stream, reasoning_effort=None, reasoning_budget_tokens=None):
    payload = dict(model=model, messages=[dict(role='user', content=prompt)],
                   temperature=temperature, max_tokens=max_tokens, stream=stream)
    if reasoning_effort is not None:
        payload['reasoning_effort'] = reasoning_effort
    if reasoning_budget_tokens is not None:
        payload['reasoning_budget_tokens'] = reasoning_budget_tokens
    if stream:
        payload['stream_options'] = {'include_usage': True}
    return payload


class LocalProver(BaseProver):
    def __init__(self, base_url, model, root_goal, imports, auto_exact=True, stream=True, max_tokens=32768, rag=None, stepwise=True, max_calls=20, max_search_seconds=900, alternatives=3, llm_per_state=2, reasoning_effort=None, auto_intro=True, reasoning_budget_tokens=None, api_timeout=900):
        super().__init__()
        self.url = base_url.rstrip('/') + '/chat/completions'
        self.model = model
        self.root_goal = root_goal
        self.imports = imports
        self.import_text = "\n".join("import " + m for m in imports)
        self.is_pythagoras = "pythagoras" in model.lower()
        self.attempted = {}
        self.calls = 0
        self.feedback = {}
        self.auto_exact = auto_exact
        self.stream = stream
        self.max_tokens = max_tokens
        self.rag = rag
        self.stepwise = stepwise
        self.max_calls = max_calls
        self.max_search_seconds = max_search_seconds
        self.started = time.monotonic()
        self.paths = {}
        self.alternatives = alternatives
        self.llm_per_state = llm_per_state
        self.reasoning_effort = reasoning_effort
        self.reasoning_budget_tokens = reasoning_budget_tokens
        self.api_timeout = api_timeout
        self.pending = {}
        self.state_calls = {}
        self.recovered = set()
        self.recovery_counts = {}
        self.auto_intro = auto_intro
        self.live = None
        self.trace_path = None
        self.bank = []
        self.local_failures = {}
        self.allow_repeat_failures = False
        self.rag_auto_apply = 0
        self.rag_auto_tried = set()
        self.rejections = Counter()
        self.accepted_candidates = 0

    def check_budget(self, check_calls=True):
        elapsed = time.monotonic() - self.started
        if (check_calls and self.calls >= self.max_calls) or elapsed >= self.max_search_seconds:
            raise SystemExit(f'SEARCH BUDGET EXHAUSTED: {self.calls} LLM calls, {elapsed:.1f}s; no completed proof reported')

    @staticmethod
    def progress(done, start, call):
        while not done.wait(15):
            print(f'[LLM #{call}] generating... {time.monotonic()-start:.0f}s', flush=True)

    def next_tactic(self, state, goal_id):
        self.check_budget(check_calls=False)
        goal = display_goal(state.goals[goal_id])
        key = (state.state_id, goal_id)
        tried = self.attempted.setdefault(key, [])
        queue = self.pending.setdefault(key, [])
        path = self.paths.get(state.state_id, ())
        bank_candidates = [bank_tactic(*entry) for entry in self.bank]
        if len(state.goals) == 1 and all(str(t) in bank_candidates for t, _, _ in path):
            for tactic in bank_candidates:
                if tactic not in tried and all(str(t) != tactic for t, _, _ in path):
                    tried.append(tactic)
                    print('[BANK] introducing verified local helper', flush=True)
                    return tactic
        # Recover bounded candidates from the actual Lean failure, before
        # requesting more tokens. Upstream search still validates each one.
        if tried:
            last = tried[-1]
            recovery_key = (key, last)
            if recovery_key not in self.recovered:
                self.recovered.add(recovery_key)
                err = self.feedback.get((state.state_id, goal_id, last), '')
                proposals = []
                if 'Unknown identifier' in err or 'Unknown constant' in err:
                    proposals.extend((t, 'live name repair') for t in repair_unknown_tactic(last, err, self.live))
                if 'rewrite` failed' in err or 'Unknown identifier' in err or 'Unknown constant' in err:
                    proposals.extend((t, 'shorter rewrite prefix') for t in rw_prefixes(last))
                proposals.extend((t, 'type mismatch decomposition') for t in repair_type_mismatch(last, err))
                remaining = max(0, 4 - self.recovery_counts.get(key, 0))
                fresh = []
                for t, kind in proposals:
                    if t not in tried and t not in queue and t not in fresh and len(fresh) < remaining:
                        fresh.append(t)
                        print(f'[RECOVERY] {kind}: {t}', flush=True)
                if fresh:
                    self.recovery_counts[key] = self.recovery_counts.get(key, 0) + len(fresh)
                    queue[:0] = fresh
        while queue:
            tactic = queue.pop(0)
            if tactic not in tried:
                if not self.allow_repeat_failures and local_failure_key(goal, tactic) in self.local_failures:
                    print('[SKIP] previously failed in identical visible local goal', flush=True)
                    continue
                tried.append(tactic)
                print(f'[CANDIDATE] cached alternative; remaining={len(queue)}',flush=True)
                return tactic
        rename = inaccessible_rename(goal)
        if rename and rename not in tried:
            tried.append(rename)
            print('[Lean search] rename inaccessible locals', flush=True)
            return rename
        if self.auto_intro and has_forall_goal(goal) and not inaccessible_rename(goal) and 'intros' not in tried:
            tried.append('intros')
            print('[Lean search] automatic introductions', flush=True)
            return 'intros'
        if (self.auto_exact and 'exact?' not in tried
                and (self.allow_repeat_failures or local_failure_key(goal, 'exact?') not in self.local_failures)):
            tried.append('exact?')
            print('[Lean search] exact?', flush=True)
            return 'exact?'
        retrieved = None
        if self.rag_auto_apply and self.rag is not None and key not in self.rag_auto_tried:
            self.rag_auto_tried.add(key)
            retrieved = self.rag.context(goal)
            tactic = rag_closing_tactic(goal, retrieved, self.live, self.rag_auto_apply)
            if tactic and tactic not in tried and (
                    self.allow_repeat_failures or local_failure_key(goal, tactic) not in self.local_failures):
                tried.append(tactic)
                print('[RAG APPLY] bounded closing search before LLM', flush=True)
                return tactic
        if self.state_calls.get(key,0) >= self.llm_per_state:
            print(f'[BACKTRACK] state={state.state_id} goal={goal_id}; local LLM limit',flush=True)
            return None
        tried_text = json.dumps([{'tactic': t, 'error': self.feedback.get((state.state_id, goal_id, t), '')} for t in tried], ensure_ascii=False)
        if self.is_pythagoras and state.state_id == 0 and goal_id == 0:
            prompt = (
                'Complete the following Lean 4 code:\n\n'
                f'```lean4\n{self.import_text}\ntheorem local_smoke : {self.root_goal} := by\n  sorry\n```\n\n'
                'Explain the proof plan, then provide the completed Lean 4 code. '
                'Use only the listed imports; prefer short existing lemmas. Do not use sorry, admit or native_decide in the answer. '
                f'Previous rejected proof bodies (try a different approach): {tried_text}'
            )
        else:
            prompt = ('You are a Lean 4 theorem prover. Give an executable tactic or tactic sequence for the selected goal. '
                      'Return Lean tactic text in a fenced lean code block, without theorem, example, or outer by. '
                      'Prefer one short tactic or a short coherent tactic sequence. Never include exact?, apply?, simp?, or another suggestion-producing tactic in a multi-tactic block. For example, return intro h or rw [h] alone; the harness tries exact? on each new state. If using exact? or apply?, return it alone. Do not guess project-specific theorem names. Use the Lean errors below to avoid repeating failed approaches. Do not use sorry, admit, or native_decide. '
                      f'Available imports: {self.import_text}.\n\n'
                      f'Goal:\n{goal}\n\nPreviously tried tactics (avoid repeating): {tried_text}')
        if self.stepwise:
            prompt += ('\nINCREMENTAL MODE: Return exactly ONE top-level tactic for the current goal, '
                       'not a full proof. If there are forall binders, introduce them first; '
                       'if the goal is an iff or conjunction, constructor may be useful. '
                       'Do not combine independent tactics with semicolons. '
                       'A have with its nested by proof is one tactic; do not give the later steps. '
                       'The next call will receive the new goal and local hypotheses.')
        else:
            prompt += ('\nBLOCK MODE: A candidate may be 1–8 coherent tactics, with correct Lean indentation. '
                       'Prefer short blocks (at most 24 lines); preserve unsolved goals rather than guessing a complete proof. '
                       'Never place suggestion-producing tactics in a block. Do not output analysis or explanations.')
        prompt += ('\nSelected conclusion (do not confuse it with the other local assumptions):\n' + goal_target(goal))
        prompt += ('\nProof strategy: before splitting a complex equivalence or other compound statement, '
                   'consider whether a shared auxiliary proposition would simplify both branches. '
                   'You may create a named helper as `have helper : P := ?_` (replace P with a fully specified proposition); '
                   'Lean will create an independent proof obligation. Use `refine` with explicit holes to expose missing arguments '
                   'rather than guessing a complete term. Do not use sorry. '
                   'For a defined predicate, inspect/unfold the definition or eliminate the existential before projecting fields. '
                   'Never type inaccessible names containing ✝; use rename_i with fresh names first. '
                   'If a cast is the only mismatch, isolate a cast equality or inequality as a helper rather than applying norm_cast indiscriminately.')
        # Carry recent verified path steps across state IDs, not just failures
        # at the present state. Do not include hidden reasoning.
        history = [str(t)[:500] for t, _, _ in self.paths.get(state.state_id, ())[-8:]]
        if history:
            prompt += '\nRecent successful tactics on this path (do not repeat unless the goal has changed): ' + json.dumps(history, ensure_ascii=False)
        prompt += '\nIf norm_cast or simp already ran, check whether it actually changed the goal; choose a different approach if not.'
        prompt += ('\nPrefer transformations that simplify the goal; do not change numeric domains unnecessarily. '
                   'For mixed Nat and ordered-field inequalities, avoid global norm_cast before eliminating field division or rewriting natural subtraction with explicit cast equalities. '
                   'Use the error messages to switch strategy, not merely rename a failing lemma.')
        # Prior failures in the same visible local context survive changes to
        # sibling goals and backtracking. Show the error, not model reasoning.
        prior = [(t, err) for (g, t), err in self.local_failures.items()
                 if g == goal.strip() and t not in tried][-6:]
        if prior:
            prompt += '\nPreviously failed in this same visible local goal on other search states; do not repeat:\n' + json.dumps(prior, ensure_ascii=False)
        prompt += ('\nIf applying a local hypothesis requires a nontrivial premise, first create that premise '
                   'as a separately named have with an explicit proposition and := ?_. '
                   'Do not repeatedly attempt a full exact/exact_mod_cast with an ill-typed witness. '
                   'If a verified helper is available in local hypotheses, use its .mp or .mpr for an equivalence '
                   'instead of deriving the same arithmetic conversion again.')
        if self.rag is not None:
            prompt += retrieved if retrieved is not None else self.rag.context(goal)
        if self.live is not None:
            recent_errors = '\n'.join(list(self.feedback.values())[-16:])
            missing = list(dict.fromkeys(unknown_names(tried_text) + unknown_names(recent_errors)))[:8]
            hints = [f'{name} -> {real} : {pp[:700]}' for name in missing for real, pp in self.live.similar(name, limit=2)]
            if hints:
                prompt += '\nReal declaration names similar to failed identifiers:\n' + '\n'.join(hints[:8])
        if self.alternatives > 1 and not self.is_pythagoras:
            prompt += (f'\nReturn up to {self.alternatives} DIFFERENT alternative candidates for the SAME current goal, '
                       'each in its own closed lean fenced block. They are alternatives, not successive steps. '
                       'Put the most promising first. No prose or explanation. A single good candidate is acceptable.')
        # Retry only malformed/duplicate model responses, not proof search.
        for format_attempt in range(3):
            self.check_budget()
            if self.state_calls.get(key,0) >= self.llm_per_state:
                return None
            self.state_calls[key] = self.state_calls.get(key,0)+1
            payload = make_chat_payload(self.model, prompt, 0.7 if self.is_pythagoras else 0.3,
                                        self.max_tokens, self.stream, self.reasoning_effort,
                                        self.reasoning_budget_tokens)
            self.calls += 1
            start = time.monotonic()
            headers = {'Content-Type': 'application/json'}
            api_key = os.environ.get('LEANDOJO_API_KEY', 'local-key')
            if api_key:
                headers['Authorization'] = 'Bearer ' + api_key
            request = urllib.request.Request(self.url, data=json.dumps(payload).encode(), headers=headers)
            print(f'[LLM #{self.calls}] start', flush=True)
            done = threading.Event()
            worker = threading.Thread(target=self.progress, args=(done, start, self.calls), daemon=True)
            worker.start()
            stats = {}
            try:
                with urllib.request.urlopen(request, timeout=self.api_timeout) as response:
                    text, finish, usage = receive_chat(response, show=False, stats=stats)
            except urllib.error.HTTPError as exc:
                if exc.code in (401, 403):
                    raise SystemExit(f"[LLM AUTH ERROR] HTTP {exc.code}; verify --base-url and LEANDOJO_API_KEY (not printed)") from None
                raise
            finally:
                done.set()
                worker.join()
            diagnostics = Counter()
            candidates = candidate_tactics(text, self.stepwise, self.alternatives,
                                           closed_only=finish=='length', diagnostics=diagnostics)
            elapsed = time.monotonic()-start
            tokens = (usage or {}).get('completion_tokens')
            rate = f', {tokens/elapsed:.1f} tok/s' if isinstance(tokens, int) and elapsed > 0 else ''
            print(f'[LLM #{self.calls}] {elapsed:.2f}s, tokens={tokens}, finish={finish}{rate}; '
                  f'content_chars={len(text)} reasoning_chars={stats.get("reasoning_chars",0)}', flush=True)
            fresh = []
            for tactic in candidates:
                if tactic in tried or tactic in queue:
                    diagnostics['duplicate_state'] += 1
                elif not self.allow_repeat_failures and local_failure_key(goal, tactic) in self.local_failures:
                    diagnostics['previously_failed'] += 1
                else:
                    fresh.append(tactic)
            if finish not in ('stop','length'):
                diagnostics['unexpected_finish'] += 1
                fresh = []
            if not fresh and not diagnostics:
                diagnostics['no_candidate'] += 1
            self.rejections.update(diagnostics)
            if diagnostics:
                print('[LLM FORMAT] '+json.dumps(dict(diagnostics),sort_keys=True),flush=True)
            if fresh:
                self.accepted_candidates += len(fresh)
                tactic = fresh.pop(0)
                queue.extend(fresh)
                print(f'[CANDIDATES] {1+len(fresh)} valid-format alternatives',flush=True)
                tried.append(tactic)
                return tactic
            print('[LLM REJECT] '+json.dumps(dict(diagnostics),sort_keys=True),flush=True)
            prompt += ('\nPrevious response yielded no usable tactic; reason codes: '+', '.join(sorted(diagnostics))+
                       '. Return ONE short different tactic in a closed lean fence, no prose, no full theorem.')
        return None

    def generate_whole_proof(self, theorem):
        raise NotImplementedError('This smoke test exercises tactic search only.')



def bounded_search(prover, server, goal, max_steps, max_trials_per_goal):
    """Local DFS driver for the installed BaseProver API with fixed limits.

    Lean still executes every candidate through FeedbackServer. Use a stack of
    actual states; discarded branches cannot contribute to the returned proof.
    The outer caller independently replays server.solved_path as before.
    A step is one outer iteration (candidate attempt or backtrack), not each
    subtrial within the isolated RAG batch.
    """
    if min(max_steps, max_trials_per_goal) < 1:
        raise ValueError('search limits must be positive')
    prover.reset()
    start = time.monotonic()
    root = server.goal_start(goal)
    n_goals_root = len(root.goals)
    stack = [(root, Counter())]
    steps = 0
    def finish(success, reason):
        print(f'[SEARCH END] reason={reason} steps={steps}/{max_steps}', flush=True)
        result = SearchResult(n_goals_root=n_goals_root, duration=time.monotonic()-start,
                              success=success, steps=steps)
        tactics = [str(t) for t, _, _ in server.solved_path] if success and server.solved_path is not None else None
        return result, tactics
    while stack:
        state, trials = stack[-1]
        # Recognize a solution on the very last allowed attempt as success.
        if not state.goals:
            if server.solved_path is None or server.goal_root(state) is None:
                raise RuntimeError('Search reached empty goals without recorded complete root')
            return finish(True, 'solved')
        if steps >= max_steps:
            return finish(False, 'step_limit')
        prover.check_budget(check_calls=False)
        steps += 1
        if steps == 1 or steps % 25 == 0:
            print(f'[SEARCH STEP] {steps}/{max_steps}; depth={len(stack)-1}', flush=True)
        priorities = prover.guidance(state) if len(state.goals) > 1 else [0.0]
        if len(priorities) != len(state.goals):
            raise RuntimeError('Invalid goal priorities')
        goal_id = max(range(len(state.goals)), key=lambda i: priorities[i])
        if trials[goal_id] >= max_trials_per_goal:
            stack.pop()
            continue
        tactic = prover.next_tactic(state, goal_id)
        if not tactic:
            stack.pop()
            continue
        trials[goal_id] += 1
        try:
            child = server.goal_tactic(state, tactic, site=Site(goal_id=goal_id, auto_resume=True))
        except TacticFailure:
            continue
        stack.append((child, Counter()))
    return finish(False, 'stack_exhausted')


def search_driver_self_test():
    from types import SimpleNamespace
    class MockServer:
        solved_path = None
        def goal_start(self, goal):
            self.solved_path = None
            return SimpleNamespace(goals=[1], state_id=0)
        def goal_root(self, state):
            return 'checked root' if not state.goals else None
        def goal_tactic(self, state, tactic, *, site):
            if tactic == 'bad':
                raise TacticFailure('mock rejection')
            if tactic == 'dead':
                return SimpleNamespace(goals=[1], state_id=-1)
            n = state.state_id + 1
            if n == 105:
                self.solved_path = [('good', (), {})] * 105
            return SimpleNamespace(goals=[] if n == 105 else [1], state_id=n)
    class MockProver:
        def reset(self): self.attempts = Counter()
        def check_budget(self, check_calls=False): pass
        def next_tactic(self, state, goal_id):
            self.attempts[state.state_id] += 1
            if state.state_id == -1: return None
            if state.state_id == 0 and self.attempts[0] <= 2:
                return ['bad','dead'][self.attempts[0]-1]
            return 'good'
    m = MockServer()
    result, tactics = bounded_search(MockProver(), m, 'mock', 100, 6)
    assert not result.success and result.steps == 100 and tactics is None
    result, tactics = bounded_search(MockProver(), m, 'mock', 108, 6)
    assert result.success and result.steps == 108 and len(tactics) == 105
    result, tactics = bounded_search(MockProver(), m, 'mock', 1000, 1)
    assert not result.success and result.steps == 2 and tactics is None
    print('SEARCH DRIVER TEST OK (100-step limit, >100 success, backtracking, trial cap)', flush=True)


def format_self_test():
    for budget in (None, 0, 16384):
        for stream in (True, False):
            payload = make_chat_payload('test', 'test', 0.3, 32768, stream, None, budget)
            assert payload['max_tokens'] == 32768
            assert ('stream_options' in payload) == stream
            assert ('reasoning_budget_tokens' in payload) == (budget is not None)
            if budget is not None:
                assert payload['reasoning_budget_tokens'] == budget
    assert make_chat_payload('test', 'test', 0.3, 100, False, 'high')['reasoning_effort'] == 'high'
    print('[FORMAT TEST] API payload budget/stream options OK', flush=True)
    from types import SimpleNamespace
    def run(text, expected, **kwargs):
        counts = Counter()
        got = candidate_tactics(text, diagnostics=counts, **kwargs)
        assert got == expected, (got, expected, counts)
        return counts
    block = 'intro n\nrfl'
    run('```lean\n'+block+'\n```', [wrap_tactic(block),'intro n'])
    run('```lean\n'+block+'\n```', ['intro n'], stepwise=True)
    run('```lean\nintro n\nexact?\n```', ['intro n'])
    assert run('```lean\nfirst | exact? | rfl\n```', [])['compound_suggestion'] == 1
    assert run('<think>private reasoning', [])['unfinished_think'] == 1
    assert run('', [])['empty_content'] == 1
    assert run('```lean\nrfl', [], closed_only=True)['truncated_no_closed_block'] == 1
    run('```lean\nrfl\n```\n```lean\nintro', ['rfl'], closed_only=True)
    assert run('```lean\nsorry\n```', [])['forbidden_token'] == 1
    assert run('I think this is true.', [])['not_tactic_text'] == 1
    assert run('```lean\nrfl\n```\n```lean\nrfl\n```', ['rfl'])['duplicate_in_response'] == 1
    run('```lean\nexact?\n```', ['exact?'])
    run('```lean\nconstructor\n  · trivial\n  · trivial\n```', [wrap_tactic('constructor\n  · trivial\n  · trivial'), 'constructor'])
    goal = 'h : PEqualNP.TopForm.IsLeastAO G C\n⊢ PEqualNP.TopForm.TopForm G C'
    refs = project_refs(goal)
    assert 'PEqualNP.TopForm.IsLeastAO' in refs
    ranked = rerank_hits([(0.50,SimpleNamespace(full_name='Quaternion.foo')),(0.46,SimpleNamespace(full_name='PEqualNP.TopForm.isLeastAO_foo'))], refs, domain_words(goal))
    assert ranked[0][1].full_name.startswith('PEqualNP.TopForm.')
    print('FORMAT AND RANKING TEST OK',flush=True)
    search_driver_self_test()


def engine_self_test(server):
    """Exercise real Lean transitions, not the LLM or any answer to L054."""
    g = server.goal_start('∀ n : Nat, n = n ∧ n = n')
    g = server.goal_tactic(g, 'intros', site=Site(goal_id=0, auto_resume=True))
    rename = inaccessible_rename(str(g.goals[0]))
    if rename:
        g = server.goal_tactic(g, rename, site=Site(goal_id=0, auto_resume=True))
        if inaccessible_rename(str(g.goals[0])):
            raise RuntimeError('rename_i left inaccessible local names')
    g = server.goal_tactic(g, 'constructor', site=Site(goal_id=0, auto_resume=True))
    if len(g.goals) != 2:
        raise RuntimeError('constructor did not expose two goals')
    g = server.goal_tactic(g, 'rfl', site=Site(goal_id=1, auto_resume=True))
    if len(g.goals) != 1:
        raise RuntimeError('Sibling goal was not preserved')
    g = server.goal_tactic(g, 'rfl', site=Site(goal_id=0, auto_resume=True))
    if g.goals or server.goal_root(g) is None:
        raise RuntimeError('Multi-goal proof did not close')
    steps = server.solved_path
    if not steps:
        raise RuntimeError('No recorded proof transitions')
    server.replaying = True
    try:
        g = server.goal_start('∀ n : Nat, n = n ∧ n = n')
        for tactic, args, kwargs in steps:
            g = server.goal_tactic(g, tactic, *args, **kwargs)
        if g.goals or server.goal_root(g) is None:
            raise RuntimeError('Multi-goal replay failed')
    finally:
        server.replaying = False
    print('[ENGINE TEST] multi-goal + replay OK', flush=True)
    g = server.goal_start('∀ n : Nat, n = n')
    block = candidate_tactics('```lean\nintro n\nrfl\n```')[0]
    g = server.goal_tactic(g, block, site=Site(goal_id=0, auto_resume=True))
    if g.goals or server.goal_root(g) is None:
        raise RuntimeError('v23 multi-tactic block did not close goal')
    steps = server.solved_path
    server.replaying = True
    try:
        g = server.goal_start('∀ n : Nat, n = n')
        for tactic, args, kwargs in steps:
            g = server.goal_tactic(g, tactic, *args, **kwargs)
        if g.goals or server.goal_root(g) is None:
            raise RuntimeError('v23 block replay failed')
    finally:
        server.replaying = False
    print('[ENGINE TEST] v23 tactic block + replay OK', flush=True)

    g = server.goal_start('True')
    g = server.goal_tactic(g, 'have h : True := ?_', site=Site(goal_id=0, auto_resume=True))
    if len(g.goals) != 2:
        raise RuntimeError('Helper did not expose two proof obligations')
    for _ in range(2):
        g = server.goal_tactic(g, 'exact True.intro', site=Site(goal_id=0, auto_resume=True))
    if g.goals or server.goal_root(g) is None:
        raise RuntimeError('Helper proof did not close')
    print('[ENGINE TEST] auxiliary goal OK', flush=True)
    # Verify opaque injection in a goal independent of the helper proof.
    g = server.goal_start('∀ n : Nat, n = n')
    g = server.goal_tactic(g, bank_tactic('ld_mem_test', '∀ n : Nat, n = n', ['intro n', 'rfl']),
                           site=Site(goal_id=0, auto_resume=True))
    local = [x for x in g.goals[0].variables if x.name == 'ld_mem_test']
    if len(local) != 1 or getattr(local[0], 'v', None):
        raise RuntimeError('Injected helper retains its proof value')
    # A failed tactic must not consume the saved parent.
    try:
        server.goal_tactic(g, 'exact False.intro', site=Site(goal_id=0, auto_resume=True))
    except TacticFailure:
        pass
    else:
        raise RuntimeError('Expected invalid tactic to fail')
    g = server.goal_tactic(g, 'exact ld_mem_test', site=Site(goal_id=0, auto_resume=True))
    if g.goals or server.goal_root(g) is None:
        raise RuntimeError('Opaque helper / parent reuse failed')
    print('[ENGINE TEST] opaque helper + failed-parent reuse OK', flush=True)
    live = LiveNames(server)
    g = server.goal_start('∀ (a b : Nat), a ≤ b → Nat.succ a ≤ Nat.succ b')
    g = server.goal_tactic(g, 'intro a b h', site=Site(goal_id=0, auto_resume=True))
    test_names = ['Nat.add_comm', 'Nat.succ_le_succ']
    lines = []
    for i, name in enumerate(test_names, 1):
        pp = live.inspect(name)
        if not pp or (live.theorem_names is not None and name not in live.theorem_names):
            raise RuntimeError(f'RAG self-test theorem unavailable: {name}')
        lines.append(f'{i}. {name} : {pp}')
    # Match the real ShardedRAG.context output, with actual newlines.
    fake_retrieved = '\n\n'.join(lines)
    batch = rag_closing_tactic(str(g.goals[0]), fake_retrieved, live, 2)
    if not batch or batch.count('  | (apply ') != 2 or any(
            f'apply {name} <;>' not in batch for name in test_names):
        raise RuntimeError(f'RAG self-test expected both candidate branches: {batch!r}')
    print('[ENGINE TEST] RAG candidate extraction OK (2 branches)', flush=True)
    # Also exercise rejection of a single irrelevant candidate independently.
    bad = rag_closing_tactic(str(g.goals[0]), lines[0], live, 1)
    try:
        server.goal_tactic(g, bad, site=Site(goal_id=0, auto_resume=True))
    except TacticFailure:
        pass
    else:
        raise RuntimeError('RAG self-test expected irrelevant candidate to fail')
    # Force the irrelevant branch first in this test only, so a pass also
    # verifies Lean's in-batch rollback rather than merely the ranking.
    branches = batch.splitlines()[1:]
    bad_first = 'first\n' + '\n'.join(sorted(branches, key=lambda b: 'apply Nat.add_comm <;>' not in b))
    g = server.goal_tactic(g, bad_first, site=Site(goal_id=0, auto_resume=True))
    if g.goals or server.goal_root(g) is None:
        raise RuntimeError('RAG closing batch did not close goal')
    print(f'[ENGINE TEST] RAG closing tactic OK (mode={server.rag_mode})', flush=True)
    counterparts = operator_counterparts('⊢ ∑ i, f i = 0',
                                        ['Finset.prod_eq_single', 'Finset.prod_eq_one'], live)
    actual = {name for name, _, _ in counterparts}
    if not {'Finset.sum_eq_single', 'Finset.sum_eq_zero'}.issubset(actual):
        raise RuntimeError(f'RAG lexical expansion failed: {actual!r}')
    print('[ENGINE TEST] RAG lexical expansion OK', flush=True)
    # Test the new driver through the actual Lean server, including failure,
    # a split goal, sibling preservation and replay of the final branch.
    class TestProver:
        def reset(self): self.counts = Counter()
        def check_budget(self, check_calls=False): pass
        def guidance(self, state): return [0.0] * len(state.goals)
        def next_tactic(self, state, goal_id):
            self.counts[state.state_id] += 1
            if sum(self.counts.values()) == 1: return 'exact False.intro'
            if sum(self.counts.values()) == 2: return 'constructor'
            return 'exact True.intro'
    result, tactics = bounded_search(TestProver(), server, 'True ∧ True', 4, 6)
    if not result.success or result.steps != 4 or len(tactics) != 3:
        raise RuntimeError('Local search driver did not solve at final permitted step')
    steps = server.solved_path
    server.replaying = True
    try:
        g = server.goal_start('True ∧ True')
        for tactic, args, kwargs in steps:
            g = server.goal_tactic(g, tactic, *args, **kwargs)
        if g.goals or server.goal_root(g) is None:
            raise RuntimeError('Local search driver replay failed')
    finally:
        server.replaying = False
    print('[ENGINE TEST] configurable local search + replay OK', flush=True)
    print('ENGINE TEST OK', flush=True)


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--base-url', default=os.environ.get('LEANDOJO_BASE_URL', 'http://172.31.64.1:8081/v1'))
    p.add_argument('--model', default='qwen3.8-flash-next-iq3_s')
    p.add_argument('--goal', default='∀ (n m : Nat), n + m = m + n')
    p.add_argument('--project', type=Path, default=Path.home() / 'dev/pequalnp-proofs/lean')
    p.add_argument('--imports', nargs='+', default=['Mathlib', 'PEqualNP.Defs'])
    p.add_argument('--no-auto-exact', action='store_true')
    p.add_argument('--no-auto-intro', action='store_true')
    p.add_argument('--no-stream', action='store_true')
    mode = p.add_mutually_exclusive_group()
    mode.add_argument('--whole-block', action='store_true', help='Default v23 bounded multi-tactic candidates (legacy flag)')
    mode.add_argument('--stepwise', action='store_true', help='Use legacy single-tactic mode')
    p.add_argument('--max-tokens', type=int, default=32768, help='Total completion token cap (reasoning plus answer on Strata)')
    p.add_argument('--reasoning-budget-tokens', type=int, default=None, help='Strata request thinking cap; 0 disables separate cap; omit to inherit server default')
    p.add_argument('--api-timeout', type=float, default=900, help='HTTP socket timeout in seconds; not a total streaming deadline')
    p.add_argument('--max-calls', type=int, default=20)
    p.add_argument('--max-search-seconds', type=float, default=900, help='Soft limit checked before the next search action or API request')
    p.add_argument('--full-root', action='store_true', help='Print complete proof term')
    p.add_argument('--rag-index', type=Path, default=Path.home() / 'dev/LeanDojo-v2/proof-logs/rag-project/indexed_corpus.pickle', help='Trusted local index generated by rag_build_project.py')
    p.add_argument('--no-rag', action='store_true')
    p.add_argument('--rag-target', help='Full name of theorem being re-proved; reject it if present in accessible indexed imports')
    p.add_argument('--rag-k', type=int, default=30)
    p.add_argument('--rag-project-slots', type=int, default=12, help='Minimum target quota for relevant project candidates when available; 0 disables')
    p.add_argument('--rag-auto-apply', type=int, default=0, help='Try this many retrieved theorems in one closing tactic batch before LLM; 0 disables')
    p.add_argument('--rag-mode', choices=['isolated', 'batch'], default='isolated', help='v21 independent candidate calls or legacy v20 first-batch')
    p.add_argument('--rag-budgets', type=int, nargs='+', default=[10000, 50000, 200000], help='Scoped heartbeat limits for RAG attempts')
    p.add_argument('--rag-retry-top', type=int, default=2, help='Retry at most this many timed-out candidates per later stage')
    p.add_argument('--rag-threads', type=int, default=4)
    p.add_argument('--mathlib-index', type=Path, default=Path.home()/'dev/LeanDojo-v2/proof-logs/rag-mathlib')
    p.add_argument('--no-mathlib-rag', action='store_true')
    p.add_argument('--alternatives', type=int, default=3)
    p.add_argument('--llm-per-state', type=int, default=2)
    p.add_argument('--max-trials-per-goal', type=int, default=6, help='Maximum candidate attempts per state and selected goal (default matches old upstream effective limit)' )
    p.add_argument('--max-steps', type=int, default=1000, help='Local outer search iteration limit')
    p.add_argument('--reasoning-effort', choices=['none','low','medium','high'], help='Optional API extension; only use if your server supports it')
    p.add_argument('--lemma-bank', type=Path, help='Optional explicit JSON bank of previously proven local helpers')
    p.add_argument('--bank-test-only', action='store_true', help='Validate lemma bank in real Lean without RAG or LLM')
    p.add_argument('--deprecation-warnings', action='store_true', help='Restore Lean deprecation warnings for A/B reproduction of Pantograph UTF-8 panic')
    p.add_argument('--allow-repeat-failures', action='store_true', help='Disable heuristic filtering of identical visible-state failures')
    p.add_argument('--format-test-only', action='store_true', help='Offline parser and ranking tests; no Lean or API calls')
    p.add_argument('--engine-test-only', action='store_true', help='Exercise actual Lean goal splitting, local renaming, auxiliary goals and replay without LLM or RAG')
    p.add_argument('--env-test-only', action='store_true', help='Check catalog and live symbol types without loading RAG or calling LLM')
    args = p.parse_args()
    if args.format_test_only:
        format_self_test()
        return
    if args.reasoning_budget_tokens is not None and args.reasoning_budget_tokens < 0:
        p.error('--reasoning-budget-tokens must be >= 0')
    if not math.isfinite(args.api_timeout) or args.api_timeout <= 0:
        p.error('--api-timeout must be finite and positive')
    if args.rag_project_slots < 0 or args.rag_k < 1:
        p.error('invalid RAG quota or k')
    if min(args.max_calls,args.alternatives,args.llm_per_state,args.max_tokens,args.max_steps,args.max_trials_per_goal) < 1 or args.max_search_seconds <= 0:
        p.error('search limits must be positive')
    if not 0 <= args.rag_auto_apply <= 8:
        p.error('--rag-auto-apply must be between 0 and 8')
    if not 1 <= len(args.rag_budgets) <= 4 or any(not 1 <= b <= 1000000 for b in args.rag_budgets) or args.rag_budgets != sorted(set(args.rag_budgets)):
        p.error('rag budgets must be 1-4 strictly increasing positive integers <= 1000000')
    if not 0 <= args.rag_retry_top <= 8:
        p.error('rag retry top must be between 0 and 8')
    FeedbackServer.rag_mode = args.rag_mode
    FeedbackServer.rag_budgets = tuple(args.rag_budgets)
    FeedbackServer.rag_retry_top = args.rag_retry_top
    print(f'[RAG CONFIG] mode={args.rag_mode} budgets={args.rag_budgets} retry_top={args.rag_retry_top}', flush=True)
    project = args.project.expanduser().resolve()
    repl = Path.home() / 'dev/Pantograph-4.36/.lake/build/bin/repl'
    assert repl.is_file(), repl
    ps._get_proc_path = lambda: repl
    print('PROJECT:', project, 'IMPORTS:', args.imports, flush=True)
    core_options = [] if args.deprecation_warnings else ['linter.deprecated=false']
    print('[LEAN CORE OPTIONS]', core_options or '(default)', flush=True)
    entries = load_lemma_bank(args.lemma_bank) if args.lemma_bank else []
    if args.bank_test_only:
        if not entries:
            p.error('--bank-test-only requires a nonempty --lemma-bank')
        with FeedbackServer(imports=args.imports, project_path=str(project), lean_path=os.environ['LEAN_PATH'], core_options=core_options) as server:
            LiveNames(server, args.rag_target)
            verify_lemma_bank(server, entries, args.goal)
        print('BANK TEST OK', flush=True)
        return
    if args.engine_test_only:
        with FeedbackServer(imports=args.imports, project_path=str(project), lean_path=os.environ['LEAN_PATH'], core_options=core_options) as server:
            engine_self_test(server)
        return
    if args.env_test_only:
        with FeedbackServer(imports=args.imports, project_path=str(project), lean_path=os.environ['LEAN_PATH'], core_options=core_options) as server:
            live = LiveNames(server, args.rag_target)
            for name in ['div_nonneg', 'div_le_iff₀', 'Nat.cast_sub', 'Nat.Int.cast_subNatNat', 'PEqualNP.Gct.HasBorderDetExpression']:
                resolved = live.resolve(name)
                pp = live.inspect(resolved) if resolved else None
                print(f'[ENV TEST] {name} -> {resolved}: {pp}', flush=True)
                if not pp:
                    raise RuntimeError(f'Environment test failed: {name}')
            print('ENV TEST OK', flush=True)
        return
    if args.no_rag:
        rag = None
    else:
        rag = ShardedRAG(args.rag_index.expanduser(),args.imports,args.rag_target,args.rag_k,args.rag_threads,args.mathlib_index.expanduser(),project) if not args.no_mathlib_rag else ShardedRAG(args.rag_index.expanduser(),[m for m in args.imports if m != 'Mathlib'],args.rag_target,args.rag_k,args.rag_threads,args.mathlib_index.expanduser(),project)
    with FeedbackServer(imports=args.imports, project_path=str(project), lean_path=os.environ['LEAN_PATH'], core_options=core_options) as server:
        live = LiveNames(server, args.rag_target)
        if rag is not None:
            rag.live = live
            rag.project_slots = args.rag_project_slots
        prover = LocalProver(args.base_url, args.model, args.goal, args.imports, not args.no_auto_exact, not args.no_stream, args.max_tokens, rag=rag, stepwise=args.stepwise, max_calls=args.max_calls, max_search_seconds=args.max_search_seconds, alternatives=args.alternatives, llm_per_state=args.llm_per_state, reasoning_effort=args.reasoning_effort, auto_intro=not args.no_auto_intro, reasoning_budget_tokens=args.reasoning_budget_tokens, api_timeout=args.api_timeout)
        print('[LLM CONFIG] '+json.dumps({'max_tokens': args.max_tokens, 'reasoning_budget_tokens': args.reasoning_budget_tokens if args.reasoning_budget_tokens is not None else 'server-default', 'reasoning_effort': args.reasoning_effort or 'server-default', 'api_timeout': args.api_timeout, 'stream': not args.no_stream}), flush=True)
        prover.live = live
        prover.bank = verify_lemma_bank(server, entries, args.goal)
        prover.allow_repeat_failures = args.allow_repeat_failures
        prover.rag_auto_apply = args.rag_auto_apply
        trace_dir = Path.home() / 'dev/LeanDojo-v2/proof-logs'
        trace_dir.mkdir(parents=True, exist_ok=True)
        prover.trace_path = trace_dir / (datetime.now().strftime('%Y%m%d-%H%M%S-%f') + '-transitions.jsonl')
        with prover.trace_path.open('x', encoding='utf-8') as trace:
            trace.write(json.dumps({'root_goal': args.goal, 'imports': args.imports, 'target': args.rag_target}, ensure_ascii=False)+'\n')
        print('[TRACE FILE]', prover.trace_path, flush=True)
        server.prover = prover
        # BaseProver.search in the installed upstream has hard-coded limits.
        # Do not modify the installed library; use our own bounded driver.
        print(f'[SEARCH CONFIG] driver=local-dfs max_steps={args.max_steps} max_trials_per_goal={args.max_trials_per_goal} max_calls={args.max_calls} seconds={args.max_search_seconds} mode={"stepwise" if args.stepwise else "blocks"} project_slots={args.rag_project_slots}', flush=True)
        try:
            result, tactics = bounded_search(prover, server, args.goal, args.max_steps, args.max_trials_per_goal)
        finally:
            print('[LLM SUMMARY]', json.dumps({'calls':prover.calls,'valid_candidates':prover.accepted_candidates,'diagnostics':dict(prover.rejections)},sort_keys=True),flush=True)
        print('SEARCH RESULT:', result, flush=True)
        print('UPSTREAM TACTICS:', tactics, flush=True)
        print('LLM CALLS:', prover.calls, flush=True)
        print('RAG QUERIES:', rag.queries if rag is not None else 0, flush=True)
        if not result.success:
            raise SystemExit('SEARCH NOT SOLVED')
        # The upstream result may omit goal indices. Replay the actual successful
        # transition chain instead, using the original Site arguments.
        path_steps = server.solved_path
        if path_steps is None:
            raise SystemExit('Search reported success without a recorded solved state')
        print('RECORDED TACTICS:', [str(t) for t, _, _ in path_steps], flush=True)
        print(f'[VERIFY] replaying {len(path_steps)} recorded transitions...', flush=True)
        server.replaying = True
        g = server.goal_start(args.goal)
        for tactic, site_args, site_kwargs in path_steps:
            g = server.goal_tactic(g, tactic, *site_args, **site_kwargs)
        assert not g.goals, 'Replay left goals'
        root = server.goal_root(g)
        assert root is not None, 'No completed root'
        root_text = str(root)
        logdir = Path.home() / 'dev/LeanDojo-v2/proof-logs'
        logdir.mkdir(parents=True, exist_ok=True)
        path = logdir / (datetime.now().strftime('%Y%m%d-%H%M%S-%f') + '-root.txt')
        path.write_text(root_text + '\n', encoding='utf-8')
        solved_file = path.with_name(path.name.replace('-root.txt', '-solved.json'))
        solved_file.write_text(json.dumps({'root_goal': args.goal, 'imports': args.imports,
            'target': args.rag_target, 'steps': [{'tactic': str(t), 'goal_id': kw['site'].goal_id}
            for t, _, kw in path_steps]}, ensure_ascii=False, indent=2)+'\n', encoding='utf-8')
        print('[SOLVED PATH]', solved_file, flush=True)

        print('ROOT:', root_text if args.full_root else root_text[:2000], flush=True)
        if not args.full_root and len(root_text) > 2000:
            print('[ROOT] truncated for console; complete term saved', flush=True)
        print('[ROOT FILE]', path, flush=True)
        print('SEARCH AND REPLAY OK', flush=True)


if __name__ == '__main__':
    main()
