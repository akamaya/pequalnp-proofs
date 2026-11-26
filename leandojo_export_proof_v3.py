#!/usr/bin/env python3
"""Recover a completed LeanDojo proof without another LLM call or repository edit."""
import argparse
import json
from pathlib import Path
import re
import subprocess
import tempfile
import textwrap

ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
NAME = re.compile(r"[\w'.]+\Z")


def load_path(path):
    if path.suffix == '.json':
        obj = json.loads(path.read_text(encoding='utf-8'))
        return obj, obj['steps']
    lines = [json.loads(line) for line in path.read_text(encoding='utf-8').splitlines() if line.strip()]
    meta, records = lines[0], lines[1:]
    states = {}
    finals = []
    for r in records:
        if r['state'] in states:
            raise ValueError('Duplicate state id in trace')
        states[r['state']] = r
        if not r['goals']:
            finals.append(r['state'])
    if not finals:
        raise ValueError('No solved state in trace')
    # The server may allocate states during lemma-bank and environment checks
    # before tracing starts. Infer the single unrecorded parent of the tree.
    roots = {r['parent'] for r in records if r['parent'] not in states}
    if len(roots) != 1:
        raise ValueError(f'Expected one trace root, found {sorted(roots)}')
    root_id = next(iter(roots))
    if 'root_state' in meta and meta['root_state'] != root_id:
        raise ValueError('Trace root does not match explicit metadata')
    current = finals[-1]
    steps, seen = [], set()
    while current in states:
        if current in seen:
            raise ValueError('Cyclic trace')
        seen.add(current)
        r = states[current]
        steps.append({'tactic': r['tactic'], 'goal_id': r['goal_id']})
        current = r['parent']
    if current != root_id:
        raise ValueError(f'Trace path does not reach root state {root_id} (got {current})')
    print(f'[TRACE] root state={root_id}, solved state={finals[-1]}', flush=True)
    return meta, steps[::-1]


def tactic_body(steps, focused):
    """Pantograph auto_resume moves selected goal descendants to the front.

    Batteries pick_goal preserves the relative order of all other goals;
    on_goal i alone instead inserts new goals at the old position.
    """
    result = []
    for step in steps:
        i = step['goal_id']
        if not isinstance(i, int) or i < 0:
            raise ValueError('Invalid goal id')
        t = step['tactic'].strip('\n')
        # v21 search-only budget is not allowed inside official proof bodies.
        if re.fullmatch(r'set_option maxHeartbeats \d+ in\n  apply [\w\'.]+ <;> \(first \| assumption \| rfl \| omega\)\n  done', t):
            t = t.splitlines()[1].strip()
        if i:
            result.append(f'  pick_goal {i+1}')
        if focused:
            result.append('  on_goal 1 =>\n' + textwrap.indent(t, '    '))
        else:
            result.append(textwrap.indent(t, '  '))
    return '\n'.join(result)


def check_axioms(output, name):
    # Lean prints this report after #print axioms. Fail closed if missing.
    name = re.escape(name)
    m = re.search(r"'"+name+r"' depends on axioms:\s*\[([^\]]*)\]", output, re.S)
    if m:
        found = {x.strip() for x in m.group(1).split(',') if x.strip()}
        return found <= ALLOWED, found
    if re.search(r"'"+name+r"' does not depend on any axioms", output):
        return True, set()
    return False, {'<unrecognized axiom report>'}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--trace', type=Path, required=True, help='v20 transitions.jsonl or v21 solved.json')
    p.add_argument('--root', type=Path, help='saved root.txt; tried before tactic reconstruction')
    p.add_argument('--source', type=Path, required=True, help='Original theorem file (read only)')
    p.add_argument('--output', type=Path, required=True, help='New standalone proof file outside repository')
    p.add_argument('--project', type=Path, default=Path.home()/'dev/pequalnp-proofs/lean')
    p.add_argument('--timeout', type=int, default=1200, help='Seconds per independent Lean check')
    p.add_argument('--source-imports', action='store_true', help='Use original file imports instead of search imports')
    args = p.parse_args()
    project = args.project.resolve()
    output = args.output.resolve()
    if output.is_relative_to(project.parent) or output.exists() or output.suffix != '.lean':
        p.error('output must be a new .lean file outside the project repository')
    meta, steps = load_path(args.trace)
    name, goal = meta.get('target'), meta['root_goal'].strip()
    if not name or not NAME.fullmatch(name):
        p.error('trace has no valid explicit target theorem name')
    source = args.source.read_text(encoding='utf-8')
    match = re.search(r'(?m)^theorem\s+'+re.escape(name)+r'\s*:\s*(.*?)\s*:=\s*by\b', source, re.S)
    if not match or match.group(1).strip() != goal:
        p.error('source statement does not exactly match the traced goal (this exporter supports explicit theorem NAME : GOAL := by)')
    imports = meta['imports']
    if args.source_imports:
        imports = [m for line in re.findall(r'(?m)^import\s+([^\n]+)', source) for m in line.split()]
    if not imports or not all(NAME.fullmatch(m) for m in imports):
        p.error('invalid import list')
    prefix = '\n'.join('import '+m for m in imports)+'\n\n'
    declaration = f'theorem {name} : {match.group(1).strip()} := '
    candidates = [('pantograph-ordered tactics', declaration+'by\n'+tactic_body(steps, False)),
                  ('pantograph-ordered focused tactics', declaration+'by\n'+tactic_body(steps, True))]
    if args.root:
        root_text = args.root.read_text(encoding='utf-8').strip()
        if re.search(r'(?<![\w.])_(?:proof|simp)_\d+\b', root_text):
            print('[SKIP] root term contains internal proof constants', flush=True)
        else:
            candidates.append(('root term', declaration+'\n'+textwrap.indent(root_text, '  ')))
    output.parent.mkdir(parents=True, exist_ok=True)
    print(f'[EXPORT] target={name}, recorded steps={len(steps)}, imports={imports}', flush=True)
    diagnostics = None
    with tempfile.TemporaryDirectory(prefix='lean-export-', dir=output.parent) as tmp:
        test_file = Path(tmp)/'Proof.lean'
        for index, (label, body) in enumerate(candidates, 1):
            code = prefix+body+'\n'
            if re.search(r'\b(sorry|admit|sorryAx|native_decide)\b', code):
                print(f'[SKIP] {label}: forbidden token', flush=True)
                continue
            test_file.write_text(code+f'\n#print axioms {name}\n', encoding='utf-8')
            print(f'[CHECK] {label}', flush=True)
            try:
                r = subprocess.run(['lake', 'env', 'lean', str(test_file)], cwd=project,
                                   capture_output=True, text=True, encoding='utf-8', errors='replace', timeout=args.timeout)
            except subprocess.TimeoutExpired:
                print('[FAILED] check timeout', flush=True)
                continue
            log = r.stdout+'\n'+r.stderr
            okay, axioms = check_axioms(log, name)
            if r.returncode or not okay or re.search(r'\berror:', log, re.I):
                if diagnostics is None:
                    diagnostics = Path(tempfile.mkdtemp(prefix='lean-export-diagnostics-', dir=output.parent))
                (diagnostics / f'candidate-{index}.lean').write_text(code+f'\n#print axioms {name}\n', encoding='utf-8')
                (diagnostics / f'candidate-{index}.log').write_text(log, encoding='utf-8')
                print(f'[FAILED] exit={r.returncode}; axioms={sorted(axioms)}\n{log[-4000:]}', flush=True)
                print(f'[DIAGNOSTICS] {diagnostics}', flush=True)
                continue
            # Exclusive creation; never overwrite a previously saved proof.
            with output.open('x', encoding='utf-8') as f:
                f.write(code)
            print(f'[AXIOMS] {sorted(axioms)}\n[OUTPUT] {output}\nSTANDALONE PROOF OK', flush=True)
            return
    raise SystemExit('EXPORT NOT VERIFIED: no candidate passed; nothing written')

if __name__ == '__main__':
    main()
