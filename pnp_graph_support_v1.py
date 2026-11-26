#!/usr/bin/env python3
"""Generate candidate positive graph proofs using a checked support-count template.
Never changes the repository or leases/submits a task. Source attribution retained.
"""
import argparse
import collections
import itertools
import re
import subprocess
import tempfile
from pathlib import Path

REV = '4581ea7890b48dd938941ef1f044563ea1129311'
BASE = 'lean/PEqualNP/Outside/'
TEMPLATE = 'L_meta_11573'
SAMPLES = ('L_meta_11066', 'L_meta_11573', 'L_meta_14086')
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def git_show(repo, ref, stem):
    return subprocess.check_output(['git', '-C', str(repo), 'show', f'{ref}:{BASE}{stem}.lean'], text=True, encoding='utf-8')


def parse(stem, source):
    name = 'PEqualNP.Outside.' + stem
    m = re.search(r'^theorem\s+' + re.escape(name) + r'\s*:', source, re.M)
    if not m:
        raise ValueError('main theorem not found')
    b = re.search(r'\s*:=\s*by\b', source[m.end():])
    if not b:
        raise ValueError('main theorem proof marker not found')
    decl = source[m.start():m.end()+b.start()].rstrip()
    statement = source[m.end():m.end()+b.start()].strip()
    if not statement.startswith('∀') or "gates'.length ≤ gates.length" not in statement:
        raise ValueError('unsupported statement: need positive graph no-saving theorem')
    ns = set(re.findall(r'Fin\s+(\d+)\s*→\s*Bool', statement))
    if len(ns) != 1:
        raise ValueError('inconsistent input count')
    n = int(ns.pop())
    if not 2 <= n <= 8:
        raise ValueError('only 2..8 vertices supported')
    lists = re.findall(r'\(\[([\d,\s]+)\]\s*:\s*List\s+ℕ\)', statement)
    flats = {tuple(map(int, re.findall(r'\d+', s))) for s in lists}
    if len(flats) != 1 or len(lists) != 6:
        raise ValueError('expected six identical literal edge lists')
    flat = flats.pop()
    if len(flat)%2 or not flat or any(x >= n for x in flat):
        raise ValueError('invalid edge list')
    edges = {tuple(sorted(p)) for p in zip(flat[::2],flat[1::2])}
    if any(a == b for a,b in edges) or set(itertools.chain.from_iterable(edges)) != set(range(n)):
        raise ValueError('loops or isolated vertices not supported')
    # Capture both actual RHS expressions, require exact same text modulo whitespace.
    rhss = []
    for match in re.finditer(r'=\s*(decide\s*\()', statement):
        start = match.start(1); pos = match.end(1); depth = 1
        while pos < len(statement) and depth:
            depth += (statement[pos] == '(') - (statement[pos] == ')')
            pos += 1
        if depth:
            raise ValueError('unbalanced RHS')
        rhss.append(statement[start:pos])
    if len(rhss) != 2 or re.sub(r'\s+','',rhss[0]) != re.sub(r'\s+','',rhss[1]):
        raise ValueError('unsupported RHS expressions')
    return decl, n, sorted(edges), rhss[0]


def verify(n, edges, gates, output):
    for bits in itertools.product((False, True), repeat=n):
        w = list(bits)
        for op,a,b in gates:
            if not (0 <= a < len(w) and 0 <= b < len(w)):
                raise ValueError('invalid wire')
            if op not in ('and','or'):
                raise ValueError('invalid operator')
            w.append((w[a] and w[b]) if op == 'and' else (w[a] or w[b]))
        if w[output] != any(bits[a] and bits[b] for a,b in edges):
            raise ValueError('truth-table mismatch')


def circuit_for_groups(n, groups):
    gates = []; cache = {}
    def emit(op,a,b):
        a,b = sorted((a,b))
        if a == b: return a
        key = (op,a,b)
        if key not in cache:
            cache[key] = n+len(gates); gates.append(key)
        return cache[key]
    # Each group is a biclique: OR(left) AND OR(right). Share OR pairs globally.
    sets = [set(s) for group in groups for s in group]
    while any(len(s)>1 for s in sets):
        counts = collections.Counter(pair for s in sets for pair in itertools.combinations(sorted(s),2))
        a,b = min(counts, key=lambda p: (-counts[p], p))
        k = emit('or',a,b)
        for s in sets:
            if a in s and b in s:
                s.difference_update((a,b)); s.add(k)
    terms = [emit('and', next(iter(sets[i])), next(iter(sets[i+1]))) for i in range(0,len(sets),2)]
    out = terms[0]
    for t in terms[1:]: out = emit('or',out,t)
    return gates,out


def synth(n, edges):
    adj = [set() for _ in range(n)]
    for a,b in edges: adj[a].add(b); adj[b].add(a)
    best = None; seen = set()
    # High-degree first, then all vertex orders. Orient each edge once, merge
    # equal neighbour sets, and factor shared ORs. This is a heuristic, not a lower bound.
    orders = itertools.chain([tuple(sorted(range(n),key=lambda v:-len(adj[v])))],itertools.permutations(range(n)))
    for order in orders:
        left = set(range(n)); by_neighbours = collections.defaultdict(list)
        for v in order:
            left.remove(v); nbr = tuple(sorted(adj[v]&left))
            if nbr: by_neighbours[nbr].append(v)
        groups = tuple(sorted(tuple(sorted((tuple(sorted(vs)),nbr))) for nbr,vs in by_neighbours.items()))
        if groups in seen: continue
        seen.add(groups)
        gates,out = circuit_for_groups(n,groups)
        if best is None or len(gates)<len(best[0]): best=(gates,out)
        if len(gates)<=n-1: break
        # Stop as soon as support counting is sufficient.
        if len(gates)<=n: break
    verify(n,edges,*best)
    return best


def render(stem, source, template, ref):
    decl,n,edges,rhs = parse(stem,source)
    gates,out = synth(n,edges)
    print(f'[WITNESS] {stem} n={n} gates={len(gates)} / bound={n}; all {2**n} rows PASS', flush=True)
    if len(gates)>n:
        return None
    # Extract only the existing general helper block; do not import or rely on
    # the earlier target theorem or its graph-specific proof.
    prefix, sep, rest = template.partition('\ndef graph (')
    if not sep or prefix.count('namespace PEqualNP.Outside.'+TEMPLATE)!=1 or 'theorem sum_lt' not in prefix:
        raise ValueError('template helper structure changed')
    if re.search(r'\b(?:sorry|admit|axiom|native_decide)\b', prefix):
        raise ValueError('unexpected token in template')
    prefix = prefix.replace('namespace PEqualNP.Outside.'+TEMPLATE, 'namespace PEqualNP.Outside.'+stem,1)
    prefix = f'-- Support-count helpers adapted from {BASE}{TEMPLATE}.lean at {ref}.\n-- Source: https://github.com/open-goat/pequalnp-proofs\n'+prefix
    lower_start = rest.index('theorem lower (gates : List Gate)')
    lower_end = rest.index('\ndef witness',lower_start)
    lower = rest[lower_start:lower_end]
    for old,new in [('Fin 7',f'Fin {n}'),('    7 ≤',f'    {n} ≤'),('inputSupps 7',f'inputSupps {n}'),('.card = 7',f'.card = {n}')]:
        if old not in lower: raise ValueError('template lower structure changed: '+old)
        lower = lower.replace(old,new)
    dnf = ' || '.join(f'(x {a} && x {b})' for a,b in edges)
    dep = '\n'.join(f'  · exact ⟨fun j => decide (j = {next(b if a==i else a for a,b in edges if i in (a,b))}), by decide +kernel⟩' for i in range(n))
    witness = ', '.join(f'⟨.{op}, [{a}, {b}]⟩' for op,a,b in gates)
    text = prefix + f'''\nset_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
def graph (x : Fin {n} → Bool) : Bool := {dnf}
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem graph_dep : ∀ i : Fin {n}, ∃ x : Fin {n} → Bool,
    graph (Function.update x i (!x i)) ≠ graph x := by
  intro i
  fin_cases i
{dep}
{lower}
def witness : List Gate := [{witness}]
theorem witnessBasis : ∀ g ∈ witness,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with {' | '.join(['rfl']*len(gates))} <;> simp
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem witnessCorrect : ∀ x : Fin {n} → Bool,
    Circuit.eval ⟨witness, {out}⟩ (List.ofFn x) = graph x := by
  decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem graph_correct : ∀ x : Fin {n} → Bool, graph x = {rhs} := by
  decide +kernel
end PEqualNP.Outside.{stem}
open PEqualNP.Outside.{stem} PEqualNP.CircuitLowerBounds in
{decl} := by
  intro gates o legal _oneNot computes
  have hev : ∀ x : Fin {n} → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = graph x :=
    fun x => (computes x).trans (graph_correct x).symm
  by_cases hn : ∃ g ∈ gates, g.op = GateOp.not
  · obtain ⟨g, hg, hgn⟩ := hn
    have hl := lower gates o hev
    have hs := sum_lt gates (fun g' hg' => cost_le g' (legal g' hg').2) ⟨g, hg, cost_not g hgn⟩
    have hw : witness.length = {len(gates)} := rfl
    exact ⟨witness, {out}, witnessBasis, by omega, fun x => (witnessCorrect x).trans (graph_correct x)⟩
  · refine ⟨gates, o, ?_, le_rfl, computes⟩
    intro g hg
    refine ⟨?_, (legal g hg).2⟩
    rcases (legal g hg).1 with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd ⟨g, hg, h⟩ hn
'''
    return text


def check(repo, stem, text, outdir, timeout):
    outdir.mkdir(parents=True,exist_ok=True)
    name='PEqualNP.Outside.'+stem
    # Save candidate and check log even when it fails. No source tree changes.
    with tempfile.TemporaryDirectory(prefix='graph-support-',dir=outdir) as d:
        p=Path(d)/'Proof.lean'; p.write_text(text+'\n#print axioms '+name+'\n',encoding='utf-8')
        try:
            r=subprocess.run(['lake','env','lean',str(p.resolve())],cwd=repo/'lean',capture_output=True,text=True,encoding='utf-8',timeout=timeout)
            log=r.stdout+'\n'+r.stderr
            ok=r.returncode==0
        except subprocess.TimeoutExpired as e:
            log='TIMEOUT\n'+str(e); ok=False
    (outdir/(stem+'.check.log')).write_text(log,encoding='utf-8')
    m=re.search(r"'"+re.escape(name)+r"' depends on axioms:\s*\[([^\]]*)\]",log)
    axioms={a.strip() for a in m.group(1).split(',') if a.strip()} if m else None
    ok=ok and axioms is not None and axioms<=ALLOWED
    print(f'[CHECK] {stem} {"PASS" if ok else "FAIL"} axioms={sorted(axioms) if axioms is not None else None}',flush=True)
    if not ok: print(log[-4000:],flush=True)
    return ok


def self_test():
    cases=[(7,[(a,b) for a in range(4) for b in range(4,7)],6),
           (7,[(a,b) for b,aa in [(5,[0,1,2]),(6,[0,1,3,4])] for a in aa],7),
           (8,[(a,b) for b,aa in [(6,[0,1,2,3]),(7,[0,1,4,5])] for a in aa],8)]
    for n,e,k in cases:
        g,o=synth(n,e); assert len(g)<=k,(n,len(g),k); verify(n,e,g,o)
        print(f'[SELF TEST] n={n}, gates={len(g)} PASS')
    print('SELF TEST OK')


def main():
    p=argparse.ArgumentParser(); p.add_argument('--repo',type=Path,default=Path.home()/'dev/pequalnp-proofs'); p.add_argument('--ref',default=REV); p.add_argument('--output',type=Path,default=Path.home()/'dev/LeanDojo-v2/proof-logs/graph-support-v1'); p.add_argument('--source',type=Path); p.add_argument('--regression',action='store_true'); p.add_argument('--self-test',action='store_true'); p.add_argument('--check',action='store_true'); p.add_argument('--timeout',type=int,default=300); a=p.parse_args()
    if a.self_test: self_test(); return
    if bool(a.source)==a.regression: p.error('choose --source or --regression')
    if a.timeout<1: p.error('timeout must be positive')
    repo=a.repo.expanduser().resolve(); outdir=a.output.expanduser().resolve(); outdir.mkdir(parents=True,exist_ok=True)
    if outdir.is_relative_to(repo): p.error('output must be outside repository')
    ref=subprocess.check_output(['git','-C',str(repo),'rev-parse','--verify',a.ref+'^{commit}'],text=True).strip()
    template=git_show(repo,ref,TEMPLATE)
    tasks=[(s,git_show(repo,ref,s)) for s in SAMPLES] if a.regression else [(a.source.stem,a.source.read_text(encoding='utf-8'))]
    all_ok=True
    for stem,source in tasks:
        if not re.fullmatch(r'L_meta_\d+',stem): raise ValueError('unsupported target name')
        candidate=render(stem,source,template,ref)
        if candidate is None:
            print('[SKIP] support bound insufficient (not a negative result)'); all_ok=False; continue
        path=outdir/(stem+'.candidate.lean'); path.write_text(candidate,encoding='utf-8'); print('[CANDIDATE]',path,flush=True)
        if a.check:
            if check(repo,stem,candidate,outdir,a.timeout):
                path2=outdir/(stem+'.verified.lean'); path2.write_text(candidate,encoding='utf-8'); print('[VERIFIED]',path2,flush=True)
            else: all_ok=False
    print('REGRESSION OK' if a.regression and a.check and all_ok else 'DONE (see statuses; no submission)')
    if not all_ok: raise SystemExit(1)

if __name__=='__main__': main()
