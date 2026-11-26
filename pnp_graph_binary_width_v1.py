#!/usr/bin/env python3
"""Compare reduced-width signed-live-search proofs using saved Binary v3 candidates.
No repo modifications; numerical screening never substitutes for Lean verification.
"""
import argparse, json, random, re, time
from pathlib import Path
import pnp_graph_binary_v3 as binary
import pnp_graph_support_v1 as support

DEFAULT = Path.home() / 'dev/LeanDojo-v2/proof-logs'
ROW_RE = re.compile(r'^def rows : List Nat := \[([^\n]*)\]$', re.M)
ROOT_RE = re.compile(r'^def roots : List W := \[([^\n]*)\]$', re.M)


def words_for(rows, n):
    return [sum(((r >> i) & 1) << j for j, r in enumerate(rows)) for i in range(n)]


def select_rows(rows, n, width, seed):
    half = width // 2
    if len(rows) != 512 or not n <= half <= 256:
        raise ValueError('invalid original rows or width')
    # Original first n pairs witness essentiality of each input. Keep all of them.
    for i in range(n):
        if rows[i] ^ rows[i+256] != 1 << i:
            raise ValueError('essential pairs do not match Binary v3 format')
    indices = list(range(n)) + sorted(random.Random(seed).sample(range(n,256),half-n))
    return [rows[i] for i in indices] + [rows[i+256] for i in indices]


def screen(words, width, cap, seconds, max_states):
    # v3 uses module-level masks; change them only for the duration of a sequential call.
    previous = binary.HALF, binary.MASK, binary.TARGET, binary.sep
    half = width // 2
    mask = (1 << half)-1
    try:
        binary.HALF = mask
        binary.MASK = (1 << width)-1
        binary.TARGET = mask << half
        binary.sep = lambda w: ((w >> half)^w)&mask
        return binary.screen(words, cap, seconds, max_states)
    finally:
        binary.HALF, binary.MASK, binary.TARGET, binary.sep = previous


def rewrite(text, stem, rows, words, width):
    # Restrict dimension changes to the helper definitions before `rows`,
    # and the three generated Fin 512 types after it. Never rewrite theorem statement.
    rm = ROW_RE.search(text)
    if not rm or len(ROW_RE.findall(text)) != 1 or len(ROOT_RE.findall(text)) != 1:
        raise ValueError('unexpected generated source layout')
    prefix, rest = text[:rm.start()], text[rm.start():]
    for required in ('abbrev W := BitVec 512','def sep (x : W) : BitVec 256','def goal : W := (-1 : BitVec 256) ++ (0 : BitVec 256)'):
        if required not in prefix: raise ValueError('unexpected helper: '+required)
    prefix = re.sub(r'\b(?:512|256)\b', lambda m: str(width if m[0]=='512' else width//2), prefix)
    rest = ROW_RE.sub('def rows : List Nat := ['+', '.join(map(str,rows))+']',rest)
    rest = ROOT_RE.sub('def roots : List W := ['+', '.join(map(hex,words))+']',rest)
    name = 'theorem PEqualNP.Outside.' + stem
    if rest.count(name) != 1: raise ValueError('missing or duplicate final theorem')
    at = rest.index(name)
    body, final = rest[:at], rest[at:]
    if body.count('Fin 512') != 3: raise ValueError('unexpected number of generated row index types')
    body = body.replace('Fin 512',f'Fin {width}')
    changed = prefix+body+final
    assert binary.parse_statement(stem,changed) == binary.parse_statement(stem,text)
    return changed


def benchmark(text, stem, width, seeds, seconds, max_states):
    _,n,edges,_=binary.parse_statement(stem,text)
    rm=ROW_RE.search(text)
    if not rm: raise ValueError('missing rows')
    rows=[int(s.strip()) for s in rm[1].split(',')]
    cap=int(re.search(r'^theorem noSearch : search (\d+) roots = false := by$',text,re.M)[1])
    def f(r): return any(r>>a&1 and r>>b&1 for a,b in edges)
    if len(rows)!=512 or any(not 0<=r<1<<n or f(r)!=(i>=256) for i,r in enumerate(rows)):
        raise ValueError('original sample table invalid')
    best=None
    for seed in range(seeds if width<512 else 1):
        rr=select_rows(rows,n,width,seed); ww=words_for(rr,n)
        assert all(f(r)==(i>=width//2) for i,r in enumerate(rr))
        if len(set(ww))!=n: raise ValueError('duplicate root')
        result,states,elapsed=screen(ww,width,cap,seconds,max_states)
        print(f'[SCREEN] width={width} seed={seed} {result} states={states} wall={elapsed:.3f}s',flush=True)
        if result=='NO_RUN' and (best is None or states<best[0]): best=(states,seed,rr,ww)
    return best


def self_test():
    n=4; edges=[(0,2),(0,3),(1,2),(1,3)]
    rows,words=binary.make_rows(n,edges)
    for width in (32,64,128,256,512):
        rr=select_rows(rows,n,width,0); ww=words_for(rr,n)
        assert screen(ww,width,2,10,100000)[0]=='NO_RUN'
        assert screen(ww,width,3,10,100000)[0]=='REACHABLE'
        assert binary.HALF==(1<<256)-1 and binary.MASK==(1<<512)-1
    print('[SELF TEST] reduced-width positive/negative search and mask restoration PASS')
    stem='L_meta_123'
    rhs='decide (∃ i < ([0, 1] : List ℕ).length / 2, (List.ofFn x).getD (([0, 1] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 1] : List ℕ).getD (2 * i + 1) 0) false = true)'
    decl=f"theorem PEqualNP.Outside.{stem} : ∀ (gates : List Nat), (∀ x : Fin 2 → Bool, true = {rhs}) → ∃ gates' : List Nat, gates'.length ≤ gates.length ∧ ∀ x : Fin 2 → Bool, true = {rhs}"
    old='abbrev W := BitVec 512\ndef sep (x : W) : BitVec 256 := 0\ndef goal : W := (-1 : BitVec 256) ++ (0 : BitVec 256)\ndef rows : List Nat := [0,1]\ndef sample (k : Fin 512) := 0\ndef roots : List W := [0,1]\ntheorem a : ∀ k : Fin 512, True := by simp\ntheorem b : ∀ k : Fin 512, True := by simp\n'+decl+' := by\n  sorry\n'
    new=rewrite(old,stem,[0,1,2,3],[3,5],64)
    assert 'BitVec 64' in new and 'BitVec 32' in new and new.count('Fin 64')==3
    assert new[new.index(decl):]==old[old.index(decl):]
    print('[SELF TEST] exact statement and final proof preservation PASS')
    print('SELF TEST OK')


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--self-test',action='store_true'); p.add_argument('--id',default='L_meta_14074')
    p.add_argument('--from-dir',type=Path,default=DEFAULT/'graph-binary-extra2')
    p.add_argument('--out',type=Path,default=DEFAULT/'graph-binary-width-v1')
    p.add_argument('--repo',type=Path,default=Path.home()/'dev/pequalnp-proofs')
    p.add_argument('--widths',nargs='+',type=int,default=[64,128,256]); p.add_argument('--seeds',type=int,default=3)
    p.add_argument('--seconds',type=float,default=10); p.add_argument('--max-states',type=int,default=500000)
    p.add_argument('--check-count',type=int,default=1); p.add_argument('--timeout',type=int,default=600)
    a=p.parse_args()
    if a.self_test: self_test(); return
    if not re.fullmatch(r'L_meta_\d+',a.id) or any(w not in (32,64,128,256,512) for w in a.widths): p.error('invalid target or width')
    if min(a.seeds,a.seconds,a.max_states,a.timeout)<1 or a.check_count<0: p.error('invalid limits')
    repo,src,out=(x.expanduser().resolve() for x in (a.repo,a.from_dir,a.out))
    if out.is_relative_to(repo) or out==src: p.error('output must be separate and outside repo')
    text=(src/(a.id+'.candidate.lean')).read_text(encoding='utf-8')
    out.mkdir(parents=True,exist_ok=True)
    records=[]; choices=[]
    def save():
        tmp=out/'results.json.tmp'; tmp.write_text(json.dumps(records,indent=2)+'\n',encoding='utf-8'); tmp.replace(out/'results.json')
    for width in sorted(set(a.widths)):
        best=benchmark(text,a.id,width,a.seeds,a.seconds,a.max_states)
        r={'width':width,'status':'NO_RUN' if best else 'NO_CANDIDATE'}; records.append(r)
        if best:
            states,seed,rr,ww=best
            candidate=rewrite(text,a.id,rr,ww,width)
            d=out/f'width-{width}'; d.mkdir(exist_ok=True)
            path=d/(a.id+'.candidate.lean'); path.write_text(candidate,encoding='utf-8')
            r.update(states=states,seed=seed,candidate=str(path)); choices.append((r,d,candidate))
            print(f'[CANDIDATE] width={width} states={states} {path}',flush=True)
        save()
    # Smallest width first, then try larger widths if a smaller proof fails.
    passed=0; attempted=0
    for r,d,candidate in choices:
        if passed>=a.check_count: break
        verified=d/(a.id+'.verified.lean')
        if verified.exists(): verified.unlink()
        t=time.monotonic(); attempted+=1
        ok=support.check(repo,a.id,candidate,d,a.timeout)
        sec=time.monotonic()-t; r.update(lean_ok=ok,lean_seconds=round(sec,3))
        print(f'[LEAN TIME] width={r["width"]} {sec:.3f}s',flush=True)
        if ok:
            verified.write_text(candidate,encoding='utf-8'); passed+=1; print('[VERIFIED]',verified,flush=True)
        save()
    print(f'[SUMMARY] width candidates={len(choices)} Lean={passed}/{attempted} (no submission)',flush=True)
    if not choices or (a.check_count and not passed): raise SystemExit(1)

if __name__=='__main__': main()
