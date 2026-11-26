#!/usr/bin/env python3
"""Generate and verify a proof of a six-input monotone table statement. No submission."""
import argparse, random, time, json, re, subprocess
from functools import lru_cache
from pathlib import Path
import pnp_graph_support_v1 as support
import pnp_graph_binary_v3 as binary
import pnp_graph_binary_width_v1 as widthlib
import pnp_graph_certificate_v3 as guard

N=6
T=3941264008*2**32+3937053320
STEM='L_meta_15579'
NS='PEqualNP.Outside.'+STEM
RHS='Nat.testBit (3941264008 * 2 ^ 32 + 3937053320) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)'
GATES=[('or',3,4),('or',1,6),('and',0,7),('and',3,4),('and',5,6),('or',9,10),('and',1,2),('and',11,12),('or',8,13)]
OUTPUT=14
PROP=f'∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => {RHS}) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = {RHS}'

FULL=(1<<(1<<N))-1
V=[sum(1<<x for x in range(1<<N) if (x>>i)&1) for i in range(N)]
def op(k,a,b):
 if a==b:return a
 if k=='and':
  if 0 in (a,b):return 0
  if 1 in (a,b):return b if a==1 else a
 else:
  if 1 in (a,b):return 1
  if 0 in (a,b):return b if a==0 else a
 return (k,*sorted((a,b),key=repr))
def nodes(e):
 if isinstance(e,tuple) and len(e)==3:return {e}|nodes(e[1])|nodes(e[2])
 return set()
def fold(k,es):
 es=list(es)
 if not es:return int(k=='and')
 while len(es)>1:
  es.sort(key=lambda e:(len(nodes(e)),repr(e)))
  a,b=es[:2];es=[op(k,a,b)]+es[2:]
 return es[0]
def minimal(f):return [x for x in range(64) if (f>>x)&1 and all(not ((f>>(x^(1<<i)))&1) for i in range(N) if x&(1<<i))]
def maximalzero(f):return [x for x in range(64) if not (f>>x)&1 and all((f>>(x|(1<<i)))&1 for i in range(N) if not x&(1<<i))]
def termtable(ts):return sum(1<<x for x in range(64) if any(x&t==t for t in ts))
def clause_table(ts):return sum(1<<x for x in range(64) if all(x&t for t in ts))
@lru_cache(None)
def best(f):
 if f==0:return 0
 if f==FULL:return 1
 if f in V:return ('x',V.index(f))
 ts=minimal(f);cs=[63^x for x in maximalzero(f)]
 opts=[fold('or',[fold('and',[('x',i) for i in range(N) if t&(1<<i)]) for t in ts]),fold('and',[fold('or',[('x',i) for i in range(N) if t&(1<<i)]) for t in cs])]
 for i in range(N):
  bit=1<<i;v=('x',i)
  lo=sum(((f>>(x&~bit))&1)<<x for x in range(64));hi=sum(((f>>(x|bit))&1)<<x for x in range(64))
  if lo==hi:continue
  opts.extend([op('or',best(lo),op('and',v,best(hi))),op('and',best(hi),op('or',v,best(lo)))])
  a=termtable([t^bit for t in ts if t&bit]);b=clause_table([t^bit for t in cs if t&bit])
  opts.extend([op('or',best(lo),op('and',v,best(a))),op('and',best(hi),op('or',v,best(b)))])
 return min(opts,key=lambda e:(len(nodes(e)),len(repr(e)),repr(e)))

def truth(x): return (T>>x)&1

def validate():
    for x in range(64):
        w=[(x>>i)&1 for i in range(N)]
        for op,a,b in GATES: w.append(w[a]&w[b] if op=='and' else w[a]|w[b])
        assert w[OUTPUT]==truth(x),x
        assert all(truth(x)<=truth(x|(1<<i)) for i in range(N))
    print(f'[WITNESS] table={T:#018x} gates={len(GATES)} all 64 rows PASS',flush=True)

def pairs(width,seed):
    h=width//2
    essential=[next((x,x|(1<<i)) for x in range(64) if not (x>>i)&1 and not truth(x) and truth(x|(1<<i))) for i in range(N)]
    pool=[(x,y) for x in range(64) for y in range(64) if not truth(x) and truth(y) and (x,y) not in essential]
    random.Random(seed).shuffle(pool); pool.sort(key=lambda p:(p[0]^p[1]).bit_count())
    chosen=essential+pool[:h-N]
    if len(chosen)<h: chosen += [chosen[i%len(chosen)] for i in range(h-len(chosen))]
    rows=[x for x,y in chosen]+[y for x,y in chosen]
    assert len(rows)==width and all(truth(r)==int(i>=h) for i,r in enumerate(rows))
    return rows,widthlib.words_for(rows,N)

def render(template,width,rows,words):
    m=len(GATES); cap=m-2
    prefix=binary.helpers(template,STEM,support.REV)
    assert 'abbrev W := BitVec 512' in prefix and 'def sep (x : W) : BitVec 256' in prefix
    prefix=re.sub(r'\b(?:512|256)\b',lambda m:str(width if m[0]=='512' else width//2),prefix)
    # Template may import only CircuitLowerBounds. Add the exact allowed definitions root.
    prefix=re.sub(r'^import[^\n]*\n','',prefix,flags=re.M)
    prefix='import Mathlib\nimport PEqualNP.Defs\n'+prefix
    witness=', '.join(f'⟨.{op}, [{a}, {b}]⟩' for op,a,b in GATES)
    data=', '.join(map(str,rows)); roots=', '.join(map(hex,words))
    text=prefix+f'''
def rows : List Nat := [{data}]
def sample (k : Fin {width}) (i : Fin 6) : Bool := (rows.getD k.val 0).testBit i.val
def roots : List W := [{roots}]
def posted (x : Fin 6 → Bool) : Bool := {RHS}
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem rootBits : ∀ k : Fin {width}, roots.map (bitlu k) = List.ofFn (sample k) := by
  decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem rowSpec : ∀ k : Fin {width}, posted (sample k) = bitlu k cible := by
  decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem noSearch : search {cap} roots = false := by
  decide +kernel

theorem binaryBound (gs : List Gate) (o : Nat) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = posted x) : {m-1} ≤ binaryCost gs := by
  by_contra! small
  have h := compileCible gs o hg roots roots.toFinset (fun w hw => .inr (.inr ⟨w,List.mem_toFinset.mpr hw,.inl rfl⟩))
    (fun k => by
      change (Circuit.mk gs o).eval (roots.map (bitlu k)) = bitlu k cible
      rw [rootBits]
      exact (he _).trans (rowSpec k))
  have bound : binaryCost gs ≤ {cap} := by omega
  have hb := sb_le bound h
  have nc : cible ≠ 0 ∧ cible ≠ ~~~0 := by decide +kernel
  have ex : ∃ t, (t = goal ∨ t = ~~~goal) ∧ build basicOps t {cap} roots.toFinset := by
    rcases hb with h|h|h|h
    · exact (nc.1 h).elim
    · exact (nc.2 h).elim
    · exact ⟨_, .inl rfl, h⟩
    · exact ⟨_, .inr rfl, h⟩
  obtain ⟨t,ht,run⟩ := ex
  have hh := search_complete ht {cap} roots (by decide +kernel) run
  rw [noSearch] at hh
  contradiction

def monoWitness : List Gate := [{witness}]
theorem monoShape : ∀ g ∈ monoWitness, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [monoWitness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with {' | '.join(['rfl']*m)} <;> simp
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem monoCorrect : ∀ x : Fin 6 → Bool, Circuit.eval ⟨monoWitness,{OUTPUT}⟩ (List.ofFn x) = posted x := by
  decide +kernel
end {NS}
open {NS} PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
{DECL} := by
  intro s hs
  rcases hs with ⟨⟨gs,o⟩, hlegal, hsize, he⟩
  have legalG : ∀ g ∈ gs, legal g := by
    intro g hg
    have h := hlegal g hg
    simpa [legal, Set.mem_insert_iff, Set.mem_singleton_iff] using h
  have correct : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = posted x := he
  by_cases hn : ∃ g ∈ gs, g.op = GateOp.not
  · obtain ⟨g,hg,hop⟩ := hn
    have lb := binaryBound gs o legalG correct
    have strict : binaryCost gs < gs.length := (List.length_filter_lt_length_iff_exists (p := isBinary)).mpr ⟨g,hg,by simp [isBinary,hop]⟩
    have hs' : gs.length ≤ s := hsize
    have hw : monoWitness.length = {m} := rfl
    have hm : Monotone2 ⟨monoWitness,{OUTPUT}⟩ := by
      intro g hg
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using monoShape g hg
    refine ⟨⟨monoWitness,{OUTPUT}⟩, hm, ?_, monoCorrect⟩
    change monoWitness.length ≤ s
    omega
  · refine ⟨⟨gs,o⟩, ?_, hsize, he⟩
    intro g hg
    have h := legalG g hg
    refine ⟨?_, h.2⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases h.1 with h'|h'|h'
    · exact Or.inl h'
    · exact Or.inr h'
    · exact absurd ⟨g,hg,h'⟩ hn
'''
    # No global resource overrides; retain declaration-local depth settings.
    text=text.replace("set_option maxRecDepth 32000 in", "set_option maxRecDepth 60000 in")
    text=re.sub(r"^set_option (?:maxRecDepth|exponentiation.threshold) \d+[ \t]*\n", "", text, flags=re.M)
    return text


def render_split(text,stem,split_depth,max_states,seconds):
    rm=re.search(r'^def roots : List W := \[([^\n]*)\]$',text,re.M)
    nm=re.search(r'^theorem noSearch : search (\d+) roots = false := by\n  decide \+kernel\n',text,re.M)
    wm=re.search(r'^abbrev W := BitVec (\d+)$',text,re.M)
    if not rm or not nm or not wm: raise ValueError('unexpected table candidate')
    w=int(wm[1]); half=w//2
    prev=(guard.HALF,guard.MASK,guard.GOAL,guard.cuts)
    guard.HALF=(1<<half)-1; guard.MASK=(1<<w)-1; guard.GOAL=guard.HALF<<half
    def cuts(ws):
        result=0
        for x in ws: result |= ((x>>half)^x)&guard.HALF
        return result
    guard.cuts=cuts
    roots=tuple(int(s.strip(),0) for s in rm[1].split(',')); cap=int(nm[1])
    try: nodes,wall=guard.certificate(roots,cap,split_depth,max_states,seconds)
    finally: guard.HALF,guard.MASK,guard.GOAL,guard.cuts=prev
    # Nodes inserted in reverse topological order. Each proof cites only earlier nodes.
    ids={key:i for i,key in enumerate(nodes)}
    root=(cap,roots); parts=[guard.LEAN_HELPERS]; transitions=0; leaves=0
    for key,(leaf,ch) in nodes.items():
        k,ws=key; i=ids[key]; n=f'certS{i}'; proof=f'certP{i}'
        words=', '.join(map(hex,ws))
        parts.append(f'\ndef {n} : List W := [{words}]\n')
        if leaf:
            leaves+=1
            parts.append(f'set_option maxRecDepth 60000 in\nset_option maxHeartbeats 0 in\ntheorem {proof} : CertDead {k} {n} := by\n  exact certLeaf {k} {n} (by decide +kernel) (by decide +kernel) (by decide +kernel)\n')
        else:
            transitions+=len(ch)
            # Local computation establishes exact enumeration; omissions cannot pass.
            expected=', '.join('certS'+str(ids[c]) for c in ch)
            term=f'certNil {k-1}'
            for c in reversed(ch): term=f'certCons certP{ids[c]} ({term})'
            parts.append(f'set_option maxRecDepth 60000 in\nset_option maxHeartbeats 0 in\ntheorem {proof} : CertDead {k} {n} := by\n  apply certNode {k-1} {n} (by decide +kernel) (by decide +kernel)\n  have hc : certChildren {k-1} {n} = [{expected}] := by decide +kernel\n  rw [hc]\n  exact {term}\n')
    rid=ids[root]
    parts.append(f'''\nset_option maxHeartbeats 0 in
theorem certRootCover : roots.sublists.all (fun ws => (cuts ws != -1) || (ws == roots)) = true := by
  decide +kernel
theorem certRootDead : CertDead {cap} roots := by
  exact certP{rid}
''')
    # Existing scoped options directly before noSearch now scope the first helper.
    # Remove those two lines, which would otherwise scope only certInsert.
    start=nm.start(); before=text[:start]; suffix='set_option maxRecDepth 60000 in\nset_option maxHeartbeats 0 in\n'
    if before.endswith(suffix): before=before[:-len(suffix)]
    old=f'  have hh := search_complete ht {cap} roots (by decide +kernel) run\n  rw [noSearch] at hh\n  contradiction'
    if text.count(old)!=1: raise ValueError('unexpected binaryBound proof')
    new=before+'\n'.join(parts)+text[nm.end():]
    new=new.replace(old,f'  exact certNoBuild ht {cap} roots certRootCover certRootDead run')
    marker='theorem PEqualNP.Outside.'+stem+' :'
    if new.count(marker)!=1 or text.count(marker)!=1 or new.split(marker)[1]!=text.split(marker)[1]: raise ValueError('statement changed')
    if re.search(r'\b(?:sorry|admit|axiom|native_decide)\b',new): raise ValueError('unsafe token')
    return new,dict(nodes=len(nodes),leaves=leaves,transitions=transitions,seconds=wall,cap=cap)

def normalized(x): return re.sub(r'\s+', '', x)

def parse(source):
    global T, STEM, NS, RHS, PROP, DECL
    ms=list(re.finditer(r'^theorem\s+PEqualNP\.Outside\.(L_meta_\d+)\s*:',source,re.M))
    if len(ms)!=1: raise ValueError('expected one target theorem')
    m=ms[0]; end=source.find(':=',m.end())
    if end<0: raise ValueError('missing theorem assignment')
    DECL=source[m.start():end].rstrip(); STEM=m[1]; NS='PEqualNP.Outside.'+STEM
    rhs=re.search(r'Nat\.testBit\s*\(\s*(\d+)\s*\*\s*2\s*\^\s*32\s*\+\s*(\d+)\s*\)\s*\(∑\s*i\s*:\s*Fin\s*6\s*,\s*if\s*x\s*i\s*then\s*2\s*\^\s*\(i\s*:\s*ℕ\)\s*else\s*0\s*\)',DECL)
    if not rhs: raise ValueError('not supported six-input table syntax')
    hi,lo=map(int,rhs.groups())
    if not (0<=hi<2**32 and 0<=lo<2**32): raise ValueError('table outside 64-bit range')
    T=hi*2**32+lo; RHS=rhs[0]
    PROP=f'∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => {RHS}) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = {RHS}'
    if normalized(DECL) not in [normalized(f'theorem {NS} : ({PROP})'),normalized(f'theorem {NS} : {PROP}')]: raise ValueError('not the supported positive statement (negative or other form)')
    if not all(truth(x)<=truth(x|(1<<i)) for x in range(64) for i in range(6)): raise ValueError('not monotone')
    if not all(any(truth(x)!=truth(x^(1<<i)) for x in range(64)) for i in range(6)): raise ValueError('requires six essential inputs')

def synthesize():
    global GATES, OUTPUT
    best.cache_clear(); expr=best(T); GATES=[]; cache={}
    def emit(e):
        if isinstance(e,int): raise ValueError('constant in circuit')
        if e[0]=='x': return e[1]
        if e not in cache:
            a,b=map(emit,e[1:]); cache[e]=6+len(GATES); GATES.append((e[0],a,b))
        return cache[e]
    OUTPUT=emit(expr); validate()

def self_test():
    original='theorem PEqualNP.Outside.L_meta_15579 : ('+PROP+') := by\n  sorry\n'
    parse(original); synthesize(); assert len(GATES)==9
    rows,words=pairs(128,0); r,n,t=widthlib.screen(words,128,len(GATES)-2,10,500000); assert r=='NO_RUN'
    try: parse(original.replace(': (∀',': (¬ (∀',1))
    except ValueError: pass
    else: raise AssertionError('negative accepted')
    # Verify certificate construction for a real 10-gate table with 512/128-bit roots.
    global T
    T=4007717024*2**32+4007657472; synthesize()
    for w in (128,512):
        rows,words=pairs(w,0)
        fake=f'abbrev W := BitVec {w}\ndef roots : List W := [{", ".join(map(hex,words))}]\nset_option maxRecDepth 60000 in\nset_option maxHeartbeats 0 in\ntheorem noSearch : search 8 roots = false := by\n  decide +kernel\n\n  have hh := search_complete ht 8 roots (by decide +kernel) run\n  rw [noSearch] at hh\n  contradiction\ntheorem PEqualNP.Outside.L_meta_15579 : True := by\n  trivial\n'
        new,meta=render_split(fake,'L_meta_15579',1,100000,10)
        assert meta['leaves']>0 and 'exact certNoBuild ht 8' in new and 'theorem noSearch' not in new
        assert new.endswith('theorem PEqualNP.Outside.L_meta_15579 : True := by\n  trivial\n')
        print('[SELF TEST] split width',w,meta,flush=True)
    print('SELF TEST OK (Python only)',flush=True)

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--source',type=Path); p.add_argument('--self-test',action='store_true')
    p.add_argument('--repo',type=Path,default=Path.home()/'dev/pequalnp-proofs')
    p.add_argument('--out',type=Path,default=Path.home()/'dev/LeanDojo-v2/proof-logs/table-solve-v2')
    p.add_argument('--widths',type=int,nargs='+',default=[128,256,512]); p.add_argument('--seeds',type=int,default=2)
    p.add_argument('--seconds',type=float,default=5); p.add_argument('--max-states',type=int,default=500000)
    p.add_argument('--check',action='store_true'); p.add_argument('--install',action='store_true'); p.add_argument('--check-limit',type=int,default=2)
    p.add_argument('--split-threshold',type=int,default=1000);p.add_argument('--split-depth',type=int,default=1);p.add_argument('--timeout',type=float,default=1800);p.add_argument('--max-rss-gib',type=float,default=20);p.add_argument('--jobs',type=int,default=4)
    a=p.parse_args()
    if a.self_test: self_test(); return 0
    if not a.source: p.error('--source required')
    if a.install and not a.check: p.error('--install requires --check')
    if a.split_threshold<1 or a.split_depth<1: p.error('invalid split limits')
    if min(a.seconds,a.max_states,a.seeds,a.timeout,a.max_rss_gib,a.jobs,a.check_limit)<=0 or any(w not in (128,256,512) for w in a.widths): p.error('invalid limits')
    source=a.source.resolve(); original=source.read_text(encoding='utf-8'); parse(original); synthesize()
    repo=a.repo.resolve(); out=a.out.resolve()
    if out.is_relative_to(repo): p.error('output must be outside repository')
    if a.install:
        if source!=repo/'lean/PEqualNP/Outside'/f'{STEM}.lean': p.error('install only into official skeleton path')
        if original.split(':=',1)[1].strip() not in ('by sorry','by\n  sorry'): p.error('install only into untouched sorry skeleton')
        rel=str(source.relative_to(repo)); tracked=subprocess.run(['git','ls-files','--',rel],cwd=repo,check=True,capture_output=True,text=True).stdout
        if tracked.strip(): p.error('refusing to overwrite tracked file')
    out=out/STEM/(time.strftime('%Y%m%d-%H%M%S')+'-'+str(time.time_ns()%1000000000).zfill(9));out.mkdir(parents=True)
    (out/'input.lean').write_text(original,encoding='utf-8')
    cap=len(GATES)-2; choices={}; results=[]
    for w in dict.fromkeys(a.widths):
        for seed in range(a.seeds):
            rows,words=pairs(w,seed); r,n,t=widthlib.screen(words,w,cap,a.seconds,a.max_states)
            print(f'[SCREEN] width={w} seed={seed} {r} states={n} wall={t:.3f}s',flush=True)
            results.append(dict(width=w,seed=seed,status=r,states=n,seconds=t))
            if r=='NO_RUN' and (w not in choices or n<choices[w][0]): choices[w]=(n,seed,rows,words)
    report=dict(stem=STEM,table=hex(T),gates=GATES,output=OUTPUT,trials=results,checks=[])
    rp=out/'results.json'; rp.write_text(json.dumps(report,indent=2)+'\n')
    if not choices: print('[NO CERTIFICATE] inconclusive, not a refutation',flush=True); return 2
    template=support.git_show(repo,support.REV,binary.TEMPLATE)
    for idx,(w,(n,seed,rows,words)) in enumerate(sorted(choices.items(),key=lambda it:(it[0]*it[1][0],it[0]))):
        d=out/f'width-{w}'; d.mkdir(); text=render(template,w,rows,words)
        assert text.count(DECL+' := by')==1
        candidate=d/(STEM+'.candidate.lean');candidate.write_text(text,encoding='utf-8');print('[CANDIDATE]',candidate,flush=True)
        if not a.check or idx>=a.check_limit: continue
        mode='direct'
        if n>=a.split_threshold:
            text,cert=render_split(text,STEM,a.split_depth,a.max_states,a.seconds)
            mode='split'
            print('[SPLIT]',json.dumps(dict(width=w,depth=a.split_depth,**cert)),flush=True)
            candidate.write_text(text,encoding='utf-8')
        r=guard.check(repo,STEM,text,d,a.timeout,a.max_rss_gib,1 if mode=='split' else a.jobs);report['checks'].append(dict(width=w,mode=mode,**r));rp.write_text(json.dumps(report,indent=2)+'\n')
        if not r['lean_ok']: continue
        verified=d/(STEM+'.verified.lean');verified.write_text(text,encoding='utf-8');print('[VERIFIED]',verified,flush=True)
        if a.install:
            if source.read_text(encoding='utf-8')!=original or subprocess.run(['git','ls-files','--',rel],cwd=repo,check=True,capture_output=True,text=True).stdout.strip(): raise ValueError('skeleton changed; refusing installation')
            source.write_text(text,encoding='utf-8');print('[INSTALLED]',source,flush=True)
        print('SOLVED LOCALLY (no submission)',flush=True);return 0
    return 1 if a.check else 0
if __name__=='__main__': raise SystemExit(main())
