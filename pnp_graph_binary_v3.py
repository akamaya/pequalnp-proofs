#!/usr/bin/env python3
"""Pilot: signed live-state lower bounds, independent Lean check, historical or new positive graph tasks.
Reads generic helper blocks from pinned L_meta_10462; never edits repo or submits.
Python screen is advisory. Lean checks the actual finite search and full theorem.
"""
import argparse, itertools, json, random, re, time
from functools import lru_cache
from pathlib import Path
import pnp_graph_support_v1 as support

TEMPLATE = 'L_meta_10462'
DEFAULT = Path.home()/'dev/LeanDojo-v2/proof-logs'
HALF = (1<<256)-1
MASK = (1<<512)-1
TARGET = HALF<<256


def make_rows(n, edges):
    pos = [x for x in range(1<<n) if any(x>>a&1 and x>>b&1 for a,b in edges)]
    pos_set=set(pos)
    neg = [x for x in range(1<<n) if x not in pos_set]
    if not pos or not neg: raise ValueError('constant graph')
    # Explicit essential-variable pairs first, so omitting any input is rejected.
    pairs = []
    for i in range(n):
        j = next(b if a==i else a for a,b in edges if i in (a,b))
        pairs.append((1<<j, (1<<j)|(1<<i)))
    # Cover every input row at least once, plus a deterministic spread of pairs.
    pairs.extend((neg[i%len(neg)],pos[i%len(pos)]) for i in range(max(len(pos),len(neg))))
    rng=random.Random(10462)
    while len(pairs)<256: pairs.append((rng.choice(neg),rng.choice(pos)))
    if len(pairs)>256: raise ValueError('too many rows')
    rows=[a for a,b in pairs]+[b for a,b in pairs]
    words=[sum(((r>>i)&1)<<j for j,r in enumerate(rows)) for i in range(n)]
    assert len(rows)==512 and len(set(words))==n
    assert all(any(r>>a&1 and r>>b&1 for a,b in edges)==(i>=256) for i,r in enumerate(rows))
    return rows,words


def norm(w): return min(w,MASK^w)
def sep(w): return ((w>>256)^w)&HALF


def screen(words, cap, seconds, max_states):
    """Complement-canonical live search with pair separation. NOT is free.
    False means no live run found by the relaxed exhaustive numerical model;
    only the independently checked Lean theorem is authoritative.
    """
    start=time.monotonic(); states=0
    target=norm(TARGET)
    roots=tuple(sorted({norm(w) for w in words}))
    def cover(ws):
        c=0
        for w in ws: c|=sep(w)
        return c==HALF
    class Limit(Exception): pass
    @lru_cache(maxsize=None)
    def dfs(ws,k):
        nonlocal states
        states+=1
        if states>max_states or time.monotonic()-start>seconds: raise Limit
        if ws==(target,): return True
        if k==0 or len(ws)>k+1 or len(ws)<2: return False
        for i,a in enumerate(ws):
            for j in range(i+1,len(ws)):
                b=ws[j]; rest=ws[:i]+ws[i+1:j]+ws[j+1:]
                for z in {norm(a&b),norm(a|b),norm(a&(MASK^b)),norm(b&(MASK^a))}:
                    if z==0 or z in ws: continue
                    for keep in ((),(a,),(b,),(a,b)):
                        child=tuple(sorted(rest+keep+(z,)))
                        if len(child)<=k and cover(child) and dfs(child,k-1): return True
        return False
    try:
        # Essential-variable pairs ensure only the full root set can separate all pairs.
        for i in range(len(roots)):
            if cover(roots[:i]+roots[i+1:]): raise ValueError('essential pair coverage missing')
        r=dfs(roots,cap) if cover(roots) else False
        result='REACHABLE' if r else 'NO_RUN'
    except Limit: result='UNKNOWN'
    return result, states, time.monotonic()-start


def block(text, a, b):
    if text.count(a)!=1 or text.count(b)!=1: raise ValueError('unexpected template marker: '+a+' / '+b)
    return text[text.index(a):text.index(b)]


def helpers(template,stem,ref):
    # All copied blocks are general helper lemmas; none refers to the historical final theorem.
    first=template.split('\ndef ins_fffefee8 :',1)[0]
    if 'theorem search_complete' not in first or 'theorem gate_reach' not in first: raise ValueError('bad template')
    second=block(template,'\ndef SignedBuild (','\ntheorem mem_ops_reach ')
    third=block(template,'\ndef bitlu (','\ntheorem septInit ')
    out=first+'\n'+second+'\ndef cible : W := goal\n'+third
    old='PEqualNP.Outside.'+TEMPLATE
    if out.count(old)!=1: raise ValueError('unexpected namespace references')
    out=out.replace(old,'PEqualNP.Outside.'+stem)
    if re.search(r'\b(?:sorry|admit|axiom|native_decide)\b',out): raise ValueError('unsafe template token')
    return '-- Generic signed live-search helpers adapted from '+support.BASE+TEMPLATE+'.lean at '+ref+'\n-- Source: https://github.com/open-goat/pequalnp-proofs\nimport Mathlib\n'+out+'\n'


def parse_statement(stem, source):
    # Historical declarations can end in `:= someProof` rather than `:= by`.
    # Only accept the literal graph-statement format already checked by support.
    name = 'PEqualNP.Outside.' + stem
    m = re.search(r'^theorem\s+' + re.escape(name) + r'\s*:', source, re.M)
    if not m:
        raise ValueError('main theorem not found')
    end = source.find(':=', m.end())
    if end < 0:
        raise ValueError('main theorem assignment marker not found')
    decl = source[m.start():end].rstrip()
    # The original proof is irrelevant: use only its exact declaration.
    return support.parse(stem, decl + ' := by\n  sorry\n')


def render(stem,source,template,ref,gates,output,rows,words):
    decl,n,edges,rhs=parse_statement(stem,source)
    m=len(gates); cap=m-2
    if cap<0: raise ValueError('invalid cap')
    data=', '.join(map(str,rows)); roots=', '.join(hex(w) for w in words)
    witness=', '.join(f'⟨.{op}, [{a}, {b}]⟩' for op,a,b in gates)
    ns='PEqualNP.Outside.'+stem
    # Graph statement is preserved byte-for-byte by support.parse.
    # `sample` uses only concrete assignments and `search` enumerates all live runs.
    return helpers(template,stem,ref)+f'''
def rows : List Nat := [{data}]
def sample (k : Fin 512) (i : Fin {n}) : Bool := (rows.getD k.val 0).testBit i.val
def roots : List W := [{roots}]
def posted (x : Fin {n} → Bool) : Bool := {rhs}
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem rootBits : ∀ k : Fin 512, roots.map (bitlu k) = List.ofFn (sample k) := by
  decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem rowSpec : ∀ k : Fin 512, posted (sample k) = bitlu k cible := by
  decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem noSearch : search {cap} roots = false := by
  decide +kernel

theorem binaryBound (gs : List Gate) (o : Nat) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin {n} → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = posted x) : {m-1} ≤ binaryCost gs := by
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
theorem monoCorrect : ∀ x : Fin {n} → Bool, Circuit.eval ⟨monoWitness,{output}⟩ (List.ofFn x) = posted x := by
  decide +kernel
end {ns}
open {ns} PEqualNP.CircuitLowerBounds in
{decl} := by
  intro gs o legalG _oneNot correct
  by_cases hn : ∃ g ∈ gs, g.op = GateOp.not
  · obtain ⟨g,hg,hop⟩ := hn
    have lb := binaryBound gs o legalG correct
    have strict : binaryCost gs < gs.length := (List.length_filter_lt_length_iff_exists (p := isBinary)).mpr ⟨g,hg,by simp [isBinary,hop]⟩
    have hw : monoWitness.length = {m} := rfl
    exact ⟨monoWitness,{output},monoShape,by omega,monoCorrect⟩
  · refine ⟨gs,o,?_,le_rfl,correct⟩
    intro g hg
    refine ⟨?_, (legalG g hg).2⟩
    rcases (legalG g hg).1 with h|h|h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd ⟨g,hg,h⟩ hn
'''


def self_test():
    # K_2,2 has a three-gate monotone circuit, no two-gate signed run.
    for n,edges,cap,expected in [(2,[(0,1)],0,'NO_RUN'),(2,[(0,1)],1,'REACHABLE'),(4,[(0,2),(0,3),(1,2),(1,3)],2,'NO_RUN'),(4,[(0,2),(0,3),(1,2),(1,3)],3,'REACHABLE'),(7,[(0,3),(0,4),(1,3),(2,3),(4,6),(5,6)],6,'NO_RUN'),(8,[(0,4),(1,2),(1,7),(2,5),(3,6),(5,6)],7,'NO_RUN')]:
        rows,words=make_rows(n,edges); r,st,t=screen(words,cap,10,100000); assert r==expected,(r,expected)
        print(f'[SELF TEST] n={n} cap={cap} {r} states={st} PASS',flush=True)
    stem='L_meta_123'
    rhs='decide (∃ i < ([0, 1] : List ℕ).length / 2, (List.ofFn x).getD (([0, 1] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 1] : List ℕ).getD (2 * i + 1) 0) false = true)'
    decl=f"theorem PEqualNP.Outside.{stem} : ∀ (gates : List Nat), (∀ x : Fin 2 → Bool, true = {rhs}) → ∃ gates' : List Nat, gates'.length ≤ gates.length ∧ ∀ x : Fin 2 → Bool, true = {rhs}"
    for proof in (' := by\n  exact h',' := h',' :=\n  someProof arg',' := by\n  exact (by trivial)'):
        assert parse_statement(stem,decl+proof)==(decl,2,[(0,1)],rhs)
    print('[SELF TEST] tactic and direct-term declaration extraction PASS')
    for bad in (decl,decl.replace('∀ (gates','¬ ∀ (gates')+' := h'):
        try: parse_statement(stem,bad)
        except ValueError: pass
        else: raise AssertionError('invalid declaration accepted')
    print('[SELF TEST] unsupported declaration rejected PASS')
    print('SELF TEST OK')



def raise_limits(text, depth):
    """Keep proof and statement intact; change only verification resource limits."""
    imports=list(re.finditer(r'^import[ \t]+[^\n]+$',text,re.M))
    if not imports:
        raise ValueError('no import header')
    at=imports[-1].end()
    # Set the default for declarations without a scoped override; retain smaller
    # explicitly scoped helper limits that have already passed in the real run.
    text=text[:at]+f'\n\nset_option maxRecDepth {depth}\nset_option exponentiation.threshold 1024\n'+text[at:]
    text=text.replace('set_option maxRecDepth 32000 in',f'set_option maxRecDepth {depth} in')
    return text


def error_context(stem, candidate, out):
    logpath=out/(stem+'.check.log')
    if not logpath.is_file(): return
    log=logpath.read_text(encoding='utf-8')
    lines=candidate.splitlines()
    for m in list(re.finditer(r'Proof\.lean:(\d+):(\d+): error[^\n]*',log))[:5]:
        line=int(m.group(1)); print('[ERROR LOCATION]',m.group(0),flush=True)
        for i in range(max(1,line-3), min(len(lines),line+3)+1):
            print(f'{i:5d} {lines[i-1][:240]}',flush=True)


def retry_saved(a, repo, out):
    src=a.retry_from.expanduser().resolve()
    if src==out or not src.is_dir(): raise ValueError('retry source must be a different existing directory')
    # Follow the original screening order, including unchecked candidates.
    records=json.loads((src/'results.json').read_text(encoding='utf-8'))
    names=[r['stem'] for r in records if r.get('result')=='NO_RUN' and (src/(r['stem']+'.candidate.lean')).is_file()]
    names=names[:a.check_count]
    if not names: raise ValueError('no saved NO_RUN candidates selected')
    results=[]
    for stem in names:
        if not re.fullmatch(r'L_meta_\d+',stem): raise ValueError('invalid target')
        candidate=raise_limits((src/(stem+'.candidate.lean')).read_text(encoding='utf-8'),a.rec_depth)
        file=out/(stem+'.candidate.lean'); file.write_text(candidate,encoding='utf-8')
        print(f'[RETRY] {stem} depth={a.rec_depth} exponentiation.threshold=1024',flush=True)
        start=time.monotonic()
        ok=support.check(repo,stem,candidate,out,a.timeout)
        if ok:
            file=out/(stem+'.verified.lean'); file.write_text(candidate,encoding='utf-8'); print('[VERIFIED]',file,flush=True)
        else: error_context(stem,candidate,out)
        results.append({'stem':stem,'lean_ok':ok,'seconds':round(time.monotonic()-start,3)})
        (out/'retry-results.json').write_text(json.dumps(results,indent=2)+'\n',encoding='utf-8')
    print(f'[RETRY SUMMARY] Lean={sum(r["lean_ok"] for r in results)}/{len(results)} (no submission)',flush=True)
    if not all(r['lean_ok'] for r in results): raise SystemExit(1)


def main():
    p=argparse.ArgumentParser(); p.add_argument('--repo',type=Path,default=Path.home()/'dev/pequalnp-proofs'); p.add_argument('--ref',default=support.REV); p.add_argument('--batch',type=Path,default=DEFAULT/'graph-support-batch-v1/batch.json'); p.add_argument('--audit',type=Path,default=DEFAULT/'graph_proof_audit.json'); p.add_argument('--out',type=Path,default=DEFAULT/'graph-binary-v3'); p.add_argument('--source',type=Path); p.add_argument('--self-test',action='store_true'); p.add_argument('--limit',type=int,default=5); p.add_argument('--seconds',type=float,default=10); p.add_argument('--max-states',type=int,default=500000); p.add_argument('--max-extra',type=int,default=1); p.add_argument('--check-count',type=int,default=2); p.add_argument('--timeout',type=int,default=180); p.add_argument('--retry-from',type=Path); p.add_argument('--rec-depth',type=int,default=60000); a=p.parse_args()
    if a.self_test:
        self_test()
        sample='import Mathlib\nimport PEqualNP.Defs\nnamespace Test\nset_option maxRecDepth 32000 in\ntheorem t : True := by trivial\nend Test\n'
        changed=raise_limits(sample,60000)
        assert 'set_option maxRecDepth 60000 in' in changed and 'set_option exponentiation.threshold 1024' in changed and 'theorem t : True := by trivial' in changed
        assert changed.index('import PEqualNP.Defs')<changed.index('set_option maxRecDepth 60000')<changed.index('namespace Test')
        print('[SELF TEST] verification limits PASS')
        return
    repo=a.repo.expanduser().resolve(); out=a.out.expanduser().resolve(); out.mkdir(parents=True,exist_ok=True)
    if out.is_relative_to(repo): p.error('output must be outside repository')
    if min(a.limit,a.seconds,a.max_states,a.timeout)<1 or a.check_count<0 or a.max_extra<1: p.error('invalid limit')
    if not 32000 <= a.rec_depth <= 65000: p.error('--rec-depth must be between 32000 and 65000')
    if a.retry_from: retry_saved(a,repo,out); return
    ref=support.subprocess.check_output(['git','-C',str(repo),'rev-parse','--verify',a.ref+'^{commit}'],text=True).strip()
    template=support.git_show(repo,ref,TEMPLATE)
    # Fail early if a global template mismatch would affect every candidate.
    helpers(template,'L_meta_999999999',ref)
    if a.source:
        tasks=[(a.source.stem,a.source.read_text(encoding='utf-8'))]
    else:
        audit=json.loads(a.audit.read_text(encoding='utf-8'))
        # Only known positive graph statements. Batch gate counts are used to prioritize.
        batch=json.loads(a.batch.read_text(encoding='utf-8'))
        if audit.get('revision') != ref or batch.get('revision') != ref:
            p.error('audit/batch revision does not match --ref')
        records=audit['records']; eligible={}
        def visit(obj):
            if isinstance(obj,list):
                for v in obj: visit(v)
            elif isinstance(obj,dict):
                stem=obj.get('stem') or obj.get('id') or obj.get('name') or obj.get('path')
                if isinstance(stem,str):
                    stem=Path(stem).stem; n=obj.get('n'); g=obj.get('gates',obj.get('gate_count'))
                    if isinstance(g,int) and isinstance(n,int): eligible[stem]=(g,n)
                for v in obj.values():
                    if isinstance(v,(dict,list)): visit(v)
        visit(batch)
        selected=[r for r in records if r.get('polarity')=='positive' and r.get('n') in (7,8) and r.get('edges')]
        def priority(r):
            s=Path(r['path']).stem; val=eligible.get(s)
            return (val is None, abs(val[0]-val[1]-1) if val else 100, r['lines'],s)
        selected.sort(key=priority)
        if eligible:
            selected=[r for r in selected if (v:=eligible.get(Path(r['path']).stem)) and v[1]<v[0]<=v[1]+a.max_extra]
        print(f'[POOL] {len(selected)} historical candidates in pilot range',flush=True)
        tasks=((Path(r['path']).stem,None) for r in selected)
    results=[]; attempted=checked=passed=skipped=errors=0
    def save():
        path=out/'results.json'; tmp=path.with_suffix('.json.tmp')
        tmp.write_text(json.dumps(results,indent=2,ensure_ascii=False)+'\n',encoding='utf-8'); tmp.replace(path)
    for stem,source in tasks:
        try:
            if not re.fullmatch(r'L_meta_\d+',stem): raise ValueError('invalid target')
            if source is None: source=support.git_show(repo,ref,stem)
            _,n,edges,_=parse_statement(stem,source)
            gates,output=support.synth(n,edges); m=len(gates)
            if not n<m<=n+a.max_extra:
                raise ValueError(f'outside pilot range: mono={m}, n={n}')
            rows,words=make_rows(n,edges)
        except (ValueError, OSError, support.subprocess.CalledProcessError) as exc:
            skipped+=1
            print(f'[SKIP] {stem}: {exc}',flush=True)
            results.append({'stem':stem,'result':'SKIPPED','error':str(exc)}); save()
            continue
        attempted+=1
        try:
            result,states,sec=screen(words,m-2,a.seconds,a.max_states)
            print(f'[SCREEN] {stem} n={n} mono={m} cap={m-2} {result} states={states} wall={sec:.3f}s',flush=True)
            rec={'stem':stem,'n':n,'gates':m,'cap':m-2,'result':result,'states':states,'seconds':sec}; results.append(rec)
            if result=='NO_RUN':
                try:
                    candidate=raise_limits(render(stem,source,template,ref,gates,output,rows,words),a.rec_depth)
                    file=out/(stem+'.candidate.lean'); file.write_text(candidate,encoding='utf-8'); print('[CANDIDATE]',file,flush=True)
                    if checked<a.check_count:
                        checked+=1; ok=support.check(repo,stem,candidate,out,a.timeout); rec['lean_ok']=ok
                        if not ok: error_context(stem,candidate,out)
                        if ok:
                            passed+=1; file=out/(stem+'.verified.lean'); file.write_text(candidate,encoding='utf-8'); print('[VERIFIED]',file,flush=True)
                except (ValueError, OSError, support.subprocess.CalledProcessError) as exc:
                    errors+=1; rec['error']=str(exc); print(f'[GENERATION ERROR] {stem}: {exc}',flush=True)
        except (ValueError, OSError, support.subprocess.CalledProcessError) as exc:
            errors+=1; results.append({'stem':stem,'result':'ERROR','error':str(exc)}); print(f'[SCREEN ERROR] {stem}: {exc}',flush=True)
        save()
        if attempted>=a.limit: break
    save()
    print(f'[SUMMARY] screened={attempted} skipped={skipped} errors={errors} no_run={sum(r["result"]=="NO_RUN" for r in results)} Lean={passed}/{checked} (no submission)',flush=True)
    print('[JSON]',out/'results.json',flush=True)
    if not attempted or errors or passed!=checked: raise SystemExit(1)

if __name__=='__main__': main()
