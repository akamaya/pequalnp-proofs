#!/usr/bin/env python3
"""Experimental hybrid live-state DAG certificate with configurable Lean workers and profiling.
Lean independently checks every transition; Python is not trusted. No repo edits/submission.
Linux/WSL only for resource guarded check. No complement normalization in this version.
"""
import argparse, itertools, json, os, re, signal, subprocess, time
from pathlib import Path
import pnp_graph_binary_v3 as binary
import pnp_graph_support_v1 as support

DEFAULT = Path.home()/'dev/LeanDojo-v2/proof-logs'
MASK = (1<<512)-1
HALF = (1<<256)-1
GOAL = HALF<<256

def cuts(ws):
    c=0
    for w in ws: c |= ((w>>256)^w)&HALF
    return c

def children(k, ws):
    # Matches certChildren exactly, including enumeration order and duplicates.
    for i,j in itertools.combinations(range(len(ws)),2):
        a,b=ws[i],ws[j]; rest=ws[:i]+ws[i+1:j]+ws[j+1:]
        for z in (a&b,a|b,a&(MASK^b),b&(MASK^a)):
            if z in ws: continue
            for kept in (rest,(a,)+rest,(b,)+rest,(a,b)+rest):
                ch=(z,)+kept
                if len(ch)<=k+1 and cuts(ch)==HALF:
                    yield tuple(sorted(ch))

LEAN_HELPERS=r'''
-- Exact-state certificate helpers. The original live-search completeness
-- lemmas remain unchanged; no external search result is trusted by Lean.
def certInsert (a : W) : List W → List W
  | [] => [a]
  | b :: bs => if a.toNat ≤ b.toNat then a :: b :: bs else b :: certInsert a bs

theorem certInsert_set (a : W) (ws : List W) :
    (certInsert a ws).toFinset = insert a ws.toFinset := by
  induction ws with
  | nil => simp [certInsert]
  | cons b bs ih =>
    simp only [certInsert]
    split
    · simp
    · simp [ih, Finset.insert_comm]

def certSort : List W → List W
  | [] => []
  | a :: ws => certInsert a (certSort ws)

theorem certSort_set (ws : List W) : (certSort ws).toFinset = ws.toFinset := by
  induction ws with
  | nil => rfl
  | cons a ws ih => simp [certSort, certInsert_set, ih]

def certChildren (k : Nat) (ws : List W) : List (List W) :=
  (pairs ws).flatMap fun (a,b,r) =>
    ((ops a b).filter fun z => decide (z ∉ ws)).flatMap fun z =>
      ((keepChoices a b r).filter fun kept =>
        decide ((z :: kept).length ≤ k + 1) && (cuts (z :: kept) == -1)).map
          fun kept => certSort (z :: kept)

def CertDead (k : Nat) (ws : List W) : Prop :=
  ∀ g : W, (g = goal ∨ g = ~~~goal) → ¬ live basicOps g k ws.toFinset

theorem certNil (k : Nat) : ∀ c ∈ ([] : List (List W)), CertDead k c := by
  simp

theorem certCons {k : Nat} {w : List W} {ws : List (List W)}
    (h : CertDead k w) (hs : ∀ c ∈ ws, CertDead k c) :
    ∀ c ∈ w :: ws, CertDead k c := by
  intro c hc
  rcases List.mem_cons.mp hc with rfl | hc
  · exact h
  · exact hs c hc

theorem certLeaf (k : Nat) (ws : List W) (hn : ws.Nodup)
    (hsz : ws.length ≤ k + 1)
    (hfalse : optimized k (k + 1 - ws.length) ws = false) : CertDead k ws := by
  intro g hg h
  have htrue := optimized_complete hg k ws (k + 1 - ws.length) hn (by omega) h
  rw [hfalse] at htrue
  contradiction

theorem certNode (k : Nat) (ws : List W) (hn : ws.Nodup)
    (hgoal : ws ≠ [goal] ∧ ws ≠ [~~~goal])
    (hdead : ∀ c ∈ certChildren k ws, CertDead k c) : CertDead (k+1) ws := by
  intro g hg h
  rcases first_live h with done | ⟨a,ha,b,hb,hab,z,hz,hout,needed,hs,tail⟩
  · have e := singleton_list hn done
    rcases hg with rfl | rfl
    · exact hgoal.1 e
    · exact hgoal.2 e
  · obtain ⟨r,hm,hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
    have go {a b : W} (pairmem : (a,b,r) ∈ pairs ws)
        (perm : ws.Perm (a :: b :: r))
        (hset : ws.toFinset = insert a (insert b needed))
        (hop : z ∈ basicOps a b) : False := by
      obtain ⟨kept,hk,hnk,hfin⟩ := recover_kept perm hn hset
      have hznew : z ∉ kept := by
        intro hu
        apply hout
        rw [hset]
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
      have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew,hnk⟩
      have hl : live basicOps g k (z :: kept).toFinset := by
        simpa [hfin] using tail
      have hlen := live_card hl
      rw [List.toFinset_card_of_nodup hnd] at hlen
      have hkeep : kept.length ≤ k := by
        simp only [List.length_cons] at hlen
        omega
      have hcuts := cuts_full hg hl
      have hzout : z ∉ ws := fun hzmem => hout (List.mem_toFinset.mpr hzmem)
      have hc : certSort (z :: kept) ∈ certChildren k ws := by
        unfold certChildren
        apply List.mem_flatMap.mpr
        refine ⟨(a,b,r),pairmem,?_⟩
        apply List.mem_flatMap.mpr
        refine ⟨z,List.mem_filter.mpr ⟨List.mem_toFinset.mp hop,by simp [hzout]⟩,?_⟩
        apply List.mem_map.mpr
        exact ⟨kept,List.mem_filter.mpr ⟨hk,by simp [hkeep,hcuts]⟩,rfl⟩
      apply hdead _ hc g hg
      rw [certSort_set]
      exact hl
    rcases hm with direct | swap
    · exact go direct hp hs hz
    · exact go swap (hp.trans (.swap _ _ _)) (by rw [hs,Finset.insert_comm]) (ops_swap a b ▸ hz)

theorem certNoBuild {g : W} (hg : g = goal ∨ g = ~~~goal)
    (k : Nat) (inputs : List W)
    (hcover : inputs.sublists.all (fun ws => (cuts ws != -1) || (ws == inputs)) = true)
    (hdead : CertDead k inputs) (h : build basicOps g k inputs.toFinset) : False := by
  classical
  obtain ⟨s,hs,hl⟩ := compress h
  let ws := inputs.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hl' : live basicOps g k ws.toFinset := eq.symm ▸ hl
  have hm : ws ∈ inputs.sublists := List.mem_sublists.mpr (List.filter_sublist ..)
  have hh := List.all_eq_true.mp hcover ws hm
  have hc := cuts_full hg hl'
  have hw : ws = inputs := by simpa [hc] using hh
  exact hdead g hg (by simpa [hw] using hl')
'''

def certificate(roots,cap,split_depth,max_states,seconds):
    if len(set(roots))!=len(roots) or cuts(roots)!=HALF or len(roots)>cap+1:
        raise ValueError('invalid roots')
    if any(cuts(roots[:i]+roots[i+1:])==HALF for i in range(len(roots))):
        raise ValueError('root essentiality missing')
    start=time.monotonic(); nodes={}; visiting=set()
    def visit(k,ws,depth):
        key=(k,ws)
        if key in nodes:return
        if key in visiting: raise ValueError('cycle')
        if len(nodes)+len(visiting)>=max_states or time.monotonic()-start>seconds: raise ValueError('certificate resource limit')
        if ws in ((GOAL,),(MASK^GOAL,)): raise ValueError('reachable state; no certificate')
        if len(set(ws))!=len(ws) or len(ws)>k+1: raise ValueError('invalid child state')
        visiting.add(key)
        leaf=(k==0 or (split_depth>=0 and depth>=split_depth))
        ch=[] if leaf else [(k-1,c) for c in children(k-1,ws)]
        for ck,c in ch: visit(ck,c,depth+1)
        visiting.remove(key)
        nodes[key]=(leaf,ch)
    visit(cap,tuple(roots),0)
    return nodes,time.monotonic()-start

def render(text,stem,split_depth,max_states,seconds):
    rm=re.search(r'^def roots : List W := \[([^\n]*)\]$',text,re.M)
    nm=re.search(r'^theorem noSearch : search (\d+) roots = false := by\n  decide \+kernel\n',text,re.M)
    if not rm or not nm or 'abbrev W := BitVec 512' not in text: raise ValueError('expected original Binary v3 512-bit candidate')
    roots=tuple(int(s.strip(),0) for s in rm[1].split(',')); cap=int(nm[1]); nodes,wall=certificate(roots,cap,split_depth,max_states,seconds)
    # Nodes inserted in reverse topological order. Each proof cites only earlier nodes.
    ids={key:i for i,key in enumerate(nodes)}
    root=(cap,roots); parts=[LEAN_HELPERS]; transitions=0; leaves=0
    for key,(leaf,ch) in nodes.items():
        k,ws=key; i=ids[key]; n=f'certS{i}'; proof=f'certP{i}'
        words=', '.join(map(hex,ws))
        parts.append(f'\ndef {n} : List W := [{words}]\n')
        if leaf:
            leaves+=1
            parts.append(f'set_option maxHeartbeats 0 in\ntheorem {proof} : CertDead {k} {n} := by\n  exact certLeaf {k} {n} (by decide +kernel) (by decide +kernel) (by decide +kernel)\n')
        else:
            transitions+=len(ch)
            # Local computation establishes exact enumeration; omissions cannot pass.
            expected=', '.join('certS'+str(ids[c]) for c in ch)
            term=f'certNil {k-1}'
            for c in reversed(ch): term=f'certCons certP{ids[c]} ({term})'
            parts.append(f'set_option maxHeartbeats 0 in\ntheorem {proof} : CertDead {k} {n} := by\n  apply certNode {k-1} {n} (by decide +kernel) (by decide +kernel)\n  have hc : certChildren {k-1} {n} = [{expected}] := by decide +kernel\n  rw [hc]\n  exact {term}\n')
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
    if binary.parse_statement(stem,new)!=binary.parse_statement(stem,text): raise ValueError('statement changed')
    if re.search(r'\b(?:sorry|admit|axiom|native_decide)\b',new): raise ValueError('unsafe token')
    return new,dict(nodes=len(nodes),leaves=leaves,transitions=transitions,seconds=wall,cap=cap)

def group_rss(pgid):
    total=0; count=0
    for p in Path('/proc').iterdir():
        if not p.name.isdecimal():continue
        try:
            tail=(p/'stat').read_text().rsplit(')',1)[1].split()
            if int(tail[2])!=pgid or tail[0]=='Z':continue
            count+=1; total+=max(0,int(tail[21]))*os.sysconf('SC_PAGE_SIZE')
        except (OSError,ValueError,IndexError):continue
    return total,count

def terminate_group(p):
    # Popen was launched in a new session, so only our process group is targeted.
    try: os.killpg(p.pid,signal.SIGTERM)
    except ProcessLookupError:pass
    end=time.monotonic()+2
    while time.monotonic()<end:
        p.poll()
        if not group_rss(p.pid)[1]:break
        time.sleep(.1)
    try: os.killpg(p.pid,signal.SIGKILL)
    except ProcessLookupError:pass
    p.wait(timeout=10)
    end=time.monotonic()+5
    while time.monotonic()<end and group_rss(p.pid)[1]:time.sleep(.1)
    return group_rss(p.pid)[1]

def guarded_run(cmd,cwd,log,timeout,mem_gib,progress=True):
    t=time.monotonic(); peak=0; reason=''; next_report=15; remaining=0
    with open(log,'wb') as f:
        p=subprocess.Popen(cmd,cwd=cwd,stdout=f,stderr=subprocess.STDOUT,start_new_session=True)
        try:
            while True:
                rss,count=group_rss(p.pid); peak=max(peak,rss); elapsed=time.monotonic()-t
                rc=p.poll()
                if rc is not None:
                    if group_rss(p.pid)[1]: reason='LEFTOVER_CHILD'; remaining=terminate_group(p)
                    break
                if elapsed>=timeout:reason='TIMEOUT';break
                if mem_gib and rss>mem_gib*1024**3:reason='RSS_LIMIT';break
                if progress and elapsed>=next_report:
                    print(f'[RUN] {elapsed:.0f}s group RSS={rss/1024**3:.2f} GiB peak={peak/1024**3:.2f} GiB',flush=True);next_report=elapsed+15
                time.sleep(.3)
        finally:
            if p.poll() is None or group_rss(p.pid)[1]:remaining=terminate_group(p)
    return dict(returncode=p.returncode,reason=reason,seconds=round(time.monotonic()-t,3),peak_rss_gib=round(peak/1024**3,3),remaining=remaining)

def check(repo,stem,text,out,timeout,mem_gib,jobs=1,profile=False):
    name='PEqualNP.Outside.'+stem
    path=out/(stem+'.check.lean'); path.write_text(text+'\n#print axioms '+name+'\n',encoding='utf-8')
    log=out/(stem+'.check.log')
    cmd=['lake','env','lean','-j',str(jobs)]
    if profile: cmd += ['-Dtrace.profiler=true','-Dtrace.profiler.threshold=1000']
    print(f'[LEAN] jobs={jobs} profile={profile} log={log}',flush=True)
    r=guarded_run(cmd+[str(path)],repo/'lean',log,timeout,mem_gib)
    r.update(jobs=jobs,profile=profile)
    content=log.read_text(encoding='utf-8',errors='replace')
    ax=re.search(r"'"+re.escape(name)+r"' depends on axioms:\s*\[([^\]]*)\]",content)
    axioms={a.strip() for a in ax[1].split(',') if a.strip()} if ax else None
    ok=r['returncode']==0 and not r['reason'] and not r['remaining'] and axioms is not None and axioms<=support.ALLOWED
    r.update(lean_ok=ok,axioms=sorted(axioms) if axioms is not None else None)
    print('[CHECK]',stem,'PASS' if ok else 'FAIL',json.dumps(r),flush=True)
    if profile:
        # Elab.async times may overlap and include waiting on dependencies.
        spans=[]
        for m in re.finditer(r'\[Elab\.async\] \[([\d.]+)\] [^\n]*?elaborating proof of ([^\n]+)',content):
            spans.append((float(m[1]),m[2].strip()))
        for sec,decl in sorted(spans,reverse=True)[:12]:
            print(f'[PROFILE] {sec:.3f}s {decl}',flush=True)
        if not spans: print('[PROFILE] no completed spans above threshold',flush=True)
    if not ok:
        errors=[line for line in content.splitlines() if ': error:' in line]
        for line in errors[:12]:print(line,flush=True)
        print(content[-5000:],flush=True)
    return r

def self_test():
    import tempfile,sys
    for n,edges,cap in [(2,[(0,1)],0),(4,[(0,2),(0,3),(1,2),(1,3)],2),(7,[(0,3),(0,4),(1,3),(2,3),(4,6),(5,6)],6),(8,[(0,4),(0,5),(1,5),(1,6),(2,6),(1,7),(2,7),(3,7)],8)]:
        _,roots=binary.make_rows(n,edges)
        # A root with cap < n-1 is rejected before any tree proof; valid screening only.
        if cap+1<n:continue
        nodes,_=certificate(tuple(roots),cap,-1,100000,30)
        assert all(c in nodes for _,ch in nodes.values() for c in ch)
        print(f'[SELF TEST] n={n} states={len(nodes)} exact DAG PASS',flush=True)
    _,roots=binary.make_rows(8,[(0,4),(0,5),(1,5),(1,6),(2,6),(1,7),(2,7),(3,7)])
    for depth in (0,1,2):
        dag,_=certificate(tuple(roots),8,depth,100000,30)
        assert all(c in dag for _,ch in dag.values() for c in ch)
        assert any(leaf for leaf,_ in dag.values())
        print(f'[SELF TEST] hybrid depth={depth} nodes={len(dag)} leaves={sum(leaf for leaf,_ in dag.values())} PASS',flush=True)
    _,roots=binary.make_rows(4,[(0,2),(0,3),(1,2),(1,3)])
    try:certificate(tuple(roots),3,-1,100000,30)
    except ValueError as e:assert 'reachable' in str(e)
    else:raise AssertionError('reachable accepted')
    with tempfile.TemporaryDirectory() as d:
        # Child survives normal parent termination unless the entire group is killed.
        r=guarded_run([sys.executable,'-c','import subprocess,time; subprocess.Popen(["sleep","60"]); time.sleep(60)'],Path(d),Path(d)/'test.log',.6,1,False)
        assert r['reason']=='TIMEOUT' and r['remaining']==0,r
        print('[SELF TEST] timeout process group cleanup PASS',flush=True)
        r=guarded_run([sys.executable,'-c','print(123)'],Path(d),Path(d)/'ok.log',5,1,False)
        assert r['returncode']==0 and not r['reason'] and r['remaining']==0,r
        print('[SELF TEST] normal process exit PASS',flush=True)
        r=guarded_run([sys.executable,'-c','import time; x=bytearray(64*1024*1024); time.sleep(60)'],Path(d),Path(d)/'rss.log',5,.04,False)
        assert r['reason']=='RSS_LIMIT' and r['remaining']==0,r
        print('[SELF TEST] memory limit cleanup PASS',flush=True)
    print('SELF TEST OK (Python only; Lean helper not compiled here)',flush=True)

def main():
    p=argparse.ArgumentParser(description=__doc__); p.add_argument('--self-test',action='store_true');p.add_argument('--id',default='L_meta_11593');p.add_argument('--from-dir',type=Path,default=DEFAULT/'graph-binary-extra2');p.add_argument('--out',type=Path,default=DEFAULT/'graph-binary-certificate-v3');p.add_argument('--repo',type=Path,default=Path.home()/'dev/pequalnp-proofs');p.add_argument('--split-depth',type=int,default=1,help='-1: full DAG; 0: one original optimized leaf; >=1: hybrid certificate');p.add_argument('--timeout',type=float,default=300);p.add_argument('--max-rss-gib',type=float,default=20);p.add_argument('--max-states',type=int,default=100000);p.add_argument('--seconds',type=float,default=60);p.add_argument('--check',action='store_true');p.add_argument('--jobs',type=int,default=1,help='Lean worker threads');p.add_argument('--profile',action='store_true');a=p.parse_args()
    if a.self_test:self_test();return
    if not re.fullmatch(r'L_meta_\d+',a.id) or a.split_depth< -1 or min(a.timeout,a.max_rss_gib,a.max_states,a.seconds,a.jobs)<=0:p.error('invalid arguments')
    repo,src,out=(x.expanduser().resolve() for x in (a.repo,a.from_dir,a.out));out=out/f'{a.id}-depth{a.split_depth}-j{a.jobs}'
    if out.is_relative_to(repo) or out.is_relative_to(src):p.error('output must be separate from repo and source')
    text=(src/(a.id+'.candidate.lean')).read_text(encoding='utf-8'); out.mkdir(parents=True,exist_ok=True)
    new,r=render(text,a.id,a.split_depth,a.max_states,a.seconds)
    path=out/(a.id+'.candidate.lean');path.write_text(new,encoding='utf-8');print('[CERTIFICATE]',a.id,json.dumps(r),flush=True);print('[CANDIDATE]',path,flush=True)
    verified=out/(a.id+'.verified.lean')
    if a.check:
        if verified.exists():verified.unlink()
        r.update(check(repo,a.id,new,out,a.timeout,a.max_rss_gib,a.jobs,a.profile))
        if r['lean_ok']:verified.write_text(new,encoding='utf-8');print('[VERIFIED]',verified,flush=True)
    r.update(split_depth=a.split_depth,jobs=a.jobs,profile=a.profile)
    (out/'results.json').write_text(json.dumps(r,indent=2)+'\n',encoding='utf-8')
    if a.check and not r['lean_ok']:raise SystemExit(1)
if __name__=='__main__':main()
