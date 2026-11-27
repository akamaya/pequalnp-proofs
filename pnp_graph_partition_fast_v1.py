#!/usr/bin/env python3
"""Cached fixed-partition SAT; combine several exact OR counts per solve.

No persistent learned clauses or MDD. Each cube uses a fresh solver.
Base CNF is cached per worker, and the partition-specific constraints
are appended to a shallow copy (existing clause lists are immutable).
Range UNSAT covers all requested exact counts; TIMEOUT covers none.
Old fixed-strong UNSAT rows are imported only after fingerprint validation.
"""
import argparse
import concurrent.futures as cf
from collections import Counter, defaultdict
from contextlib import ExitStack
import copy
import functools
import hashlib
import json
import multiprocessing as mp
from pathlib import Path
import random
import sqlite3
import time
import fcntl

import pnp_graph_partition_fixed_bench_v1 as bench
import pnp_graph_partition_sweep_v2 as dbv2
import pnp_graph_partition_incremental_v1 as inc

sw=bench.sw
ROOT=Path(__file__).resolve().parent
OLD_FILES=sw.v19.DEPS+("pnp_sat_solve_v19.py","pnp_graph_partition_exact_v1.py",
    "pnp_graph_partition_sweep_v1.py","pnp_graph_partition_sweep_v2.py",
    "pnp_graph_partition_incremental_v1.py","pnp_graph_partition_fixed_bench_v1.py",
    "pnp_graph_partition_fixed_sweep_v1.py")

@functools.lru_cache(maxsize=8)
def template(n,edges,k,m,base,minimal):
    enc,_,_,_=sw.v19.build(n,list(edges),2*k+1+m,k,base,m,[],minimal,"compact")
    sides,jtruth=inc.singleton_sides(enc)
    inc.first_merge(enc,edges,sides)
    bearing=[enc.disj(s) for s in jtruth]
    hits=[]
    for u,v in edges:
        terms=[]
        for A,B in sides[:2]:
            terms.extend([enc.conj([A[u],B[v],-A[v],-B[u]]),
                          enc.conj([A[v],B[u],-A[u],-B[v]])])
        hits.append(enc.disj(terms))
    return enc,sides,jtruth,bearing,hits

def build(n,edges,k,counts,part,base=17,minimal=True):
    counts=tuple(sorted(set(counts)))
    m=counts[-1]
    orig,sides,jtruth,bearing,hits=template(n,tuple(edges),k,m,base,minimal)
    enc=copy.copy(orig)
    enc.cnf=orig.cnf[:]
    # Exact active suffix, or a union of allowed exact suffix lengths.
    if counts[0]:enc.add(enc.active[m-counts[0]])
    for r in range(counts[0],m):
        if r not in counts:
            # Forbid precisely r active slots.
            enc.add(enc.active[m-r-1],*([-enc.active[m-r]] if r else []))
    b=max(part)+1
    L=b+2
    slack=m-(n-b)
    if slack<0:raise ValueError("impossible partition")
    junk=[inc.onehot(enc,L) for _ in range(2)]
    for h,s in enumerate(jtruth):
        for v,z in enumerate(s):enc.add(-z,junk[h][part[v]])
    ors=[]
    for active,S in zip(enc.active,enc.support):
        P=[enc.fresh() for _ in range(L)]
        enc.add(-active,*P)
        enc.atmost(P,1)
        for z in P:enc.add(-z,active)
        ors.append(P)
        for v in range(n):enc.add(-S[v],P[part[v]])
        for h in range(2):
            for a in range(L):enc.add(-S[n+h],-P[a],junk[h][a])
    for a in range(b):
        attached=[enc.conj([junk[h][a],-bearing[h]]) for h in range(2)]
        enc.atmost([-P[a] for P in ors]+attached,m-(part.count(a)-1))
    for a in range(b,L):
        enc.add(-junk[0][a],-junk[1][a],*(P[a] for P in ors))
    # Same fixed-partition locality and clique cuts as the strong benchmark.
    # The support cap uses the largest allowed budget, a safe relaxation
    # for smaller exact counts. Every old exact model embeds in this CNF.
    different=[(u,v) for u in range(n) for v in range(u) if part[u]!=part[v]]
    blocks=[[v for v in range(n) if part[v]==a] for a in range(b)]
    for pair in enc.ands:
        for _,S in pair:
            for u,v in different:enc.add(-S[u],-S[v])
            for block in blocks:
                raw=[S[v] for v in block]
                if len(raw)+slack < len(raw)+2:
                    present=enc.disj(raw)
                    bench.conditional_atmost(enc,raw+S[n:],len(raw)+slack,present)
    for pair in sides:
        for S in pair:
            for u,v in different:enc.add(-S[u],-S[v])
    for C in bench.incompatible_cliques(edges,part,k):
        enc.atmost([-hits[e] for e in C],k)
    return enc

def direct(task):
    part,k,counts,name,seconds,chunk=task
    from pysat.solvers import Solver
    n,edges=sw.v1.CASES["l2260"]
    t=time.monotonic()
    enc=build(n,edges,k,counts,part)
    built=time.monotonic()
    with Solver(name=name,bootstrap_with=enc.cnf) as sol:
        loaded=time.monotonic()
        while True:
            sol.conf_budget(chunk)
            ans=sol.solve_limited()
            if ans is not None or time.monotonic()-built>=seconds:break
        out={"status":"TIMEOUT" if ans is None else "SAT" if ans else "UNSAT",
             "counts":list(counts),"assignment":list(part),
             "build_seconds":built-t,"load_seconds":loaded-built,
             "solve_seconds":time.monotonic()-loaded,"stats":sol.accum_stats()}
        if ans is True:
            w=enc.decode(sol.get_model())
            chk=sw.v4.check_star(n,enc.masks,w,17,True)
            ok=sw.v1.verify(n,enc.masks,w) and chk["valid"] and w["internal_or_gates"] in counts
            out.update(witness=w,structure_check=chk,verified_full_truth_table=ok)
            if not ok:out["status"]="MODEL_INVALID"
    out["elapsed"]=time.monotonic()-t
    return out

def self_test(name):
    from pysat.solvers import Solver
    bench.self_test(name)
    n,edges,k,base=3,[(0,1)],1,2
    # Check exact and range encodings against the previous strong CNF.
    sat=unsat=0
    for part in ((0,0,0),(0,0,1),(0,1,0),(0,1,1),(0,1,2)):
        exact={}
        for r in range(n-(max(part)+1),3):
            enc,_,_,_=sw.v19.build(n,edges,2*k+1+r,k,base,r,[],False,"compact")
            sw.ex.constrain_partition(enc,part)
            bench.strengthen(enc,edges,part)
            with Solver(name=name,bootstrap_with=enc.cnf) as s:exact[r]=s.solve()
        from itertools import combinations
        for z in range(1,len(exact)+1):
            for counts in combinations(exact,z):
                enc=build(n,edges,k,counts,part,base,False)
                with Solver(name=name,bootstrap_with=enc.cnf) as s:
                    got=s.solve()
                    assert got==any(exact[r] for r in counts),(part,counts,got,exact)
                    if got:
                        w=enc.decode(s.get_model())
                        assert w["internal_or_gates"] in counts
                        assert sw.v1.verify(n,enc.masks,w)
                        assert sw.v4.check_star(n,enc.masks,w,base,True)["valid"]
                        sat+=1
                    else:unsat+=1
    assert sat and unsat
    print("FAST FIXED RANGE SELF TEST OK",{"sat":sat,"unsat":unsat},flush=True)

def key(n,edges,k,r,parts,new=False):
    h=hashlib.sha256(json.dumps([n,edges,k,r,"fixed-strong",parts]).encode())
    for name in OLD_FILES+(("pnp_graph_partition_fast_v1.py",) if new else ()):
        h.update((ROOT/name).read_bytes())
    return h.hexdigest()

def import_old(db,path,expected,parts):
    if not path.exists():return 0
    old=sqlite3.connect(path.resolve().as_uri()+"?mode=ro",uri=True)
    try:
        if old.execute("SELECT fingerprint FROM meta WHERE id=1").fetchone()!=(expected,):
            raise ValueError("old fixed checkpoint fingerprint mismatch")
        states=dbv2.load(old,parts)
        if any(x in ("SAT","ERROR","MODEL_INVALID") for x in states.values()):
            raise ValueError("old checkpoint has a non-UNSAT/TIMEOUT result; inspect it")
        n=0
        with db:
            for idx,st,payload in old.execute("SELECT id,status,payload FROM results WHERE status='UNSAT'"):
                out=json.loads(payload)
                out["inherited_from_fixed_v1"]=True
                cur=db.execute("INSERT OR REPLACE INTO results VALUES(?,?,?)",
                    (idx,st,json.dumps(out,separators=(",",":"))))
                n+=cur.rowcount
        return n
    finally:old.close()

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--top-count",type=int,default=5)
    ap.add_argument("--or-min",type=int,default=8)
    ap.add_argument("--or-max",type=int,default=10)
    ap.add_argument("--jobs",type=int,default=8)
    ap.add_argument("--seconds",type=float,default=2)
    ap.add_argument("--wall-seconds",type=float,default=1800)
    ap.add_argument("--chunk",type=int,default=2000)
    ap.add_argument("--solver",default="cadical195")
    ap.add_argument("--benchmark",type=int,default=0,metavar="SAMPLES_PER_BLOCK")
    ap.add_argument("--self-test",action="store_true")
    a=ap.parse_args()
    if a.self_test:self_test(a.solver);return
    k,lo,hi=a.top_count,a.or_min,a.or_max
    if k<1 or not 0<=lo<=hi or 2*k+1+hi>21 or min(a.jobs,a.seconds,a.wall_seconds,a.chunk)<=0:
        ap.error("invalid limits")
    start=time.monotonic()
    n,edges=sw.v1.CASES["l2260"]
    allparts={}
    lookup=defaultdict(dict)
    for r in range(lo,hi+1):
        parts,generic=sw.candidates(n,edges,k,r)
        if (k,r) in dbv2.EXPECTED and (generic,len(parts))!=dbv2.EXPECTED[k,r]:
            raise ValueError("enumeration cross-check failed")
        allparts[r]=parts
        for idx,p in enumerate(parts,1):lookup[p][r]=idx
    print("[PARTITIONS]",json.dumps({"exact":{r:len(p) for r,p in allparts.items()},
        "union":len(lookup),"enumeration_seconds":time.monotonic()-start}),flush=True)
    ctx=mp.get_context("spawn")
    if a.benchmark:
        groups=defaultdict(list)
        for p in lookup:groups[max(p)+1].append(p)
        rng=random.Random(2260)
        sample=[p for g in sorted(groups) for p in rng.sample(groups[g],min(a.benchmark,len(groups[g])))]
        # Matched comparison, no checkpoint writes.
        reference={}
        for mode in ("old-exact","fast-exact","fast-range"):
            t=time.monotonic()
            rows=[]
            with cf.ProcessPoolExecutor(max_workers=a.jobs,mp_context=ctx) as pool:
                if mode=="old-exact":
                    futures={pool.submit(bench.run,(lookup[p][r],p,k,r,a.solver,a.seconds,"strong")):(p,(r,))
                        for p in sample for r in lookup[p]}
                else:
                    tasks=[(p,tuple(lookup[p])) for p in sample] if mode=="fast-range" else [
                        (p,(r,)) for p in sample for r in lookup[p]]
                    futures={pool.submit(direct,(p,k,rr,a.solver,a.seconds,a.chunk)):(p,rr) for p,rr in tasks}
                for f in cf.as_completed(futures):
                    p,rr=futures[f]
                    out=f.result()
                    st=out["status"]
                    if st not in ("UNSAT","TIMEOUT"):print("[TARGET]",mode,p,rr,json.dumps(out),flush=True)
                    if st in ("ERROR","MODEL_INVALID"):raise RuntimeError(out)
                    if mode=="old-exact":reference[p,rr[0]]=st
                    if st=="UNSAT" and any(reference.get((p,r))=="SAT" for r in rr):
                        raise RuntimeError("UNSAT disagrees with known SAT")
                    if st=="SAT" and reference.get((p,out["witness"]["internal_or_gates"]))=="UNSAT":
                        raise RuntimeError("SAT disagrees with reference")
                    rows.append((rr,out))
            wall=time.monotonic()-t
            done=sum(len(rr) for rr,out in rows if out["status"]=="UNSAT")
            print("[BENCH]",json.dumps({"mode":mode,"wall_seconds":round(wall,3),
                "calls":len(rows),"counts":dict(Counter(o["status"] for _,o in rows)),
                "exact_unsat":done,"exact_unsat_per_second":round(done/wall,3),
                "sum_build":round(sum(o.get("build_seconds",0) for _,o in rows),3),
                "sum_load":round(sum(o.get("load_seconds",0) for _,o in rows),3),
                "sum_solve":round(sum(o.get("solve_seconds",0) for _,o in rows),3)}),flush=True)
        return
    root=Path("sat-results");root.mkdir(exist_ok=True)
    with ExitStack() as stack:
        dbs={};states={}
        for r,parts in allparts.items():
            path=root/f"l2260-fast-strong-k{k}-r{r}.sqlite3"
            lock=stack.enter_context(open(str(path)+".lock","a"))
            fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
            db=dbv2.open_db(path,key(n,edges,k,r,parts,True));stack.callback(db.close)
            imported=import_old(db,root/f"l2260-fixed-strong-k{k}-r{r}.sqlite3",
                key(n,edges,k,r,parts),parts)
            dbs[r]=db;states[r]=dbv2.load(db,parts)
            print("[CHECKPOINT]",json.dumps({"r":r,"imported":imported,
                "unsat":sum(s=="UNSAT" for s in states[r].values()),"total":len(parts)}),flush=True)
        if any(s in ("SAT","ERROR","MODEL_INVALID") for ss in states.values() for s in ss.values()):
            raise ValueError("inspect previous SAT/error before resume")
        tasks=[]
        for p,ids in lookup.items():
            rr=tuple(r for r,idx in ids.items() if states[r].get(idx)!="UNSAT")
            if rr:tasks.append((p,rr))
        tasks.sort(key=lambda t:(all(lookup[t[0]][r] in states[r] for r in t[1]),t[0]))
        prior=sum(s=="UNSAT" for ss in states.values() for s in ss.values())
        unsat=prior;attempted=0;stop=False;new=Counter()
        print("[CONFIG]",json.dumps({"pending_cubes":len(tasks),
            "pending_exact":sum(len(rr) for _,rr in tasks),"prior_unsat":prior,
            "jobs":a.jobs,"seconds":a.seconds,"solver":a.solver}),flush=True)
        with cf.ProcessPoolExecutor(max_workers=a.jobs,mp_context=ctx) as pool:
            todo=iter(tasks);fs={}
            def fill():
                while len(fs)<a.jobs and time.monotonic()-start<a.wall_seconds:
                    task=next(todo,None)
                    if task is None:break
                    p,rr=task
                    fs[pool.submit(direct,(p,k,rr,a.solver,a.seconds,a.chunk))]=task
            fill();last=time.monotonic()
            while fs:
                done,_=cf.wait(fs,return_when=cf.FIRST_COMPLETED)
                for f in done:
                    p,rr=fs.pop(f)
                    try:out=f.result()
                    except Exception as e:out={"status":"ERROR","error":repr(e)}
                    st=out["status"]
                    attempted+=1;new[st]+=1
                    if st in ("UNSAT","TIMEOUT"):
                        if out.get("assignment")!=list(p) or out.get("counts")!=list(rr):
                            raise ValueError("worker result mismatch")
                        for r in rr:
                            idx=lookup[p][r]
                            dbv2.save(dbs[r],idx,{**out,"partition":idx,"exact_r":r})
                            states[r][idx]=st
                            if st=="UNSAT":unsat+=1
                    else:
                        stop=True
                        print("[TARGET]",json.dumps({"part":p,"counts":rr,**out}),flush=True)
                        # Do not mark any other exact count UNSAT on a SAT/error.
                        r=out.get("witness",{}).get("internal_or_gates",rr[0])
                        if r not in rr:r=rr[0]
                        idx=lookup[p][r]
                        dbv2.save(dbs[r],idx,{**out,"partition":idx,"assignment":list(p)})
                        states[r][idx]=st
                if not stop:fill()
                if time.monotonic()-last>=10 or stop:
                    print("[PROGRESS]",json.dumps({"attempted_cubes":attempted,
                        "unsat_exact":unsat,"new_unsat":unsat-prior,
                        "new_counts":dict(new),"elapsed":round(time.monotonic()-start,3)}),flush=True)
                    last=time.monotonic()
        rem={r:len(parts)-sum(s=="UNSAT" for s in states[r].values()) for r,parts in allparts.items()}
        print("[SUMMARY]",json.dumps({"status":"STOPPED" if stop else "UNRESOLVED" if any(rem.values()) else "ALL_PARTITIONS_UNSAT",
            "k":k,"remaining_by_r":rem,"new_counts":dict(new),"new_unsat":unsat-prior,
            "wall_seconds":round(time.monotonic()-start,3),"lean_verified":False}),flush=True)
        if stop:raise SystemExit(1)

if __name__=="__main__":main()
