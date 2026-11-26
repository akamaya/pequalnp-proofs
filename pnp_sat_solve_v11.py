#!/usr/bin/env python3
"""SAT v11: split v9 into exact internal OR counts, with resumable CPU search.

Each exact-count cube adds at most two unit clauses to v9's formula.
The active ORs form a suffix, so all counts 0..m are exhaustive.
UNSAT is experimental, not a formally verified Lean certificate.
"""
import argparse
import concurrent.futures as cf
import hashlib
import json
import multiprocessing as mp
import os
import time
from pathlib import Path

import pnp_sat_solve_v1 as v1
import pnp_sat_solve_v4 as v4
import pnp_sat_solve_v9 as v9


ROOT=Path(__file__).resolve().parent
FILES=("pnp_sat_solve_v1.py","pnp_sat_solve_v2.py","pnp_sat_solve_v4.py","pnp_sat_solve_v9.py")
CACHE={}


def digest(obj,files):
    h=hashlib.sha256(json.dumps(obj).encode())
    for name in files:h.update((ROOT/name).read_bytes())
    return h.hexdigest()


def exact_units(active,r):
    m=len(active)
    if not 0<=r<=m:raise ValueError("invalid active OR count")
    units=[]
    if r:units.append(active[m-r])
    if r<m:units.append(-active[m-r-1])
    return units


def run(task):
    n,edges,total,k,r,base,solver,seconds,chunk=task
    import copy
    start=time.monotonic()
    key=(n,tuple(map(tuple,edges)),total,k,base)
    if key not in CACHE:
        # Bound per-process memory: retain only the latest base formula.
        CACHE.clear()
        CACHE[key]=v9.Encoding(n,edges,total,k,base).build()
    base_enc=CACHE[key]
    enc=copy.copy(base_enc)
    units=exact_units(enc.active,r)
    enc.cnf=base_enc.cnf+[[x] for x in units]
    meta={"top_count":k,"internal_or_count":r,"variables":enc.max_var,
          "clauses":len(enc.cnf),"build_seconds":round(time.monotonic()-start,3),
          "solver":solver,"seconds_per_cube":seconds}
    res=v4.solve(enc,"full",base,solver,seconds,chunk)
    if res["status"]=="SAT" and res["witness"]["internal_or_gates"]!=r:
        res.update(status="MODEL_INVALID",error="incorrect active OR count")
    return {**meta,**res}


def self_test(solver,seconds,chunk):
    from pysat.solvers import Solver
    # Verify partition disjointness and completeness for every suffix.
    for m in range(19):
        active=list(range(1,m+1))
        for count in range(m+1):
            pos=set(active[m-count:])
            matched=[r for r in range(m+1) if all(
                (x in pos) if x>0 else (-x not in pos)
                for x in exact_units(active,r))]
            assert matched==[count],(m,count,matched)
    # Force v9's known boundary witness, then test all exact counts.
    enc=v9.Encoding(3,[(0,1)],5,1,2).build()
    ass=[]
    for pairs,choices in ((enc.ors,[(0,1),(5,3)]),
                          (enc.ands,[(1,2),(1,6),(0,4)])):
        for pair,(a,b) in zip(pairs,choices):
            for (sels,_),src in zip(pair,sorted((a,b))):ass.append(sels[src])
    with Solver(name=solver,bootstrap_with=enc.cnf) as sol:
        for r in range(3):
            assert sol.solve(assumptions=ass+exact_units(enc.active,r))==(r==2)
            if r==2:
                w=enc.decode(sol.get_model())
                assert v1.verify(3,enc.masks,w)
                assert v4.check_star(3,enc.masks,w,2,True)["valid"]
    # Actual subprocess tests include the independent decoded witness check.
    for total,r,expected in ((3,0,"UNSAT"),(5,2,"SAT")):
        got=run((3,[(0,1)],total,1,r,0,solver,seconds,chunk))
        print("[TEST]",json.dumps(got),flush=True)
        assert got["status"]==expected,got
    print("SAT V11 SELF TEST OK",flush=True)


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--case",choices=v1.CASES,default="l2260")
    ap.add_argument("--gates",type=int,default=21)
    ap.add_argument("--jobs",type=int,default=4)
    ap.add_argument("--seconds",type=float,default=5)
    ap.add_argument("--chunk",type=int,default=20000)
    ap.add_argument("--solver",choices=("g4","cadical195"),default="cadical195")
    ap.add_argument("--seed-v9",type=Path)
    ap.add_argument("--checkpoint",type=Path)
    ap.add_argument("--top-count",type=int)
    ap.add_argument("--self-test",action="store_true")
    a=ap.parse_args()
    if a.gates<3 or a.jobs<1 or a.seconds<=0 or a.chunk<1:ap.error("invalid limits")
    if a.self_test:self_test(a.solver,a.seconds,a.chunk);return
    n,edges=v1.CASES[a.case]
    base=17 if a.case=="l2260" else 0
    full_counts=list(range((a.gates-1)//2,0,-1))
    counts=full_counts[:]
    if a.top_count is not None:
        if a.top_count not in counts:ap.error("invalid top count")
        counts=[a.top_count]
    key=digest([n,edges,a.gates,base,counts,"exact"],FILES+("pnp_sat_solve_v11.py",))
    manifest={str(k):list(range(a.gates-2*k)) for k in counts}
    path=a.checkpoint

    def execute():
        start=time.monotonic()
        data={"fingerprint":key,"manifest":manifest,"inherited":{},"results":{}}
        if path and path.exists():
            data=json.loads(path.read_text())
            if data.get("fingerprint")!=key or data.get("manifest")!=manifest:
                raise ValueError("checkpoint mismatch")
        results=data["results"]
        inherited=data["inherited"]
        if a.seed_v9:
            old=json.loads(a.seed_v9.read_text())
            if old.get("fingerprint")!=digest([n,edges,a.gates,base,full_counts],FILES):
                raise ValueError("v9 seed fingerprint mismatch")
            for k in counts:
                prev=old.get("results",{}).get(str(k),{})
                if prev.get("status")=="UNSAT":inherited[str(k)]=prev
        def save():
            if path:
                tmp=path.with_name(path.name+".tmp")
                tmp.write_text(json.dumps(data,indent=2)+"\n")
                os.replace(tmp,path)
        def name(k,r):return f"{k}:{r}"
        def status(k,r):
            if str(k) in inherited:return "UNSAT"
            return results.get(name(k,r),{}).get("status","PENDING")
        all_pairs=[(k,r) for k in counts for r in manifest[str(k)]]
        # Round-robin by OR count; small circuits first for each k.
        pending=sorted([(k,r) for k,r in all_pairs if status(k,r)!="UNSAT"],
                       key=lambda p:(p[1],-p[0]))
        print("[CONFIG]",json.dumps({"top_counts":counts,"inherited_unsat":sorted(map(int,inherited)),
              "pending_cubes":len(pending),"jobs":a.jobs,"seconds":a.seconds,
              "solver":a.solver}),flush=True)
        save()
        if pending and not any(x.get("status")=="SAT" for x in results.values()):
            with cf.ProcessPoolExecutor(max_workers=a.jobs,mp_context=mp.get_context("fork")) as pool:
                todo=iter(pending)
                active={}
                def fill():
                    while len(active)<a.jobs:
                        pair=next(todo,None)
                        if pair is None:break
                        k,r=pair
                        active[pool.submit(run,(n,edges,a.gates,k,r,base,a.solver,a.seconds,a.chunk))]=pair
                fill()
                stop=False
                while active:
                    done,_=cf.wait(active,return_when=cf.FIRST_COMPLETED)
                    for f in done:
                        k,r=active.pop(f)
                        try:res=f.result()
                        except Exception as e:res={"status":"ERROR","error":repr(e)}
                        results[name(k,r)]=res
                        save()
                        print("[OR CUBE]",k,r,json.dumps(res),flush=True)
                        if res["status"] in ("SAT","ERROR","MODEL_INVALID"):stop=True
                    if not stop:fill()
        total_stats={}
        top_stats={}
        for k in counts:
            hist={}
            for r in manifest[str(k)]:
                s=status(k,r)
                hist[s]=hist.get(s,0)+1
                total_stats[s]=total_stats.get(s,0)+1
            state=("ERROR" if hist.get("ERROR") or hist.get("MODEL_INVALID") else
                   "SAT" if hist.get("SAT") else "UNSAT" if hist.get("UNSAT")==len(manifest[str(k)]) else "UNRESOLVED")
            top_stats[str(k)]={"status":state,"counts":hist,
                              "inherited":str(k) in inherited}
        states=[v["status"] for v in top_stats.values()]
        overall=("ERROR" if "ERROR" in states else "SAT" if "SAT" in states else
                 "UNSAT" if all(s=="UNSAT" for s in states) else "UNRESOLVED")
        print("[SUMMARY]",json.dumps({"status":overall,"top_cases":top_stats,"cube_counts":total_stats,
            "wall_seconds":round(time.monotonic()-start,3)}),flush=True)
        if overall=="ERROR":raise SystemExit(1)

    if path:
        import fcntl
        path.parent.mkdir(parents=True,exist_ok=True)
        with open(str(path)+".lock","a") as lock:
            fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
            execute()
    else:execute()


if __name__=="__main__":main()
