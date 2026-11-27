#!/usr/bin/env python3
"""Full fixed-partition sweep using the benchmarked strong encoding.

Uses the exact same run() as fixed_bench_v1. Separate SQLite checkpoint.
An optional wall budget stops dispatching new work; in-flight bounded
solves finish and are committed. No incomplete result is an exclusion.
"""
import argparse
import concurrent.futures as cf
from collections import Counter
import hashlib
import json
import multiprocessing as mp
from pathlib import Path
import time
import fcntl

import pnp_graph_partition_fixed_bench_v1 as bench
import pnp_graph_partition_sweep_v2 as dbv2

sw=bench.sw

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--top-count",type=int,default=5)
    ap.add_argument("--or-count",type=int,default=8)
    ap.add_argument("--seconds",type=float,default=2)
    ap.add_argument("--jobs",type=int,default=8)
    ap.add_argument("--solver",default="cadical195")
    ap.add_argument("--wall-seconds",type=float,default=1800,
                    help="dispatch deadline; active jobs finish before exit")
    ap.add_argument("--checkpoint",type=Path)
    ap.add_argument("--self-test",action="store_true")
    a=ap.parse_args()
    if a.self_test:
        bench.self_test(a.solver)
        dbv2.self_test(a.solver)
        return
    k,r=a.top_count,a.or_count
    if k<1 or r<0 or 2*k+1+r>21 or a.jobs<1 or min(a.seconds,a.wall_seconds)<=0:
        ap.error("invalid limits")
    start=time.monotonic()
    n,edges=sw.v1.CASES["l2260"]
    parts,generic=sw.candidates(n,edges,k,r)
    if (k,r) in dbv2.EXPECTED and (generic,len(parts))!=dbv2.EXPECTED[k,r]:
        raise ValueError("enumeration cross-check failed")
    blocks=Counter(max(p)+1 for p in parts)
    print("[PARTITIONS]",json.dumps({"k":k,"r":r,"generic":generic,
          "refined":len(parts),"by_blocks":dict(sorted(blocks.items())),
          "enumeration_seconds":round(time.monotonic()-start,3)}),flush=True)
    root=Path(__file__).resolve().parent
    h=hashlib.sha256(json.dumps([n,edges,k,r,"fixed-strong",parts]).encode())
    for name in sw.v19.DEPS+("pnp_sat_solve_v19.py","pnp_graph_partition_exact_v1.py",
            "pnp_graph_partition_sweep_v1.py","pnp_graph_partition_sweep_v2.py",
            "pnp_graph_partition_incremental_v1.py","pnp_graph_partition_fixed_bench_v1.py",
            "pnp_graph_partition_fixed_sweep_v1.py"):
        h.update((root/name).read_bytes())
    path=a.checkpoint or Path(f"sat-results/l2260-fixed-strong-k{k}-r{r}.sqlite3")
    path.parent.mkdir(parents=True,exist_ok=True)
    with open(str(path)+".lock","a") as lock:
        fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
        db=dbv2.open_db(path,h.hexdigest())
        try:
            states=dbv2.load(db,parts)
            pending=[i for i in range(1,len(parts)+1) if states.get(i)!="UNSAT"]
            # Complete never-attempted partitions before reattempting
            # timeouts; a resume does not get stuck on early hard cubes.
            pending.sort(key=lambda i:(i in states,i))
            prior=len(parts)-len(pending)
            unsat=prior
            count=0
            new=Counter()
            print("[CONFIG]",json.dumps({"pending":len(pending),"prior_unsat":prior,
                  "jobs":a.jobs,"seconds":a.seconds,"solver":a.solver,
                  "wall_limit":a.wall_seconds,"checkpoint":str(path)}),flush=True)
            stop=any(s in ("SAT","MODEL_INVALID") for s in states.values())
            if pending and not stop:
                with cf.ProcessPoolExecutor(max_workers=a.jobs,mp_context=mp.get_context("spawn")) as pool:
                    todo=iter(pending)
                    fs={}
                    def fill():
                        while len(fs)<a.jobs and time.monotonic()-start<a.wall_seconds:
                            idx=next(todo,None)
                            if idx is None:break
                            task=(idx,parts[idx-1],k,r,a.solver,a.seconds,"strong")
                            fs[pool.submit(bench.run,task)]=idx
                    fill()
                    last=time.monotonic()
                    while fs:
                        done,_=cf.wait(fs,return_when=cf.FIRST_COMPLETED)
                        for f in done:
                            idx=fs.pop(f)
                            try:out=f.result()
                            except Exception as e:out={"status":"ERROR","error":repr(e)}
                            st=out.get("status","ERROR")
                            if st=="UNSAT" and (out.get("partition")!=idx or out.get("assignment")!=list(parts[idx-1])):
                                out={"status":"ERROR","error":"partition result mismatch"}
                                st="ERROR"
                            dbv2.save(db,idx,out)
                            states[idx]=st
                            new[st]+=1
                            count+=1
                            if st=="UNSAT":unsat+=1
                            elif st!="TIMEOUT":
                                print("[TARGET]",idx,json.dumps(out),flush=True)
                                stop=True
                        if time.monotonic()-last>=10 or stop:
                            print("[PROGRESS]",json.dumps({"attempted":count,"unsat":unsat,
                                  "new_unsat":unsat-prior,"timeouts":new["TIMEOUT"],
                                  "total":len(parts),"elapsed":round(time.monotonic()-start,3)}),flush=True)
                            last=time.monotonic()
                        if not stop:fill()
            rem=[i for i in range(1,len(parts)+1) if states.get(i)!="UNSAT"]
            state=("ERROR" if any(s in ("ERROR","MODEL_INVALID") for s in states.values())
                   else "SAT" if "SAT" in states.values()
                   else "UNRESOLVED" if rem else "ALL_PARTITIONS_UNSAT")
            print("[SUMMARY]",json.dumps({"status":state,"k":k,"r":r,
                  "total":len(parts),"prior_unsat":prior,"attempted":count,
                  "unsat":unsat,"new_unsat":unsat-prior,"new_counts":dict(new),
                  "remaining_count":len(rem),"not_attempted":sum(i not in states for i in rem),
                  "remaining_by_blocks":dict(sorted(Counter(max(parts[i-1])+1 for i in rem).items())),
                  "remaining_partitions":rem if len(rem)<=100 else None,
                  "wall_seconds":round(time.monotonic()-start,3),"lean_verified":False}),flush=True)
            if state=="ERROR":raise SystemExit(1)
        finally:db.close()

if __name__=="__main__":main()
