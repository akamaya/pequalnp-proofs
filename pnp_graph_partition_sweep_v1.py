#!/usr/bin/env python3
"""Enumerate graph partitions, then solve the exact circuit in each.

Uses graph_partition_v1.md's necessary bounds and the component encoding
tested in pnp_graph_partition_exact_v1.py. No graph-v3 screening needed.
All exclusions remain conditional on the unformalized reductions.
"""
import argparse
import concurrent.futures as cf
from functools import lru_cache
import hashlib
import json
import multiprocessing as mp
import os
from pathlib import Path
import time

import pnp_sat_solve_v1 as v1
import pnp_sat_solve_v4 as v4
import pnp_sat_solve_v19 as v19
import pnp_graph_partition_exact_v1 as ex

def candidates(n,edges,k,r):
    incident=[0]*n
    for i,(u,v) in enumerate(edges):
        incident[u]|=1<<i
        incident[v]|=1<<i
    @lru_cache(None)
    def cover(m):
        if not m:return 0
        i=(m&-m).bit_length()-1
        u,v=edges[i]
        return 1+min(cover(m&~incident[u]),cover(m&~incident[v]))
    # The first-merge star bound assumes no C4.
    adj=[set() for _ in range(n)]
    for u,v in edges:adj[u].add(v);adj[v].add(u)
    if any(len(adj[u]&adj[v])>1 for u in range(n) for v in range(u)):
        raise ValueError("four-cycle violates star bound")
    p=[0]*n
    out=[]
    generic=0
    def walk(i,b):
        nonlocal generic
        if b+n-i<n-r:return
        if i<n:
            for x in range(b+1):
                p[i]=x
                walk(i+1,max(b,x+1))
            return
        g={}
        for j,(u,v) in enumerate(edges):
            a,c=sorted((p[u],p[v]))
            g[a,c]=g.get((a,c),0)|(1<<j)
        t={q:cover(m) for q,m in g.items()}
        s=sum(t.values())
        top=sorted(t.values(),reverse=True)+[0,0]
        if s-top[0]-top[1]>k:return
        generic+=1
        if b==n-r:
            loop=max((t.get((a,a),0) for a in range(b)),default=0)
            incident_discount=max((t.get((a,a),0)+
                max((t.get(tuple(sorted((a,c))),0) for c in range(b) if c!=a),default=0)
                for a in range(b)),default=0)
            if min(s-top[0]+1,s-incident_discount+1,s-loop)>k:return
        out.append(tuple(p))
    walk(1,1)
    return out,generic

def run(task):
    idx,part,k,r,solver,seconds,chunk,mode=task
    start=time.monotonic()
    n,edges=v1.CASES["l2260"]
    enc,_,_,meta=v19.build(n,edges,2*k+1+r,k,17,r,[],True,mode)
    info=ex.constrain_partition(enc,part)
    meta.update(info,partition=idx,assignment=list(part),solver=solver,
                variables=enc.max_var,clauses=len(enc.cnf),
                build_seconds=round(time.monotonic()-start,3))
    out=v4.solve(enc,"full",17,solver,seconds,chunk)
    if out.get("status")=="SAT" and out.get("witness",{}).get("internal_or_gates")!=r:
        out.update(status="MODEL_INVALID",error="wrong exact OR count")
    return {**meta,**out}

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--top-count",type=int,default=7)
    ap.add_argument("--or-count",type=int,default=5)
    ap.add_argument("--seconds",type=float,default=5)
    ap.add_argument("--jobs",type=int,default=8)
    ap.add_argument("--solver",default="cadical195")
    ap.add_argument("--chunk",type=int,default=20000)
    ap.add_argument("--mode",choices=("compact","canonical"),default="compact")
    ap.add_argument("--checkpoint",type=Path)
    ap.add_argument("--self-test",action="store_true")
    ap.add_argument("--list-only",action="store_true")
    a=ap.parse_args()
    k,r=a.top_count,a.or_count
    if k<1 or r<0 or 2*k+1+r>21 or min(a.jobs,a.chunk)<1 or a.seconds<=0:
        ap.error("invalid case or limits")
    n,edges=v1.CASES["l2260"]
    start=time.monotonic()
    parts,generic=candidates(n,edges,k,r)
    expected={(7,4):(82,0),(7,5):(11517,1272),(6,5):(1417,69),(5,6):(6349,878)}
    if (k,r) in expected and (generic,len(parts))!=expected[k,r]:
        raise ValueError("v1 enumeration cross-check failed")
    print("[PARTITIONS]",json.dumps({"k":k,"r":r,"generic":generic,
          "refined":len(parts),"by_blocks":{b:sum(max(p)+1==b for p in parts)
          for b in sorted({max(p)+1 for p in parts})},
          "enumeration_seconds":round(time.monotonic()-start,3)}),flush=True)
    if a.self_test:
        ex.self_test(a.solver)
        print("PARTITION SWEEP SELF TEST OK",flush=True)
        return
    if a.list_only:return
    root=Path(__file__).resolve().parent
    h=hashlib.sha256(json.dumps([n,edges,k,r,a.mode,parts]).encode())
    for name in v19.DEPS+("pnp_sat_solve_v19.py","pnp_graph_partition_exact_v1.py",
                          "pnp_graph_partition_sweep_v1.py"):
        h.update((root/name).read_bytes())
    key=h.hexdigest()
    path=a.checkpoint or Path(f"sat-results/l2260-graph-sweep-k{k}-r{r}-{a.mode}.json")
    path.parent.mkdir(parents=True,exist_ok=True)
    import fcntl
    with open(str(path)+".lock","a") as lock:
        fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
        data={"fingerprint":key,"results":{}}
        if path.exists():
            data=json.loads(path.read_text())
            if data.get("fingerprint")!=key:raise ValueError("checkpoint mismatch")
        results=data["results"]
        def save():
            tmp=path.with_name(path.name+".tmp")
            tmp.write_text(json.dumps(data,indent=2)+"\n")
            os.replace(tmp,path)
        def remaining():
            return [i for i in range(1,len(parts)+1)
                    if results.get(str(i),{}).get("status")!="UNSAT"]
        pending=remaining()
        print("[CONFIG]",json.dumps({"pending":len(pending),"prior_unsat":len(parts)-len(pending),
              "jobs":a.jobs,"seconds":a.seconds,"solver":a.solver}),flush=True)
        if not any(x.get("status")=="SAT" for x in results.values()):
            with cf.ProcessPoolExecutor(max_workers=a.jobs,mp_context=mp.get_context("fork")) as pool:
                todo=iter(pending)
                fs={}
                stop=False
                def fill():
                    while len(fs)<a.jobs:
                        idx=next(todo,None)
                        if idx is None:break
                        task=(idx,parts[idx-1],k,r,a.solver,a.seconds,a.chunk,a.mode)
                        fs[pool.submit(run,task)]=idx
                fill()
                count=0
                while fs:
                    done,_=cf.wait(fs,return_when=cf.FIRST_COMPLETED)
                    for f in done:
                        idx=fs.pop(f)
                        try:out=f.result()
                        except Exception as e:out={"status":"ERROR","error":repr(e)}
                        results[str(idx)]=out
                        count+=1
                        save()
                        st=out["status"]
                        if st!="UNSAT":
                            print("[TARGET]",idx,json.dumps(out),flush=True)
                        if st in ("SAT","ERROR","MODEL_INVALID"):stop=True
                    if count%25<len(done) or not fs or stop:
                        print("[PROGRESS]",json.dumps({"attempted":count,"unsat":len(parts)-len(remaining()),
                              "total":len(parts),"elapsed":round(time.monotonic()-start,3)}),flush=True)
                    if not stop:fill()
        rem=remaining()
        states=[x.get("status") for x in results.values()]
        state=("ERROR" if any(s in ("ERROR","MODEL_INVALID") for s in states) else
               "SAT" if "SAT" in states else "UNRESOLVED" if rem else "ALL_PARTITIONS_UNSAT")
        print("[SUMMARY]",json.dumps({"status":state,"k":k,"r":r,"remaining_count":len(rem),
              "remaining_partitions":rem,"total":len(parts),"wall_seconds":round(time.monotonic()-start,3),
              "lean_verified":False}),flush=True)
        if state=="ERROR":raise SystemExit(1)

if __name__=="__main__":main()
