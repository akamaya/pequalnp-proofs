#!/usr/bin/env python3
"""Targeted exact SAT for the two remaining graph-partition-v3 survivors.

Checks all realizations within each partition, not merely the first
printed junk witness. Graph-v3 exclusions remain unformalized.
"""
import argparse
import concurrent.futures as cf
import json
import re
import time
from pathlib import Path
import pnp_sat_solve_v1 as v1
import pnp_sat_solve_v4 as v4
import pnp_sat_solve_v19 as v19


def read_shards(root,shards=4):
    found={}
    seen=set()
    for shard in range(shards):
        path=root/f"l2260-graph-v3-{shard}.log"
        pending=None
        partition=None
        local=set()
        survivors={}
        summaries=[]
        for line in path.read_text().splitlines():
            if line.startswith("[RELAXED WITNESS]"):
                m=re.search(r"\bpartition=(\d+)\b",line)
                if not m or pending is not None:
                    raise ValueError(f"{path}: malformed witness sequence")
                pending=int(m.group(1))
            elif line.endswith(" survives"):
                m=re.fullmatch(r"([0-9]{11}) survives",line)
                if not m or pending is None or partition is not None:
                    raise ValueError(f"{path}: malformed survivor")
                partition=tuple(map(int,m.group(1)))
                if partition[0]!=0 or any(x>1+max(partition[:i]) for i,x in enumerate(partition) if i):
                    raise ValueError("invalid restricted-growth partition")
                if max(partition)+1 not in (5,6):
                    raise ValueError("invalid component count")
            elif line.startswith("[PARTITION]"):
                m=re.match(r"\[PARTITION\] (\d+)\b",line)
                if not m:raise ValueError(f"{path}: malformed progress")
                idx=int(m.group(1))
                if idx in local or idx in seen or not 1<=idx<=878 or (idx-1)%shards!=shard:
                    raise ValueError(f"{path}: duplicate or misplaced partition {idx}")
                local.add(idx);seen.add(idx)
                if pending is not None:
                    if pending!=idx or partition is None:
                        raise ValueError(f"{path}: missing survivor details")
                    survivors[idx]=partition
                    pending=None;partition=None
            elif line.startswith("before "):
                m=re.fullmatch(r"before (\d+) examined (\d+) after (\d+) pairs (\d+) merge (\d+) cover (\d+)",line)
                if not m:raise ValueError(f"{path}: malformed summary")
                summaries.append(tuple(map(int,m.groups())))
        expected={i for i in range(1,879) if (i-1)%shards==shard}
        if (pending is not None or partition is not None or local!=expected
            or len(summaries)!=1 or summaries[0][:3]!=(878,len(local),len(survivors))
            or summaries[0][5]!=len(survivors)):
            raise ValueError(f"{path}: incomplete or inconsistent shard")
        found.update(survivors)
    if seen!=set(range(1,879)):
        raise ValueError("partition coverage incomplete")
    return found


def exactly_one(enc,xs):
    enc.add(*xs)
    enc.atmost(xs,1)


def constrain_partition(enc,part):
    """Necessary final component restrictions; no assumption on junk truth."""
    n=enc.n
    if len(part)!=n or min(part)!=0 or set(part)!=set(range(max(part)+1)):
        raise ValueError("invalid partition")
    b=max(part)+1
    m=enc.m
    labels=b+2
    # Two possible original-free components are sufficient.
    junk=[[enc.fresh() for _ in range(labels)] for _ in range(2)]
    for p in junk:exactly_one(enc,p)
    # Singleton truth determines the original component of bearing junk.
    A,B=[bits for _,bits in enc.ands[0]]
    X,Y=[bits for _,bits in enc.ands[1]]
    s0=[enc.conj([A[v],B[v]]) for v in range(n)]
    s1=[enc.conj([enc.disj([X[v],enc.conj([X[n],s0[v]])]),
                  enc.disj([Y[v],enc.conj([Y[n],s0[v]])])])
        for v in range(n)]
    bearing=[enc.disj(s) for s in (s0,s1)]
    for h,s in enumerate((s0,s1)):
        for v,z in enumerate(s):
            enc.add(-z,junk[h][part[v]])
    # The cube uses exactly m internal ORs, so every slot is active.
    # The component of every OR's complete symbolic support is unique.
    ors=[]
    for active,S in zip(enc.active,enc.support):
        enc.add(active)
        P=[enc.fresh() for _ in range(labels)]
        exactly_one(enc,P)
        ors.append(P)
        for v in range(n):
            enc.add(-S[v],P[part[v]])
        for h in range(2):
            for a in range(labels):
                enc.add(-S[n+h],-P[a],junk[h][a])
    # Rank bound per original component:
    # ORs_in_block >= original_vertices - 1 + attached nonbearing junk.
    for a in range(b):
        attached=[enc.conj([junk[h][a],-bearing[h]]) for h in range(2)]
        enc.atmost([-P[a] for P in ors]+attached,m-(part.count(a)-1))
    # Two junk atoms in a common original-free component need an OR.
    for a in range(b,labels):
        enc.add(-junk[0][a],-junk[1][a],*(P[a] for P in ors))
    return {"blocks":b,"slack":m-(n-b)}


def run(task):
    idx,part,solver,seconds,chunk,mode=task
    t=time.monotonic()
    n,edges=v1.CASES["l2260"]
    # Build only the exact six-OR formula, not the previous ten-slot
    # budget. No v16 cut import or prior semantic witness is required.
    enc,_,_,meta=v19.build(n,edges,21,5,17,6,[],True,mode)
    before=len(enc.cnf)
    info=constrain_partition(enc,part)
    meta.update(info,partition=idx,assignment=list(part),solver=solver,
                clauses=len(enc.cnf),variables=enc.max_var,
                partition_clauses=len(enc.cnf)-before,
                build_seconds=round(time.monotonic()-t,3))
    print("[TARGET CNF]",json.dumps(meta),flush=True)
    out=v4.solve(enc,"full",17,solver,seconds,chunk)
    if out.get("status")=="SAT" and out.get("witness",{}).get("internal_or_gates")!=6:
        out.update(status="MODEL_INVALID",error="wrong exact OR count")
    return {**meta,**out}


def self_test(solver):
    from pysat.solvers import Solver
    # Known v19 witness (not minimum): J0=x1&x2,
    # J1=x1&(x0|x1|J0), top=x0&J1.
    ss=[2,4,2,11,1,16]
    for part,expected in (((0,0,1),True),((0,1,2),False)):
        enc,_,_,_=v19.build(3,[(0,1)],5,1,2,2,[],False,"compact")
        constrain_partition(enc,part)
        ass=[x if S&(1<<i) else -x for S,bits in zip(ss,enc.sidebits)
             for i,x in enumerate(bits)]
        with Solver(name=solver,bootstrap_with=enc.cnf) as sol:
            assert sol.solve(assumptions=ass)==expected,(part,expected)
            if expected:
                w=enc.decode(sol.get_model())
                assert v1.verify(3,enc.masks,w)
                assert v4.check_star(3,enc.masks,w,2,True)["valid"]
    print("PARTITION EXACT SELF TEST OK",flush=True)


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--logs",type=Path,default=Path("sat-results"))
    ap.add_argument("--shards",type=int,default=4)
    ap.add_argument("--seconds",type=float,default=120)
    ap.add_argument("--jobs",type=int,default=2)
    ap.add_argument("--solver",default="cadical195")
    ap.add_argument("--chunk",type=int,default=20000)
    ap.add_argument("--mode",choices=("compact","canonical"),default="compact")
    ap.add_argument("--self-test",action="store_true")
    a=ap.parse_args()
    if min(a.shards,a.jobs,a.chunk)<1 or a.seconds<=0:ap.error("invalid limits")
    if a.self_test:self_test(a.solver);return
    found=read_shards(a.logs,a.shards)
    print("[CONFIG]",json.dumps({"partitions":found,"seconds":a.seconds,
          "jobs":a.jobs,"solver":a.solver,"mode":a.mode}),flush=True)
    start=time.monotonic()
    results={}
    with cf.ProcessPoolExecutor(max_workers=a.jobs) as pool:
        fs={pool.submit(run,(idx,p,a.solver,a.seconds,a.chunk,a.mode)):idx
            for idx,p in found.items()}
        for f in cf.as_completed(fs):
            idx=fs[f]
            try:out=f.result()
            except Exception as e:out={"status":"ERROR","error":repr(e)}
            results[idx]=out
            print("[TARGET]",idx,json.dumps(out),flush=True)
    remaining=[i for i in found if results[i]["status"]!="UNSAT"]
    state=("ERROR" if any(x["status"] in ("ERROR","MODEL_INVALID") for x in results.values())
           else "SAT" if any(x["status"]=="SAT" for x in results.values())
           else "UNRESOLVED" if remaining else "ALL_TARGETS_UNSAT")
    print("[SUMMARY]",json.dumps({"status":state,"remaining_partitions":remaining,
          "checked":len(results),"wall_seconds":round(time.monotonic()-start,3),
          "lean_verified":False}),flush=True)
    if state=="ERROR":raise SystemExit(1)


if __name__=="__main__":main()
