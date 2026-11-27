#!/usr/bin/env python3
"""Fixed partition SAT benchmark: explicit first merge and edge clique cuts.

No MDD, no symbolic component labels, no range expansion. Compare matched
stratified samples against v2 (same exact circuit CNF and solver).
"""
import argparse
import concurrent.futures as cf
from collections import defaultdict, Counter
import json
import multiprocessing as mp
import random
import time
from pathlib import Path
import pnp_graph_partition_sweep_v1 as sw
import pnp_graph_partition_incremental_v1 as inc

def incompatible_cliques(edges,part,k):
    # A clean first-merge AND is a star (no four-cycle) whose two
    # effective singleton supports each occupy one original block.
    # Different group pairs OR disjoint endpoints cannot share a top.
    groups=[tuple(sorted((part[u],part[v]))) for u,v in edges]
    N=[set() for _ in edges]
    for i,e in enumerate(edges):
        for j in range(i):
            if groups[i]!=groups[j] or not set(e).intersection(edges[j]):
                N[i].add(j);N[j].add(i)
    out=[]
    def visit(R,P,X):
        if len(R)+len(P)<=k:return
        if not P and not X:
            out.append(tuple(sorted(R)));return
        pivot=max(P|X,key=lambda u:(len(P&N[u]),-u))
        for v in sorted(P-N[pivot]):
            visit(R|{v},P&N[v],X&N[v])
            P.remove(v);X.add(v)
    visit(set(),set(range(len(edges))),set())
    return out

def conditional_atmost(enc,xs,b,guard):
    if b>=len(xs):return
    start=len(enc.cnf)
    enc.atmost(xs,b)
    for i in range(start,len(enc.cnf)):
        enc.cnf[i].append(-guard)

def strengthen(enc,edges,part):
    n,m=enc.n,enc.m
    b=max(part)+1
    slack=m-(n-b)
    if slack<0:raise ValueError("impossible component count")
    start=len(enc.cnf)
    sides,_=inc.singleton_sides(enc)
    inc.first_merge(enc,edges,sides)
    # Explicit support locality. Even when a source is a single junk
    # atom, its nonempty effective singleton set has one component.
    for pair in enc.ands:
        for _,S in pair:
            for u in range(n):
                for v in range(u):
                    if part[u]!=part[v]:enc.add(-S[u],-S[v])
            for a in range(b):
                raw=[S[v] for v in range(n) if part[v]==a]
                present=enc.disj(raw)
                # Other raw components need at least |block|-1 ORs;
                # hence this one has <= |block|-1+slack ORs. A root
                # containing raw inputs in this component needs >=
                # |symbolic support|-1 ORs in its cone.
                conditional_atmost(enc,raw+S[n:],len(raw)+slack,present)
    for pair in sides:
        for S in pair:
            for u in range(n):
                for v in range(u):
                    if part[u]!=part[v]:enc.add(-S[u],-S[v])
    # On any clique of mutually incompatible graph edges, each clean
    # top covers <=1 by first merge. At least |clique|-k must therefore
    # be first-merge candidates of either junk AND. We overapproximate
    # first merge by the opposite-singleton condition, which is safe.
    junk=[]
    for u,v in edges:
        terms=[]
        for A,B in sides[:2]:
            terms.extend([enc.conj([A[u],B[v],-A[v],-B[u]]),
                          enc.conj([A[v],B[u],-A[u],-B[v]])])
        junk.append(enc.disj(terms))
    cliques=incompatible_cliques(edges,part,enc.k)
    for C in cliques:
        enc.atmost([-junk[e] for e in C],enc.k)
    return {"extra_clauses":len(enc.cnf)-start,"edge_cliques":len(cliques)}

def run(task):
    idx,part,k,r,solver,seconds,variant=task
    t=time.monotonic()
    n,edges=sw.v1.CASES["l2260"]
    enc,_,_,meta=sw.v19.build(n,edges,2*k+1+r,k,17,r,[],True,"compact")
    info=sw.ex.constrain_partition(enc,part)
    extra=strengthen(enc,edges,part) if variant=="strong" else {}
    out=sw.v4.solve(enc,"full",17,solver,seconds,10000)
    if out.get("status")=="SAT" and out.get("witness",{}).get("internal_or_gates")!=r:
        out.update(status="MODEL_INVALID",error="wrong exact OR count")
    return {"partition":idx,"assignment":list(part),"variant":variant,
            "variables":enc.max_var,"clauses":len(enc.cnf),**info,**extra,
            **out,"elapsed":round(time.monotonic()-t,3)}

def self_test(name):
    from pysat.solvers import Solver
    from itertools import combinations
    # Brute force every clique of the 16-edge incompatibility graph
    # for these representative partitions, compare maximal cliques.
    n,edges=sw.v1.CASES["l2260"]
    for part in ((0,)*n,tuple(range(n)),(0,0,1,2,0,0,0,3,2,0,4)):
        group=[tuple(sorted((part[u],part[v]))) for u,v in edges]
        def clash(i,j):
            return group[i]!=group[j] or not set(edges[i]).intersection(edges[j])
        masks=[]
        for t in range(6,len(edges)+1):
            for C in combinations(range(len(edges)),t):
                if all(clash(i,j) for i,j in combinations(C,2)) and not any(
                    all(clash(i,j) for i in C) for j in range(len(edges)) if j not in C):
                    masks.append(C)
        assert set(masks)==set(incompatible_cliques(edges,part,5))
    # Small exact cases with both SAT and UNSAT. In particular preserve
    # the known non-minimal witness and all tested exact partitions.
    inc.self_test(name)
    n,edges,k,base=3,[(0,1)],1,2
    sat=unsat=0
    for r in (0,1,2):
        for p in ((0,0,0),(0,0,1),(0,1,0),(0,1,1),(0,1,2)):
            if r<n-(max(p)+1):continue
            enc,_,_,_=sw.v19.build(n,edges,2*k+1+r,k,base,r,[],False,"compact")
            sw.ex.constrain_partition(enc,p)
            with Solver(name=name,bootstrap_with=enc.cnf) as sol:
                expected=sol.solve()
            strengthen(enc,edges,p)
            with Solver(name=name,bootstrap_with=enc.cnf) as sol:
                assert sol.solve()==expected,(r,p,expected)
                if expected:sat+=1
                else:unsat+=1
    assert sat and unsat,(sat,unsat)
    print("FIXED FIRST MERGE SELF TEST OK",{"sat":sat,"unsat":unsat},flush=True)

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--top-count",type=int,default=5)
    ap.add_argument("--or-count",type=int,default=8)
    ap.add_argument("--per-block",type=int,default=32)
    ap.add_argument("--seconds",type=float,default=2)
    ap.add_argument("--jobs",type=int,default=8)
    ap.add_argument("--solver",default="cadical195")
    ap.add_argument("--seed",type=int,default=2260)
    ap.add_argument("--output",type=Path)
    ap.add_argument("--self-test",action="store_true")
    a=ap.parse_args()
    if a.self_test:self_test(a.solver);return
    k,r=a.top_count,a.or_count
    if k<1 or r<0 or 2*k+1+r>21 or min(a.per_block,a.jobs)<1 or a.seconds<=0:
        ap.error("invalid limits")
    n,edges=sw.v1.CASES["l2260"]
    parts,generic=sw.candidates(n,edges,k,r)
    groups=defaultdict(list)
    for i,p in enumerate(parts,1):groups[max(p)+1].append(i)
    rng=random.Random(a.seed)
    sample=sorted(i for ids in groups.values() for i in rng.sample(ids,min(len(ids),a.per_block)))
    # Both variants use identical partition IDs; separate phases avoid
    # baseline and strong formula competing for resources.
    print("[CONFIG]",json.dumps({"k":k,"r":r,"total":len(parts),
          "sample":len(sample),"by_blocks":dict(Counter(max(parts[i-1])+1 for i in sample)),
          "seconds":a.seconds,"jobs":a.jobs,"seed":a.seed}),flush=True)
    path=a.output or Path(f"sat-results/l2260-fixed-bench-k{k}-r{r}-{a.seed}.json")
    path.parent.mkdir(parents=True,exist_ok=True)
    all_results={}
    for variant in ("baseline","strong"):
        start=time.monotonic()
        rows={}
        with cf.ProcessPoolExecutor(max_workers=a.jobs,mp_context=mp.get_context("fork")) as pool:
            fs={pool.submit(run,(i,parts[i-1],k,r,a.solver,a.seconds,variant)):i for i in sample}
            for f in cf.as_completed(fs):
                i=fs[f]
                try:out=f.result()
                except Exception as e:out={"status":"ERROR","error":repr(e)}
                rows[i]=out
                if out["status"] not in ("UNSAT","TIMEOUT"):
                    print("[TARGET]",variant,i,json.dumps(out),flush=True)
        all_results[variant]=rows
        print("[BENCH]",json.dumps({"variant":variant,"counts":dict(Counter(x["status"] for x in rows.values())),
            "wall_seconds":round(time.monotonic()-start,3),
            "sum_task_seconds":round(sum(x.get("elapsed",0) for x in rows.values()),3),
            "by_blocks":{b:dict(Counter(rows[i]["status"] for i in sample if max(parts[i-1])+1==b))
                         for b in sorted(groups)}}),flush=True)
    matrix=Counter((all_results["baseline"][i]["status"],all_results["strong"][i]["status"]) for i in sample)
    out={"k":k,"r":r,"sample":sample,"results":all_results,
         "paired":{f"{a}->{b}":n for (a,b),n in matrix.items()},"lean_verified":False}
    path.write_text(json.dumps(out,indent=2)+"\n")
    print("[SUMMARY]",json.dumps({"sample":len(sample),"paired":out["paired"],
          "output":str(path),"lean_verified":False}),flush=True)
    if any(x["status"] not in ("UNSAT","TIMEOUT") for rows in all_results.values() for x in rows.values()):
        raise SystemExit(1)

if __name__=="__main__":main()
