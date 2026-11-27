#!/usr/bin/env python3
"""Read-only benchmark: exact-active-budget propagation and SAT solver tuning.

Global attached-junk charge follows by summing the existing component
rank inequalities. The per-support cap is the same bound as v1's AND
operand cap, applied also to actual OR supports and conditioned on the
number of active slots. No old DB is modified.
"""
import argparse
import concurrent.futures as cf
from collections import Counter,defaultdict
import copy
import hashlib
import json
import multiprocessing as mp
from pathlib import Path
import random
import sqlite3
import time
import pnp_graph_partition_fast_v1 as old
import pnp_graph_partition_fast_v2 as v2
import pnp_graph_partition_fast_v4 as v4

ENGINE_SHA=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()

def available(name):
    from pysat.solvers import Solver
    try:
        with Solver(name=name,bootstrap_with=[[1]]) as s:
            s.conf_budget(100)
            return s.solve_limited(assumptions=[-1]) is False
    except (NotImplementedError,ValueError) as e:
        print("[SOLVER UNAVAILABLE]",name,repr(e),flush=True)
        return False
    except Exception as e:
        if type(e).__name__=="NoSuchSolverError":
            print("[SOLVER UNAVAILABLE]",name,repr(e),flush=True)
            return False
        raise

def budget_build(n,edges,k,counts,part,base=17,minimal=True):
    counts=tuple(sorted(set(counts)))
    m=counts[-1]
    orig,sides,jtruth,bearing,hits=old.template(n,tuple(edges),k,m,base,minimal)
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
    junk=[old.inc.onehot(enc,L) for _ in range(2)]
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
    attached_all=[]
    for a in range(b):
        attached=[enc.conj([junk[h][a],-bearing[h]]) for h in range(2)]
        attached_all.extend(attached)
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
                    old.bench.conditional_atmost(enc,raw+S[n:],len(raw)+slack,present)
    for pair in sides:
        for S in pair:
            for u,v in different:enc.add(-S[u],-S[v])
    for C in old.bench.incompatible_cliques(edges,part,k):
        enc.atmost([-hits[e] for e in C],k)
    # Per-group rank inequalities imply a global budget after summing
    # over the disjoint groups. Two free junk atoms sharing a group
    # also cost at least one OR, from the existing free-group clause.
    free_cost=[enc.conj([junk[0][a],junk[1][a]]) for a in range(b,L)]
    budget_terms=attached_all+free_cost
    supports=[S for pair in enc.ands for _,S in pair]+list(enc.support)
    # Active slots are a suffix. If active[m-r-1] is false, at most r
    # ORs exist. Guard each stronger cardinality bound accordingly.
    for r in counts:
        guard=None if r==m else -enc.active[m-r-1]
        slack_r=r-(n-b)
        start=len(enc.cnf)
        enc.atmost(budget_terms,slack_r)
        if guard is not None:
            for c in enc.cnf[start:]:c.append(-guard)
        if slack_r>=2:continue
        for S in supports:
            for block in blocks:
                raw=[S[v] for v in block]
                # All nonempty raw parts use one component. If a
                # support contains a raw vertex, the union DAG needs
                # at least |S|-1 ORs in that component. Other raw
                # components require their own |block|-1 ORs.
                present=enc.disj(raw)
                start=len(enc.cnf)
                enc.atmost(raw+S[n:],len(raw)+slack_r)
                for c in enc.cnf[start:]:
                    c.append(-present)
                    if guard is not None:c.append(-guard)
    return enc

def solve(n,edges,k,counts,part,base,minimal,name,seconds,chunk,mode,batch):
    t=time.monotonic()
    if mode=="guard":
        out=v2.solve_fixed(n,edges,k,counts,part,base,minimal,name,seconds,chunk,
                           "guard",batch,.1)
        out["extra_clauses"]=0
        return out
    enc=(budget_build if mode=="budget" else old.build)(n,edges,k,counts,part,base,minimal)
    orig,sides,jtruth,bearing,hits=old.template(n,edges,k,max(counts),base,minimal)
    extra=v4.projected_cover(enc,edges,part,hits,True)
    if mode=="budget":extra=len(enc.cnf)-len(orig.cnf)
    local=enc.cnf[len(orig.cnf):]
    built=time.monotonic()
    obj=v2.pool(name,(n,edges,k,max(counts),base,minimal,mode),orig.cnf,orig.max_var,batch)
    loaded=time.monotonic()
    ans,model,ld,sl,stats=obj.query(local,enc.max_var,built+seconds,chunk)
    out={"status":"TIMEOUT" if ans is None else "SAT" if ans else "UNSAT",
         "counts":list(counts),"assignment":list(part),
         "build_seconds":built-t,"load_seconds":loaded-built+ld,
         "solve_seconds":sl,"stats":stats,"engine":"fast-v6-"+mode,
         "engine_sha256":ENGINE_SHA,"extra_clauses":extra,
         "base_clauses":len(orig.cnf)}
    if ans is True:
        pos=set(model)
        if not all(any(x in pos for x in c) for c in enc.cnf):
            raise ValueError("model does not satisfy concrete CNF")
        w=enc.decode(model)
        chk=old.sw.v4.check_star(n,enc.masks,w,base,True)
        ok=(old.sw.v1.verify(n,enc.masks,w) and chk["valid"]
            and w["internal_or_gates"] in counts)
        out.update(witness=w,structure_check=chk,verified_full_truth_table=ok)
        if not ok:out["status"]="MODEL_INVALID"
    out["elapsed"]=time.monotonic()-t
    return out

def direct(task):
    part,k,counts,name,seconds,chunk,mode,batch=task
    n,edges=old.sw.v1.CASES["l2260"]
    return solve(n,tuple(edges),k,counts,part,17,True,name,seconds,chunk,
        mode,batch)


def self_test(name):
    from itertools import combinations
    from pysat.solvers import Solver
    v4.self_test(name)
    sat=unsat=0
    for n,edges in ((3,((0,1),)),(3,((0,1),(0,2),(1,2))),
                    (4,((0,1),(1,2),(2,3)))):
        # All canonical raw partitions of these small graphs.
        def parts(p):
            if len(p)==n:
                yield p
                return
            for a in range(max(p)+2):yield from parts(p+(a,))
        for part in parts((0,)):
            for k in (1,2):
                rs=range(n-(max(part)+1),min(3,n-1)+1)
                for size in range(1,len(rs)+1):
                    for counts in combinations(rs,size):
                        enc=old.build(n,edges,k,counts,part,0,False)
                        with Solver(name=name,bootstrap_with=enc.cnf) as s:expected=s.solve()
                        out=solve(n,edges,k,counts,part,0,False,name,10,2000,"budget",4)
                        assert out["status"]==("SAT" if expected else "UNSAT"),(n,edges,part,k,counts,out)
                        sat+=expected;unsat+=not expected
    assert sat and unsat
    for o in v2.POOLS.values():o.close()
    v2.POOLS.clear()
    print("FAST V6 ACTIVE BUDGET SELF TEST OK",{"sat":sat,"unsat":unsat},flush=True)

def benchmark(a,rest):
    # Read the same immutable v1 checkpoints without changing them.
    p=argparse.ArgumentParser()
    p.add_argument("--top-count",type=int,default=5)
    p.add_argument("--or-min",type=int,default=8)
    p.add_argument("--or-max",type=int,default=10)
    p.add_argument("--jobs",type=int,default=8)
    p.add_argument("--seconds",type=float,default=2)
    p.add_argument("--chunk",type=int,default=2000)
    p.add_argument("--solver",default="cadical195")
    p.add_argument("--solvers",default="cadical195,cadical153,glucose42,maplechrono")
    b=p.parse_args(rest)
    n,edges=old.sw.v1.CASES["l2260"]
    lookup=defaultdict(list)
    seen=defaultdict(bool)
    for r in range(b.or_min,b.or_max+1):
        parts,generic=old.sw.candidates(n,edges,b.top_count,r)
        if (b.top_count,r) in old.dbv2.EXPECTED and (generic,len(parts))!=old.dbv2.EXPECTED[b.top_count,r]:
            raise ValueError("enumeration mismatch")
        path=Path("sat-results")/f"l2260-fast-strong-k{b.top_count}-r{r}.sqlite3"
        states={}
        if path.exists():
            with sqlite3.connect(path.resolve().as_uri()+"?mode=ro",uri=True) as db:
                if db.execute("SELECT fingerprint FROM meta WHERE id=1").fetchone()!=(old.key(n,edges,b.top_count,r,parts,True),):
                    raise ValueError("checkpoint fingerprint mismatch")
                states=old.dbv2.load(db,parts)
                if any(s not in ("UNSAT","TIMEOUT") for s in states.values()):
                    raise ValueError("inspect previous SAT/error")
        for idx,part in enumerate(parts,1):
            if states.get(idx)!="UNSAT":
                lookup[part].append(r)
                seen[part]|=states.get(idx)=="TIMEOUT"
    groups=defaultdict(list)
    for part,rr in lookup.items():groups[max(part)+1,seen[part]].append((part,tuple(rr)))
    rng=random.Random(2260)
    sample=[t for key in sorted(groups) for t in rng.sample(groups[key],min(a.compare,len(groups[key])))]
    # Group by max r for solver reuse, otherwise randomized matched cases.
    sample.sort(key=lambda t:(max(t[1]),max(t[0]),t[0]))
    print("[COMPARE CONFIG]",json.dumps({"cubes":len(sample),"exact":sum(len(rr) for _,rr in sample),
          "groups":{str(k):len(v) for k,v in groups.items()},"batch":a.batch_size,
          "seconds":b.seconds,"solvers":b.solvers,"engines":["direct","budget"]}),flush=True)
    known={}
    ctx=mp.get_context("spawn")
    configs=[("direct",b.solver),("budget",b.solver)]
    for name in b.solvers.split(","):
        if name and name!=b.solver:configs.append(("direct",name))
    for mode,name in configs:
        if not available(name):
            print("[SKIP SOLVER]",name,flush=True)
            continue
        rows=[]
        start=time.monotonic()
        with cf.ProcessPoolExecutor(max_workers=b.jobs,mp_context=ctx) as pool:
            fs={pool.submit(direct,(part,b.top_count,rr,name,b.seconds,b.chunk,mode,a.batch_size)):(part,rr)
                for part,rr in sample}
            for f in cf.as_completed(fs):
                part,rr=fs[f]
                out=f.result()
                st=out["status"]
                if st not in ("UNSAT","TIMEOUT","SAT"):raise RuntimeError(out)
                if st=="SAT":
                    print("[TARGET]",json.dumps(out),flush=True)
                    raise RuntimeError("SAT witness found; inspect before continuing")
                if mode=="direct" and name==b.solver:known[part,rr]=st
                rows.append((rr,out))
        wall=time.monotonic()-start
        done=sum(len(rr) for rr,o in rows if o["status"]=="UNSAT")
        print("[COMPARE]",json.dumps({"mode":mode,"solver":name,"wall_seconds":round(wall,3),
              "calls":len(rows),"counts":dict(Counter(o["status"] for _,o in rows)),
              "exact_unsat":done,"exact_unsat_per_second":round(done/wall,3),
              "extra_clauses_mean":round(sum(o.get("extra_clauses",0) for _,o in rows)/max(1,len(rows)),1),
              "sum_build":round(sum(o.get("build_seconds",0) for _,o in rows),3),
              "sum_load":round(sum(o.get("load_seconds",0) for _,o in rows),3),
              "sum_solve":round(sum(o.get("solve_seconds",0) for _,o in rows),3),
              "base_clauses":next((o["base_clauses"] for _,o in rows if "base_clauses" in o),None),
              "prior_timeouts_unsat":sum(1 for (rr,o) in rows if o["status"]=="UNSAT" and seen[tuple(o["assignment"])])}),flush=True)



def main():
    p=argparse.ArgumentParser(add_help=False)
    p.add_argument("--compare",type=int,default=24)
    p.add_argument("--batch-size",type=int,default=16)
    p.add_argument("--self-test",action="store_true")
    a,rest=p.parse_known_args()
    if min(a.compare,a.batch_size)<1:p.error("invalid limits")
    if a.self_test:
        s=argparse.ArgumentParser()
        s.add_argument("--solver",default="cadical195")
        self_test(s.parse_args(rest).solver)
    else:benchmark(a,rest)
if __name__=="__main__":main()
