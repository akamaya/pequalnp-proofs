#!/usr/bin/env python3
"""Benchmark exact projection of group vertex cover onto junk-hit bits.
All new clauses are implied (with fresh existential variables) by v3
cover. Existing checkpoints are read only. No new graph assumptions.
"""
import argparse
import concurrent.futures as cf
from collections import Counter, defaultdict
import hashlib
import functools
import json
import multiprocessing as mp
import os
from pathlib import Path
import random
import sqlite3
import time

import pnp_graph_partition_fast_v1 as old
import pnp_graph_partition_fast_v2 as v2

ENGINE_SHA=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()

def group_edges(edges,part):
    return [tuple(sorted((part[u],part[v]))) for u,v in edges]

def verify_graph(n,edges):
    if len(edges)!=len(set(edges)) or any(not 0<=u<v<n for u,v in edges):
        raise ValueError("expected simple sorted edges")
    adj=[set() for _ in range(n)]
    for u,v in edges:
        adj[u].add(v);adj[v].add(u)
    if any(len(adj[u]&adj[v])>1 for u in range(n) for v in range(u)):
        raise ValueError("cover cut requires C4-free graph")

def cover_cuts(enc,edges,part,sides,hits,star=False):
    verify_graph(enc.n,edges)
    before=len(enc.cnf)
    groups=group_edges(edges,part)
    center={}
    for (u,v),g in zip(edges,groups):
        for w in (u,v):
            if (g,w) not in center:center[g,w]=enc.fresh()
    enc.atmost(list(center.values()),enc.k)
    for (u,v),g,h in zip(edges,groups,hits):
        enc.add(h,center[g,u],center[g,v])
    if star:
        # Both effective singleton sides cannot have two vertices:
        # disjoint sides + all cross edges would give a four-cycle.
        for A,B in sides[2:]:
            pick=enc.fresh()
            for xs,guard in ((A,pick),(B,-pick)):
                for i,x in enumerate(xs):
                    for y in xs[:i]:enc.add(-guard,-x,-y)
        # Each dirty AND's effective singleton sides are local even
        # when they overlap. Every oriented exclusive first merge uses
        # the same unordered pair of raw block labels.
        keys=sorted(set(groups))
        for A,B in sides[:2]:
            gs={g:enc.fresh() for g in keys}
            enc.atmost(list(gs.values()),1)
            for (u,v),g in zip(edges,groups):
                enc.add(-A[u],-B[v],A[v],B[u],gs[g])
                enc.add(-A[v],-B[u],A[u],B[v],gs[g])
    return len(enc.cnf)-before


@functools.lru_cache(maxsize=32768)
def minimal_obstructions(edges):
    """For each t, inclusion-minimal edge sets with vertex cover >= t."""
    incident={}
    for i,(u,v) in enumerate(edges):
        for w in (u,v):incident[w]=incident.get(w,0)|(1<<i)
    @functools.lru_cache(None)
    def tau(mask):
        if not mask:return 0
        i=(mask&-mask).bit_length()-1
        u,v=edges[i]
        return 1+min(tau(mask&~incident[u]),tau(mask&~incident[v]))
    groups=defaultdict(list)
    for mask in range(1,1<<len(edges)):
        t=tau(mask)
        # Removing one edge reduces tau by at most one. Monotonicity
        # then makes this test equivalent to inclusion minimality.
        bits=[i for i in range(len(edges)) if mask&(1<<i)]
        if all(tau(mask^(1<<i))<t for i in bits):
            groups[t].append(tuple(bits))
    return tuple((t,tuple(groups[t])) for t in sorted(groups))

def projected_cover(enc,edges,part,hits,direct=False):
    """Existential projection of v3 cover onto junk-hit variables.

    If all edges of an obstruction have hit=False, its group needs
    at least t centers. Monotone threshold flags count these costs.
    In direct mode add up to 512 globally valid clauses as well:
    a collection of disjoint-group obstructions of total cost k+1
    must contain a junk hit. The cap affects speed, never soundness.
    """
    verify_graph(enc.n,edges)
    before=len(enc.cnf)
    groups=defaultdict(list)
    for i,g in enumerate(group_edges(edges,part)):groups[g].append(i)
    allflags=[]
    blocks=[]
    for ids in groups.values():
        obs=minimal_obstructions(tuple(edges[i] for i in ids))
        flags=[]
        choices=[]
        for t,sets in obs:
            z=enc.fresh()
            if flags:enc.add(-z,flags[-1])
            flags.append(z)
            clauses=[tuple(hits[ids[i]] for i in inds) for inds in sets]
            for c in clauses:enc.add(*c,z)
            choices.append((t,clauses))
        allflags+=flags
        blocks.append(choices)
    enc.atmost(allflags,enc.k)
    if direct:
        # Exact lower-bound witnesses. Each selected group contributes
        # just one obstruction. No two contributions from one group.
        # Search high costs first; keep deterministic fixed clause cap.
        blocks.sort(key=lambda b:(-b[-1][0],sum(len(cs) for _,cs in b)))
        suffix=[0]*(len(blocks)+1)
        for i in reversed(range(len(blocks))):
            suffix[i]=suffix[i+1]+blocks[i][-1][0]
        left=512
        def visit(i,cost,clause):
            nonlocal left
            if not left:return
            if cost>enc.k:
                enc.add(*clause)
                left-=1
                return
            if i==len(blocks) or cost+suffix[i]<=enc.k:return
            for t,cs in reversed(blocks[i]):
                for c in cs:
                    visit(i+1,cost+t,clause+c)
                    if not left:return
            visit(i+1,cost,clause)
        visit(0,0,())
    return len(enc.cnf)-before

def solve(n,edges,k,counts,part,base,minimal,name,seconds,chunk,mode,batch):
    t=time.monotonic()
    if mode=="guard":
        out=v2.solve_fixed(n,edges,k,counts,part,base,minimal,name,seconds,chunk,
                           "guard",batch,.1)
        out["extra_clauses"]=0
        return out
    enc=old.build(n,edges,k,counts,part,base,minimal)
    orig,sides,jtruth,bearing,hits=old.template(n,edges,k,max(counts),base,minimal)
    extra=(cover_cuts(enc,edges,part,sides,hits) if mode=="cover" else
           projected_cover(enc,edges,part,hits,mode=="direct"))
    local=enc.cnf[len(orig.cnf):]
    built=time.monotonic()
    obj=v2.pool(name,(n,edges,k,max(counts),base,minimal,mode),orig.cnf,orig.max_var,batch)
    loaded=time.monotonic()
    ans,model,ld,sl,stats=obj.query(local,enc.max_var,built+seconds,chunk)
    out={"status":"TIMEOUT" if ans is None else "SAT" if ans else "UNSAT",
         "counts":list(counts),"assignment":list(part),
         "build_seconds":built-t,"load_seconds":loaded-built+ld,
         "solve_seconds":sl,"stats":stats,"engine":"fast-v4-"+mode,
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
    part,k,counts,name,seconds,chunk=task
    n,edges=old.sw.v1.CASES["l2260"]
    return solve(n,tuple(edges),k,counts,part,17,True,name,seconds,chunk,
        os.environ.get("PNP_FAST4_MODE","cover"),int(os.environ.get("PNP_FAST2_BATCH","16")))

def self_test(name):
    from itertools import combinations
    from pysat.solvers import Solver
    # Exhaustive truth of the added cover construction on a triangle:
    # every edge pair intersects, but all three require two centers.
    class Toy:
        n=3
        k=1
        def __init__(self):self.cnf=[];self.max_var=3
        def fresh(self):self.max_var+=1;return self.max_var
        def add(self,*xs):self.cnf.append(list(xs))
        def atmost(self,xs,b): 
            for c in combinations(xs,b+1):self.add(*(-x for x in c))
    toy=Toy()
    cover_cuts(toy,((0,1),(0,2),(1,2)),(0,0,0),[],[1,2,3])
    with Solver(name=name,bootstrap_with=toy.cnf) as s:
        for mask in range(8):
            assert s.solve(assumptions=[i+1 if mask&(1<<i) else -i-1 for i in range(3)])==bool(mask)
    # Exhaustively compare projected and original cover with ALL hit
    # assignments on small graphs and partitions, not just SAT status
    # of the enclosing circuit CNF.
    import itertools
    graph_cases=[(3,((0,1),(0,2),(1,2))),
                 (5,((0,1),(1,2),(2,3),(3,4),(0,4))),
                 (5,((0,1),(0,2),(0,3),(0,4)))]
    checks=0
    for n,edges in graph_cases:
        for part in ((0,)*n,tuple(i%2 for i in range(n)),tuple(range(n))):
            for k in range(1,4):
                formulas=[]
                for mode in ("cover","threshold","direct"):
                    toy=Toy();toy.n=n;toy.k=k;toy.max_var=len(edges)
                    hs=list(range(1,len(edges)+1))
                    if mode=="cover":cover_cuts(toy,edges,part,[],hs)
                    else:projected_cover(toy,edges,part,hs,mode=="direct")
                    formulas.append(Solver(name=name,bootstrap_with=toy.cnf))
                try:
                    for mask in range(1<<len(edges)):
                        ass=[i+1 if mask&(1<<i) else -i-1 for i in range(len(edges))]
                        results=[s.solve(assumptions=ass) for s in formulas]
                        assert len(set(results))==1,(edges,part,k,mask,results)
                        checks+=1
                finally:
                    for s in formulas:s.delete()
    print("PROJECTED COVER TRUTH TABLE OK",checks,flush=True)
    # Match the old CNF on every small range and partition, including
    # actual satisfiable circuits; verify all resulting full witnesses.
    sat=unsat=0
    for edges in (((0,1),),((0,1),(0,2),(1,2))):
        for part in ((0,0,0),(0,0,1),(0,1,0),(0,1,1),(0,1,2)):
            for k in (1,2):
                rs=range(3-(max(part)+1),3)
                for z in range(1,len(rs)+1):
                    for counts in combinations(rs,z):
                        enc=old.build(3,edges,k,counts,part,0,False)
                        with Solver(name=name,bootstrap_with=enc.cnf) as s:expected=s.solve()
                        for mode in ("threshold","direct"):
                            out=solve(3,edges,k,counts,part,0,False,name,10,2000,mode,4)
                            assert out["status"]==("SAT" if expected else "UNSAT"),(edges,part,k,counts,mode,out)
                            sat+=expected;unsat+=not expected
    assert sat and unsat
    for o in v2.POOLS.values():o.close()
    v2.POOLS.clear()
    print("FAST V4 COVER SELF TEST OK",{"sat":sat,"unsat":unsat},flush=True)

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
          "seconds":b.seconds,"engines":["cover","threshold","direct"]}),flush=True)
    known={}
    ctx=mp.get_context("spawn")
    for mode in ("cover","threshold","direct"):
        os.environ["PNP_FAST4_MODE"]=mode
        rows=[]
        start=time.monotonic()
        with cf.ProcessPoolExecutor(max_workers=b.jobs,mp_context=ctx) as pool:
            fs={pool.submit(direct,(part,b.top_count,rr,b.solver,b.seconds,b.chunk)):(part,rr)
                for part,rr in sample}
            for f in cf.as_completed(fs):
                part,rr=fs[f]
                out=f.result()
                st=out["status"]
                if st not in ("UNSAT","TIMEOUT","SAT"):raise RuntimeError(out)
                if st=="SAT":
                    print("[TARGET]",json.dumps(out),flush=True)
                    raise RuntimeError("SAT witness found; inspect before continuing")
                if mode=="cover":known[part,rr]=st
                rows.append((rr,out))
        wall=time.monotonic()-start
        done=sum(len(rr) for rr,o in rows if o["status"]=="UNSAT")
        print("[COMPARE]",json.dumps({"mode":mode,"wall_seconds":round(wall,3),
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
    os.environ["PNP_FAST2_BATCH"]=str(a.batch_size)
    if a.self_test:
        s=argparse.ArgumentParser()
        s.add_argument("--solver",default="cadical195")
        self_test(s.parse_args(rest).solver)
    else:benchmark(a,rest)

if __name__=="__main__":main()
