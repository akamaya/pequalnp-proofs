#!/usr/bin/env python3
"""Fast v2: bounded incremental fixed cubes and a clause-subset prefilter.

The v1 CNF, enumeration, fingerprint and checkpoint schema are unchanged.
A prefilter UNSAT implies full UNSAT because its clauses are literally a
subset of the full fixed-partition CNF. SAT/TIMEOUT must fall back to full.
In incremental mode each cube is guarded by a fresh assumption literal,
with all local auxiliary IDs renamed above the persistent base variables.
The guard is permanently disabled after each solve. A bounded pool of
fresh solvers prevents indefinite accumulation. No new mathematical cuts.
"""
import argparse
import concurrent.futures as cf
from collections import Counter, defaultdict
import functools
import hashlib
import json
import multiprocessing as mp
import os
from pathlib import Path
import random
import sqlite3
import sys
import time

import pnp_graph_partition_fast_v1 as old

ROOT=Path(__file__).resolve().parent
ENGINE_SHA=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
POOLS={}
ORIGINAL_DIRECT=old.direct

@functools.lru_cache(maxsize=8)
def bases(n,edges,k,m,base,minimal):
    orig,sides,jtruth,bearing,hits=old.template(n,edges,k,m,base,minimal)
    # All OR/AND selectors and support bits are allocated before v9's
    # expensive boundary-row evaluation. singleton_sides allocates its
    # first fresh variable in jtruth[0], after v19.build has finished.
    low=max(v for pair in orig.ands for sels,S in pair for v in sels+S)
    high=min(jtruth[0])
    if not low<high<=orig.max_var:
        raise ValueError("unexpected v19 variable allocation")
    # Clause deletion only: even if the variable layout changes, this
    # remains a relaxation. Do not drop any partition-specific clauses.
    reduced=[c for c in orig.cnf if all(abs(x)<=low or abs(x)>=high for x in c)]
    return orig,reduced

class Guarded:
    def __init__(self,name,baseclauses,basevars):
        from pysat.solvers import Solver
        self.sol=Solver(name=name,bootstrap_with=baseclauses)
        self.basevars=basevars
        self.nextvar=max(basevars,self.sol.nof_vars())
        self.uses=0

    def close(self):
        self.sol.delete()

    def query(self,local,maxvar,deadline,chunk):
        # Some solvers have extra internal variables. Recheck their
        # public maximum before allocating the next guarded namespace.
        first=max(self.nextvar,self.sol.nof_vars())
        g=first+1
        shift=g-self.basevars
        self.nextvar=g+max(0,maxvar-self.basevars)
        def rename(x):
            v=abs(x)
            if v<=self.basevars:return x
            return (v+shift) if x>0 else (x-shift)
        before=self.sol.accum_stats()
        t=time.monotonic()
        self.sol.append_formula([[-g]+[rename(x) for x in c] for c in local])
        loaded=time.monotonic()
        try:
            while True:
                self.sol.conf_budget(chunk)
                ans=self.sol.solve_limited(assumptions=[g])
                if ans is not None or time.monotonic()>=deadline:break
            model=None
            if ans is True:
                # Base variables retain their IDs. Map every local
                # variable back for a full witness, before disabling g.
                pos=set(x for x in self.sol.get_model() if x>0)
                model=[v if (v if v<=self.basevars else v+shift) in pos else -v
                       for v in range(1,maxvar+1)]
            after=self.sol.accum_stats()
            return ans,model,loaded-t,time.monotonic()-loaded,{
                x:y-before.get(x,0) for x,y in after.items()}
        finally:
            self.sol.add_clause([-g])
            self.uses+=1

def pool(name,key,clauses,basevars,batch):
    # A worker may encounter different exact-range maxima. Keep at most
    # two persistent instances per mode and close old ones explicitly.
    tag=(name,key)
    obj=POOLS.get(tag)
    if obj is not None and obj.uses>=batch:
        obj.close()
        del POOLS[tag]
        obj=None
    if obj is None:
        kind=key[-1]
        same=[k for k in POOLS if k[1][-1]==kind]
        if len(same)>=2:
            victim=same[0]
            POOLS.pop(victim).close()
        obj=Guarded(name,clauses,basevars)
        POOLS[tag]=obj
    return obj

def direct(task):
    part,k,counts,name,seconds,chunk=task
    mode=os.environ.get("PNP_FAST2_MODE","project")
    batch=int(os.environ.get("PNP_FAST2_BATCH","16"))
    ptime=float(os.environ.get("PNP_FAST2_PROJECT_SECONDS","0.10"))
    if mode=="fresh":
        return ORIGINAL_DIRECT(task)
    n,edges=old.sw.v1.CASES["l2260"]
    return solve_fixed(n,tuple(edges),k,counts,part,17,True,name,seconds,chunk,
                       mode,batch,ptime)

def solve_fixed(n,edges,k,counts,part,base,minimal,name,seconds,chunk,mode,batch,ptime):
    t=time.monotonic()
    enc=old.build(n,edges,k,counts,part,base,minimal)
    orig,reduced=bases(n,edges,k,max(counts),base,minimal)
    basevars=orig.max_var
    # old.build shallow-copies this exact immutable prefix.
    local=enc.cnf[len(orig.cnf):]
    if len(local)<1:
        raise ValueError("missing fixed cube clauses")
    key=(n,edges,k,max(counts),base,minimal)
    built=time.monotonic()
    deadline=built+seconds
    loads=solves=0.0
    stats={}
    pst="SKIP"
    pseconds=0.0
    def run(kind,clauses,end,c):
        nonlocal loads,solves
        a=time.monotonic()
        obj=pool(name,key+(kind,),clauses,basevars,batch)
        loads+=time.monotonic()-a
        ans,model,ld,sl,ss=obj.query(local,enc.max_var,end,c)
        loads+=ld
        solves+=sl
        for x,y in ss.items():stats[x]=stats.get(x,0)+y
        return ans,model
    ans=None
    model=None
    if mode=="project":
        a=time.monotonic()
        ans,model=run("project",reduced,min(deadline,a+ptime),min(chunk,200))
        pseconds=time.monotonic()-a
        pst="UNSAT" if ans is False else "SAT" if ans is True else "TIMEOUT"
    # Only false from the strict clause subset is sufficient.
    if ans is not False:
        ans,model=run("full",orig.cnf,deadline,chunk)
    out={"status":"TIMEOUT" if ans is None else "SAT" if ans else "UNSAT",
         "counts":list(counts),"assignment":list(part),
         "build_seconds":built-t,"load_seconds":loads,"solve_seconds":solves,
         "stats":stats,"engine":"fast-v2-"+mode,"engine_sha256":ENGINE_SHA,
         "projection_status":pst,"projection_seconds":pseconds,
         "base_clauses":len(orig.cnf),"projected_base_clauses":len(reduced)}
    if ans is True:
        w=enc.decode(model)
        chk=old.sw.v4.check_star(n,enc.masks,w,base,True)
        ok=(old.sw.v1.verify(n,enc.masks,w) and chk["valid"]
            and w["internal_or_gates"] in counts)
        out.update(witness=w,structure_check=chk,verified_full_truth_table=ok)
        if not ok:out["status"]="MODEL_INVALID"
    out["elapsed"]=time.monotonic()-t
    return out

def self_test(name):
    from pysat.solvers import Solver
    from itertools import combinations
    # Repeated conflicting cubes sharing auxiliary variable numbers.
    g=Guarded(name,[[1]],1)
    try:
        for local,expected in (([[2],[-2]],False),([[2]],True),
                               ([[-1]],False),([[-2]],True))*3:
            ans,model,*_=g.query(local,2,time.monotonic()+10,2000)
            assert ans is expected,(local,ans,expected)
            if ans:assert all(any(x in model for x in c) for c in [[1]]+local)
    finally:g.close()
    old.self_test(name)
    n,edges,k,base=3,((0,1),),1,2
    sat=unsat=0
    for part in ((0,0,0),(0,0,1),(0,1,0),(0,1,1),(0,1,2)):
        rs=range(n-(max(part)+1),3)
        for size in range(1,len(rs)+1):
            for counts in combinations(rs,size):
                enc=old.build(n,edges,k,counts,part,base,False)
                orig,red=bases(n,edges,k,max(counts),base,False)
                # A literal-subset check on the complete concrete formula.
                fullset={tuple(c) for c in enc.cnf}
                assert all(tuple(c) in fullset for c in red)
                with Solver(name=name,bootstrap_with=enc.cnf) as s:
                    expected=s.solve()
                for mode in ("guard","project"):
                    out=solve_fixed(n,edges,k,counts,part,base,False,name,10,2000,mode,4,.1)
                    assert out["status"]==("SAT" if expected else "UNSAT"),(part,counts,mode,out)
                    sat+=expected;unsat+=not expected
    for obj in POOLS.values():obj.close()
    POOLS.clear()
    print("FAST V2 SELF TEST OK",{"sat":sat,"unsat":unsat},flush=True)

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
          "seconds":b.seconds,"project_seconds":a.project_seconds}),flush=True)
    known={}
    ctx=mp.get_context("spawn")
    for mode in ("fresh","guard","project"):
        os.environ["PNP_FAST2_MODE"]=mode
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
                if mode=="fresh":known[part,rr]=st
                rows.append((rr,out))
        wall=time.monotonic()-start
        done=sum(len(rr) for rr,o in rows if o["status"]=="UNSAT")
        print("[COMPARE]",json.dumps({"mode":mode,"wall_seconds":round(wall,3),
              "calls":len(rows),"counts":dict(Counter(o["status"] for _,o in rows)),
              "exact_unsat":done,"exact_unsat_per_second":round(done/wall,3),
              "projection_counts":dict(Counter(o.get("projection_status","SKIP") for _,o in rows)),
              "sum_build":round(sum(o.get("build_seconds",0) for _,o in rows),3),
              "sum_load":round(sum(o.get("load_seconds",0) for _,o in rows),3),
              "sum_solve":round(sum(o.get("solve_seconds",0) for _,o in rows),3),
              "base_clauses":next((o["base_clauses"] for _,o in rows if "base_clauses" in o),None),
              "projected_base_clauses":next((o["projected_base_clauses"] for _,o in rows if "projected_base_clauses" in o),None)}),flush=True)

def main():
    p=argparse.ArgumentParser(add_help=False)
    p.add_argument("--engine",choices=("fresh","guard","project"),default="project")
    p.add_argument("--batch-size",type=int,default=16)
    p.add_argument("--project-seconds",type=float,default=.10)
    p.add_argument("--compare",type=int,default=0,metavar="SAMPLES_PER_GROUP")
    p.add_argument("--self-test",action="store_true")
    a,rest=p.parse_known_args()
    if a.batch_size<1 or a.project_seconds<=0 or a.compare<0:p.error("invalid fast v2 limits")
    os.environ.update(PNP_FAST2_MODE=a.engine,PNP_FAST2_BATCH=str(a.batch_size),
                      PNP_FAST2_PROJECT_SECONDS=str(a.project_seconds))
    if a.self_test:
        s=argparse.ArgumentParser()
        s.add_argument("--solver",default="cadical195")
        self_test(s.parse_args(rest).solver)
        return
    if a.compare:
        benchmark(a,rest)
        return
    if "--benchmark" in rest:p.error("use --compare for v2")
    # Reuse the unchanged production scheduler, validation, SQLite locks,
    # candidate IDs, and fingerprints. Worker results carry v2 provenance.
    # Spawn workers import this module and inherit the engine environment.
    old.direct=direct
    sys.argv=[sys.argv[0]]+rest
    print("[FAST V2]",json.dumps({"engine":a.engine,"batch":a.batch_size,
          "projection_seconds":a.project_seconds,"engine_sha256":ENGINE_SHA}),flush=True)
    old.main()

if __name__=="__main__":main()
