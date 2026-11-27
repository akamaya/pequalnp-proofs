#!/usr/bin/env python3
"""Production direct cover (v4) plus experimental two-junk group cuts.

Old checkpoint files are never written. New DBs are keyed by all
engine sources and the selected mode. Old validated rows are imported.
The group cuts are consequences of effective singleton locality:
each junk AND's exclusive first-merge edges belong to one unordered
block pair. Its hit edges are bipartite; within a same-block group,
one junk cannot remove an odd cycle. No assumption on junk truth or
new graph bound is needed beyond the existing fixed CNF.
"""
import argparse
import concurrent.futures as cf
from collections import Counter, defaultdict
from contextlib import ExitStack
import functools
import hashlib
import itertools
import json
import multiprocessing as mp
import os
from pathlib import Path
import random
import sqlite3
import time
import fcntl

import pnp_graph_partition_fast_v1 as old
import pnp_graph_partition_fast_v2 as v2
import pnp_graph_partition_fast_v4 as v4

sw=old.sw
dbv2=old.dbv2
ENGINE_SHA=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()

@functools.lru_cache(maxsize=32768)
def group_cost(edges):
    """Exact ordinary cover and minimum residual after one bipartite hit."""
    vs=sorted({v for e in edges for v in e})
    ix={v:i for i,v in enumerate(vs)}
    es=[(ix[u],ix[v]) for u,v in edges]
    incident=[0]*len(vs)
    for i,(u,v) in enumerate(es):
        incident[u]|=1<<i
        incident[v]|=1<<i
    @functools.lru_cache(None)
    def tau(mask):
        if not mask:return 0
        i=(mask&-mask).bit_length()-1
        u,v=es[i]
        return 1+min(tau(mask&~incident[u]),tau(mask&~incident[v]))
    full=tau((1<<len(es))-1)
    # Extend the exclusive left/right singleton sets to a full cut.
    # Removing all crossing edges is an optimistic relaxation of hits.
    residual=full
    for mask in range(1<<(len(vs)-1)):
        remaining=sum(1<<i for i,(u,v) in enumerate(es)
                      if ((mask>>u)&1)==((mask>>v)&1))
        residual=min(residual,tau(remaining))
        if residual==0:break
    return full,residual

def junk_group_cuts(enc,edges,part,sides):
    before=len(enc.cnf)
    groups=defaultdict(list)
    for i,g in enumerate(v4.group_edges(edges,part)):groups[g].append(i)
    keys=sorted(groups)
    costs={g:group_cost(tuple(edges[i] for i in groups[g])) for g in keys}
    choices=[]
    for A,B in sides[:2]:
        # None denotes no positive edge first merge; selecting a group
        # with no actual hits is also allowed (a safe relaxation).
        G={g:enc.fresh() for g in [None]+keys}
        enc.add(*G.values())
        enc.atmost(list(G.values()),1)
        for g in keys:
            for i in groups[g]:
                u,v=edges[i]
                enc.add(-A[u],-B[v],A[v],B[u],G[g])
                enc.add(-A[v],-B[u],A[u],B[v],G[g])
        choices.append(G)
    total=sum(c[0] for c in costs.values())
    for g,h in itertools.product([None]+keys,repeat=2):
        lower=total
        for q in {g,h}-{None}:
            # With two junk hits in a group, zero is a safe lower
            # bound. With one, exact best bipartite removal is used.
            c,d=costs[q]
            lower-=c
            if g!=h:lower+=d
        if lower>enc.k:enc.add(-choices[0][g],-choices[1][h])
    return len(enc.cnf)-before

def solve(n,edges,k,counts,part,base,minimal,name,seconds,chunk,mode,batch):
    if mode=="direct":
        out=v4.solve(n,edges,k,counts,part,base,minimal,name,seconds,chunk,"direct",batch)
        out["engine"]="fast-v5-direct"
        out["engine_sha256"]=ENGINE_SHA
        return out
    t=time.monotonic()
    enc=old.build(n,edges,k,counts,part,base,minimal)
    orig,sides,jtruth,bearing,hits=old.template(n,edges,k,max(counts),base,minimal)
    extra=v4.projected_cover(enc,edges,part,hits,mode=="group")
    extra+=junk_group_cuts(enc,edges,part,sides)
    local=enc.cnf[len(orig.cnf):]
    built=time.monotonic()
    obj=v2.pool(name,(n,edges,k,max(counts),base,minimal,"v5-"+mode),orig.cnf,orig.max_var,batch)
    loaded=time.monotonic()
    ans,model,ld,sl,stats=obj.query(local,enc.max_var,built+seconds,chunk)
    out={"status":"TIMEOUT" if ans is None else "SAT" if ans else "UNSAT",
         "counts":list(counts),"assignment":list(part),
         "build_seconds":built-t,"load_seconds":loaded-built+ld,
         "solve_seconds":sl,"stats":stats,"engine":"fast-v5-"+mode,
         "engine_sha256":ENGINE_SHA,"extra_clauses":extra,
         "base_clauses":len(orig.cnf)}
    if ans is True:
        pos=set(model)
        if not all(any(x in pos for x in c) for c in enc.cnf):
            raise ValueError("model does not satisfy concrete CNF")
        w=enc.decode(model)
        chk=sw.v4.check_star(n,enc.masks,w,base,True)
        ok=(sw.v1.verify(n,enc.masks,w) and chk["valid"]
            and w["internal_or_gates"] in counts)
        out.update(witness=w,structure_check=chk,verified_full_truth_table=ok)
        if not ok:out["status"]="MODEL_INVALID"
    out["elapsed"]=time.monotonic()-t
    return out

def direct(task):
    part,k,counts,name,seconds,chunk=task
    n,edges=sw.v1.CASES["l2260"]
    return solve(n,tuple(edges),k,counts,part,17,True,name,seconds,chunk,
        os.environ.get("PNP_FAST5_MODE","direct"),int(os.environ.get("PNP_FAST2_BATCH","16")))

def newkey(n,edges,k,r,parts,mode):
    h=hashlib.sha256()
    for s in (old.key(n,edges,k,r,parts,True),ENGINE_SHA,v2.ENGINE_SHA,v4.ENGINE_SHA,mode):
        h.update(s.encode()+b"\0")
    return h.hexdigest()

def import_seed(db,path,expected,parts):
    if not path.exists():return 0
    seed=sqlite3.connect(path.resolve().as_uri()+"?mode=ro",uri=True)
    try:
        if seed.execute("SELECT fingerprint FROM meta WHERE id=1").fetchone()!=(expected,):
            raise ValueError("v1 seed fingerprint mismatch")
        states=dbv2.load(seed,parts)
        if any(s not in ("UNSAT","TIMEOUT") for s in states.values()):
            raise ValueError("inspect previous SAT/error before import")
        n=0
        with db:
            for idx,st,payload in seed.execute("SELECT id,status,payload FROM results"):
                out=json.loads(payload)
                out["inherited_from_fast_v1"]=True
                cur=db.execute("INSERT INTO results VALUES(?,?,?) ON CONFLICT(id) DO UPDATE SET status=excluded.status,payload=excluded.payload WHERE results.status='TIMEOUT' AND excluded.status='UNSAT'",
                    (idx,st,json.dumps(out,separators=(",",":"))))
                n+=cur.rowcount
        return n
    finally:seed.close()

def self_test(name):
    from pysat.solvers import Solver
    from itertools import combinations
    import tempfile
    v4.self_test(name)
    assert group_cost(((0,1),(0,2),(1,2)))==(2,1)
    assert group_cost(((0,1),(1,2),(2,3),(3,4),(0,4)))==(3,1)
    assert group_cost(((0,1),(0,2),(0,3)))==(1,0)
    sat=unsat=0
    for edges in (((0,1),),((0,1),(0,2),(1,2))):
        for part in ((0,0,0),(0,0,1),(0,1,0),(0,1,1),(0,1,2)):
            for k in (1,2):
                rs=range(3-(max(part)+1),3)
                for z in range(1,len(rs)+1):
                    for counts in combinations(rs,z):
                        enc=old.build(3,edges,k,counts,part,0,False)
                        with Solver(name=name,bootstrap_with=enc.cnf) as s:expected=s.solve()
                        for mode in ("group","group-threshold"):
                            out=solve(3,edges,k,counts,part,0,False,name,10,2000,mode,4)
                            assert out["status"]==("SAT" if expected else "UNSAT"),(edges,part,k,counts,mode,out)
                            sat+=expected;unsat+=not expected
    for o in v2.POOLS.values():o.close()
    v2.POOLS.clear()
    with tempfile.TemporaryDirectory() as td:
        p=Path(td)/"old.db";q=Path(td)/"new.db"
        parts=[(0,0,1),(0,1,2)]
        seed=dbv2.open_db(p,"old")
        dbv2.save(seed,1,{"status":"UNSAT","partition":1,"assignment":[0,0,1]})
        dbv2.save(seed,2,{"status":"TIMEOUT"})
        seed.close()
        dest=dbv2.open_db(q,"new")
        assert import_seed(dest,p,"old",parts)==2
        assert import_seed(dest,p,"old",parts)==0
        assert dbv2.load(dest,parts)=={1:"UNSAT",2:"TIMEOUT"}
        dbv2.save(dest,2,{"status":"UNSAT","partition":2,"assignment":[0,1,2]})
        assert import_seed(dest,p,"old",parts)==0
        assert dbv2.load(dest,parts)=={1:"UNSAT",2:"UNSAT"}
        dest.close()
    print("FAST V5 GROUP AND CHECKPOINT SELF TEST OK",{"sat":sat,"unsat":unsat},flush=True)

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
          "seconds":b.seconds,"engines":["direct","group","group-threshold"]}),flush=True)
    known={}
    ctx=mp.get_context("spawn")
    for mode in ("direct","group","group-threshold"):
        os.environ["PNP_FAST5_MODE"]=mode
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
                if mode=="direct":known[part,rr]=st
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
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--engine",choices=("direct","group","group-threshold"),default="direct")
    p.add_argument("--compare",type=int,default=0)
    p.add_argument("--batch-size",type=int,default=16)
    p.add_argument("--self-test",action="store_true")
    a,rest=p.parse_known_args()
    if a.batch_size<1 or a.compare<0:p.error("invalid limits")
    os.environ["PNP_FAST2_BATCH"]=str(a.batch_size)
    os.environ["PNP_FAST5_MODE"]=a.engine
    if a.self_test:
        s=argparse.ArgumentParser()
        s.add_argument("--solver",default="cadical195")
        self_test(s.parse_args(rest).solver)
        return
    if a.compare:
        benchmark(a,rest)
        return
    p=argparse.ArgumentParser()
    p.add_argument("--top-count",type=int,default=5)
    p.add_argument("--or-min",type=int,default=8)
    p.add_argument("--or-max",type=int,default=10)
    p.add_argument("--jobs",type=int,default=8)
    p.add_argument("--seconds",type=float,default=2)
    p.add_argument("--wall-seconds",type=float,default=1800)
    p.add_argument("--chunk",type=int,default=2000)
    p.add_argument("--solver",default="cadical195")
    a=p.parse_args(rest,namespace=a)
    k,lo,hi=a.top_count,a.or_min,a.or_max
    if k<1 or not 0<=lo<=hi or 2*k+1+hi>21 or min(a.jobs,a.seconds,a.wall_seconds,a.chunk)<=0:
        p.error("invalid limits")
    start=time.monotonic()
    n,edges=sw.v1.CASES["l2260"]
    allparts={}
    lookup=defaultdict(dict)
    for r in range(lo,hi+1):
        parts,generic=sw.candidates(n,edges,k,r)
        if (k,r) in dbv2.EXPECTED and (generic,len(parts))!=dbv2.EXPECTED[k,r]:
            raise ValueError("enumeration cross-check failed")
        allparts[r]=parts
        for idx,part in enumerate(parts,1):lookup[part][r]=idx
    print("[PARTITIONS]",json.dumps({"exact":{r:len(p) for r,p in allparts.items()},
        "union":len(lookup),"enumeration_seconds":time.monotonic()-start}),flush=True)
    ctx=mp.get_context("spawn")
    print("[ENGINE]",json.dumps({"engine":a.engine,"engine_sha256":ENGINE_SHA}),flush=True)
    root=Path("sat-results");root.mkdir(exist_ok=True)
    with ExitStack() as stack:
        dbs={};states={}
        for r,parts in allparts.items():
            path=root/f"l2260-fast5-{a.engine}-k{k}-r{r}.sqlite3"
            lock=stack.enter_context(open(str(path)+".lock","a"))
            fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
            db=dbv2.open_db(path,newkey(n,edges,k,r,parts,a.engine));stack.callback(db.close)
            imported=import_seed(db,root/f"l2260-fast-strong-k{k}-r{r}.sqlite3",
                old.key(n,edges,k,r,parts,True),parts)
            imported+=old.import_old(db,root/f"l2260-fixed-strong-k{k}-r{r}.sqlite3",
                old.key(n,edges,k,r,parts),parts)
            dbs[r]=db;states[r]=dbv2.load(db,parts)
            print("[CHECKPOINT]",json.dumps({"r":r,"imported":imported,
                "unsat":sum(s=="UNSAT" for s in states[r].values()),"total":len(parts)}),flush=True)
        if any(s in ("SAT","ERROR","MODEL_INVALID") for ss in states.values() for s in ss.values()):
            raise ValueError("inspect previous SAT/error before resume")
        tasks=[]
        for p,ids in lookup.items():
            rr=tuple(r for r,idx in ids.items() if states[r].get(idx)!="UNSAT")
            if rr:tasks.append((p,rr))
        tasks.sort(key=lambda t:(all(lookup[t[0]][r] in states[r] for r in t[1]),max(t[1]),max(t[0]),t[0]))
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
