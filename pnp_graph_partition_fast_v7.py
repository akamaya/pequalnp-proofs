#!/usr/bin/env python3
"""Production v6 budget engine; benchmark compact support caps and OR links.

The tested v6 budget mode is unchanged. Compact replaces only redundant
guarded support-cap cardinalities by their equivalent short clauses.
Linked adds OR selector => same component label (implied by nonempty
child support and union). New checkpoints are separate and versioned.
Old v1 and v5-direct checkpoints are imported read-only.
"""
import argparse
import concurrent.futures as cf
from collections import Counter,defaultdict
from contextlib import ExitStack
import copy
import hashlib
import itertools
import json
import multiprocessing as mp
from pathlib import Path
import random
import sqlite3
import time
import fcntl
import pnp_graph_partition_fast_v1 as old
import pnp_graph_partition_fast_v2 as v2
import pnp_graph_partition_fast_v4 as v4
import pnp_graph_partition_fast_v5 as v5
import pnp_graph_partition_fast_v6 as v6

sw=old.sw
dbv2=old.dbv2
ENGINE_SHA=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()

def compact_cap(enc,raw,junk,slack,guard):
    if len(junk)!=2 or not raw or slack<0:
        raise ValueError("invalid compact cap")
    q=len(raw)
    if slack>=2:return
    tail=[] if guard is None else [-guard]
    # One junk plus every raw exceeds q only at slack zero.
    if slack==0:
        for j in junk:enc.add(*[-x for x in raw],-j,*tail)
    # Both junk plus q-1 raw exceeds q at slack zero; at slack
    # one, q raw are required. The present guard requires >=1 raw.
    take=max(1,q-1+slack)
    if take<=q:
        for xs in itertools.combinations(raw,take):
            enc.add(*[-x for x in xs],-junk[0],-junk[1],*tail)

def compact_build(n,edges,k,counts,part,base=17,minimal=True,linked=False):
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
                # Exact CNF for (any raw) => sum(raw+junk)<=q+slack.
                # Only two junk bits: enumerate the minimal violations.
                compact_cap(enc,raw,S[n:],slack_r,guard)
    if linked:
        # An active OR's child OR has nonempty support; union contains
        # it. The one-hot component labels must therefore agree.
        # Add the implied selector => equal-label clauses directly.
        for j,pair in enumerate(enc.ors):
            for sels,_ in pair:
                for i in range(j):
                    sel=sels[n+2+i]
                    for a in range(L):
                        enc.add(-sel,-ors[i][a],ors[j][a])
    return enc


def solve(n,edges,k,counts,part,base,minimal,name,seconds,chunk,mode,batch):
    if mode=="budget":
        out=v6.solve(n,edges,k,counts,part,base,minimal,name,seconds,chunk,"budget",batch)
        out.update(engine="fast-v7-budget",engine_sha256=ENGINE_SHA)
        return out
    t=time.monotonic()
    enc=compact_build(n,edges,k,counts,part,base,minimal,mode=="linked")
    orig,sides,jtruth,bearing,hits=old.template(n,edges,k,max(counts),base,minimal)
    v4.projected_cover(enc,edges,part,hits,True)
    local=enc.cnf[len(orig.cnf):]
    built=time.monotonic()
    obj=v2.pool(name,(n,edges,k,max(counts),base,minimal,"v7-"+mode),orig.cnf,orig.max_var,batch)
    loaded=time.monotonic()
    ans,model,ld,sl,stats=obj.query(local,enc.max_var,built+seconds,chunk)
    out={"status":"TIMEOUT" if ans is None else "SAT" if ans else "UNSAT",
         "counts":list(counts),"assignment":list(part),
         "build_seconds":built-t,"load_seconds":loaded-built+ld,
         "solve_seconds":sl,"stats":stats,"engine":"fast-v7-"+mode,
         "engine_sha256":ENGINE_SHA,"extra_clauses":len(local),
         "base_clauses":len(orig.cnf)}
    if ans is True:
        pos=set(model)
        if not all(any(x in pos for x in c) for c in enc.cnf):
            raise ValueError("model does not satisfy concrete CNF")
        w=enc.decode(model)
        chk=sw.v4.check_star(n,enc.masks,w,base,True)
        ok=sw.v1.verify(n,enc.masks,w) and chk["valid"] and w["internal_or_gates"] in counts
        out.update(witness=w,structure_check=chk,verified_full_truth_table=ok)
        if not ok:out["status"]="MODEL_INVALID"
    out["elapsed"]=time.monotonic()-t
    return out

def direct(task):
    part,k,counts,name,seconds,chunk,mode,batch=task
    n,edges=sw.v1.CASES["l2260"]
    return solve(n,tuple(edges),k,counts,part,17,True,name,seconds,chunk,mode,batch)

def newkey(n,edges,k,r,parts,mode):
    h=hashlib.sha256()
    for s in (old.key(n,edges,k,r,parts,True),v2.ENGINE_SHA,v4.ENGINE_SHA,
              v5.ENGINE_SHA,v6.ENGINE_SHA,ENGINE_SHA,mode):
        h.update(s.encode()+b"\0")
    return h.hexdigest()

def import_v5(db,path,key,parts):
    if not path.exists():return 0
    seed=sqlite3.connect(path.resolve().as_uri()+"?mode=ro",uri=True)
    try:
        if seed.execute("SELECT fingerprint FROM meta WHERE id=1").fetchone()!=(key,):
            raise ValueError("v5 seed fingerprint mismatch")
        states=dbv2.load(seed,parts)
        if any(s not in ("UNSAT","TIMEOUT") for s in states.values()):
            raise ValueError("inspect prior SAT/error")
        n=0
        with db:
            for idx,st,payload in seed.execute("SELECT id,status,payload FROM results"):
                out=json.loads(payload)
                out["inherited_from_fast_v5_direct"]=True
                cur=db.execute("INSERT INTO results VALUES(?,?,?) ON CONFLICT(id) DO UPDATE SET status=excluded.status,payload=excluded.payload WHERE results.status='TIMEOUT' AND excluded.status='UNSAT'",
                    (idx,st,json.dumps(out,separators=(",",":"))))
                n+=cur.rowcount
        return n
    finally:seed.close()

def self_test(name):
    from pysat.solvers import Solver
    # Exhaustively verify the compressed support-cap clause encoding.
    class Toy:
        def __init__(self):self.cnf=[]
        def add(self,*xs):self.cnf.append(list(xs))
    checks=0
    for q in range(1,12):
        for slack in (0,1,2):
            for guard in (None,q+3,-q-3):
                enc=Toy()
                compact_cap(enc,list(range(1,q+1)),[q+1,q+2],slack,guard)
                for mask in range(1<<(q+3)):
                    def val(v):
                        return bool(mask&(1<<(abs(v)-1)))==(v>0)
                    expected=((guard is not None and not val(guard)) or
                              not any(val(v) for v in range(1,q+1)) or
                              sum(val(v) for v in range(1,q+3))<=q+slack)
                    assert all(any(val(x) for x in c) for c in enc.cnf)==expected
                    checks+=1
    print("COMPACT CAP TRUTH TABLE OK",checks,flush=True)
    v6.self_test(name)
    sat=unsat=0
    for n,edges in ((3,((0,1),)),(3,((0,1),(0,2),(1,2))),
                    (4,((0,1),(1,2),(2,3)))):
        def parts(p):
            if len(p)==n:
                yield p
                return
            for a in range(max(p)+2):yield from parts(p+(a,))
        for part in parts((0,)):
            for k in (1,2):
                rs=range(n-(max(part)+1),min(3,n-1)+1)
                for z in range(1,len(rs)+1):
                    for counts in itertools.combinations(rs,z):
                        enc=v6.budget_build(n,edges,k,counts,part,0,False)
                        v4.projected_cover(enc,edges,part,old.template(n,edges,k,max(counts),0,False)[4],True)
                        with Solver(name=name,bootstrap_with=enc.cnf) as s:expected=s.solve()
                        for mode in ("compact","linked"):
                            out=solve(n,edges,k,counts,part,0,False,name,10,2000,mode,4)
                            assert out["status"]==("SAT" if expected else "UNSAT"),(part,counts,mode,out)
                            sat+=expected;unsat+=not expected
    assert sat and unsat
    for o in v2.POOLS.values():o.close()
    v2.POOLS.clear()
    print("FAST V7 SELF TEST OK",{"sat":sat,"unsat":unsat},flush=True)

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
          "seconds":b.seconds,"engines":["budget","compact","linked"]}),flush=True)
    known={}
    ctx=mp.get_context("spawn")
    configs=[(mode,b.solver) for mode in ("budget","compact","linked")]
    for mode,name in configs:
        if not v6.available(name):
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
                if mode=="budget":known[part,rr]=st
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
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--engine",choices=("budget","compact","linked"),default="budget")
    p.add_argument("--compare",type=int,default=0)
    p.add_argument("--batch-size",type=int,default=16)
    p.add_argument("--self-test",action="store_true")
    a,rest=p.parse_known_args()
    if a.batch_size<1 or a.compare<0:p.error("invalid limits")
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
            path=root/f"l2260-fast7-{a.engine}-k{k}-r{r}.sqlite3"
            lock=stack.enter_context(open(str(path)+".lock","a"))
            fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
            db=dbv2.open_db(path,newkey(n,edges,k,r,parts,a.engine));stack.callback(db.close)
            imported=v5.import_seed(db,root/f"l2260-fast-strong-k{k}-r{r}.sqlite3",
                old.key(n,edges,k,r,parts,True),parts)
            imported+=import_v5(db,root/f"l2260-fast5-direct-k{k}-r{r}.sqlite3",
                v5.newkey(n,edges,k,r,parts,"direct"),parts)
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
                while len(fs)<a.jobs and time.monotonic()-start+max(5,a.seconds+2)<a.wall_seconds:
                    task=next(todo,None)
                    if task is None:break
                    p,rr=task
                    fs[pool.submit(direct,(p,k,rr,a.solver,a.seconds,a.chunk,a.engine,a.batch_size))]=task
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
