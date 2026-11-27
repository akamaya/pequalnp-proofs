#!/usr/bin/env python3
"""Adaptive prefix cubes over a reduced multi-valued decision diagram.

The diagram admits exactly the graph-bound candidate partitions for
one block count. A single prefix UNSAT excludes every admitted leaf
under that prefix. TIMEOUT splits the prefix, never excludes it.
Reuses the incremental component/first-merge encoding.
"""
import argparse
from collections import defaultdict, deque
import hashlib
import json
import multiprocessing as mp
from pathlib import Path
import queue
import time
import fcntl

import pnp_graph_partition_incremental_v1 as inc

sw=inc.sw
dbv2=inc.dbv2

def diagram(parts):
    """Bottom-up suffix sharing. Node 0 is the accepting terminal."""
    if not parts:raise ValueError("empty partition domain")
    n=len(parts[0])
    layer={tuple(p):0 for p in parts}
    nodes=[None]
    for i in range(n-1,-1,-1):
        parents=defaultdict(list)
        for prefix,child in layer.items():
            parents[prefix[:-1]].append((prefix[-1],child))
        layer={}
        unique={}
        for prefix,children in parents.items():
            key=tuple(sorted(children))
            if key not in unique:
                unique[key]=len(nodes)
                nodes.append((i,key))
            layer[prefix]=unique[key]
    return nodes,layer[()]

def accepts(d,part):
    nodes,node=d
    for i,a in enumerate(part):
        if not node or nodes[node][0]!=i:return False
        children=dict(nodes[node][1])
        if a not in children:return False
        node=children[a]
    return node==0

def encode_diagram(enc,raw,d):
    """Root enabled; enabled node must follow its chosen label.
    Because each raw label vector is one-hot, this is equivalent to
    existence of a root-to-accept path for that complete assignment.
    """
    nodes,root=d
    z=[None]+[enc.fresh() for _ in nodes[1:]]
    enc.add(z[root])
    for j,(i,arcs) in enumerate(nodes[1:],1):
        c=dict(arcs)
        for a,x in enumerate(raw[i]):
            if a not in c:enc.add(-z[j],-x)
            elif c[a]:enc.add(-z[j],-x,z[c[a]])
    return len(nodes)-1

def common_prefix(parts,ids):
    a,b=parts[ids[0]-1],parts[ids[-1]-1]
    i=0
    while i<len(a) and a[i]==b[i]:i+=1
    return a[:i]

def group_prefix(parts,ids,depth):
    buckets=defaultdict(list)
    for idx in ids:
        p=parts[idx-1]
        buckets[(max(p)+1,p[:depth])].append(idx)
    return [(b,common_prefix(parts,xs),tuple(xs))
            for (b,_),xs in sorted(buckets.items())]

def worker(inq,outq,config,diagrams):
    from pysat.solvers import Solver
    k,lo,hi,name,seconds,leaf_seconds,chunk,mode=config
    n,edges=sw.v1.CASES["l2260"]
    sol=None
    b0=None
    try:
        while True:
            task=inq.get()
            if task is None:return
            job,b,prefix=task
            t=time.monotonic()
            if b!=b0:
                if sol is not None:sol.delete()
                enc,raw,meta=inc.build(n,edges,k,lo,hi,b,mode)
                d=diagrams[b]
                meta["mdd_nodes"]=encode_diagram(enc,raw,d)
                meta["mdd_arcs"]=sum(len(x[1]) for x in d[0][1:])
                meta["variables"]=enc.max_var
                meta["clauses"]=len(enc.cnf)
                sol=Solver(name=name,bootstrap_with=enc.cnf)
                b0=b
            ass=inc.assume(raw,prefix)
            limit=leaf_seconds if len(prefix)==n else seconds
            before=sol.accum_stats()
            st=time.monotonic()
            while True:
                sol.conf_budget(chunk)
                answer=sol.solve_limited(assumptions=ass)
                if answer is not None or time.monotonic()-st>=limit:break
            after=sol.accum_stats()
            out={**meta,"prefix":list(prefix),"solver":name,
                 "status":"TIMEOUT" if answer is None else "SAT" if answer else "UNSAT",
                 "solve_seconds":round(time.monotonic()-st,3),
                 "wall_seconds":round(time.monotonic()-t,3),
                 "stats":{x:y-before.get(x,0) for x,y in after.items()}}
            if answer is False:
                core=sol.get_core()
                if core is None:core=ass
                if not set(core)<=set(ass):raise ValueError("unexpected core")
                sol.add_clause([-x for x in core])
                out["core_size"]=len(core)
                out["core_prefix_positions"]=[i for i,x in enumerate(ass) if x in core]
            elif answer is True:
                model=sol.get_model()
                pos={x for x in model if x>0}
                part=tuple(next(a for a,x in enumerate(P) if x in pos) for P in raw)
                w=enc.decode(model)
                chk=sw.v4.check_star(n,enc.masks,w,17,True)
                ok=(accepts(diagrams[b],part) and part[:len(prefix)]==prefix and
                    sw.v1.verify(n,enc.masks,w) and chk["valid"] and
                    lo<=w["internal_or_gates"]<=hi)
                out.update(witness=w,structure_check=chk,assignment=list(part),
                           verified_full_truth_table=ok)
                if not ok:out["status"]="MODEL_INVALID"
            outq.put((job,out))
    except BaseException as e:
        outq.put((None,{"status":"ERROR","error":repr(e)}))
    finally:
        if sol is not None:sol.delete()

def self_test(name):
    from itertools import product
    from pysat.solvers import Solver
    inc.self_test(name)
    # Independent one-hot formula: verify the exact MDD language.
    class Enc:
        def __init__(self):self.max_var=0;self.cnf=[]
        def fresh(self):self.max_var+=1;return self.max_var
        def add(self,*xs):self.cnf.append(list(xs))
        def atmost(self,xs,k):
            assert k==1
            for i,x in enumerate(xs):
                for y in xs[:i]:self.add(-x,-y)
    for parts in (
        [(0,0,1),(0,1,0)],
        [(0,0,0),(0,1,1),(1,0,0),(1,1,1)],
        [(0,1,2,2),(0,1,2,1),(0,1,0,2),(0,0,1,2)]):
        n=len(parts[0]);b=max(max(p) for p in parts)+1
        d=diagram(parts);enc=Enc()
        raw=[inc.onehot(enc,b) for _ in range(n)]
        encode_diagram(enc,raw,d)
        with Solver(name=name,bootstrap_with=enc.cnf) as sol:
            for p in product(range(b),repeat=n):
                want=p in parts
                assert accepts(d,p)==want,(parts,p)
                assert sol.solve(assumptions=inc.assume(raw,p))==want,(parts,p)
            for depth in range(n+1):
                for pre in product(range(b),repeat=depth):
                    want=any(p[:depth]==pre for p in parts)
                    assert sol.solve(assumptions=inc.assume(raw,pre))==want,(parts,pre)
    # Small real formulas: a grouped prefix is SAT iff at least one
    # exact partition is SAT. Includes the known exact-v1 SAT witness.
    n=3;edges=[(0,1)];k=1;base=2
    parts=[(0,0,1),(0,1,0),(0,1,1)]
    for lo,hi in ((0,0),(1,2),(2,2)):
        d=diagram(parts)
        enc,raw,_=inc.build(n,edges,k,lo,hi,2,minimal=False,base=base)
        encode_diagram(enc,raw,d)
        with Solver(name=name,bootstrap_with=enc.cnf) as sol:
            expected={}
            for p in parts:
                ref,rr,_=inc.build(n,edges,k,lo,hi,2,minimal=False,base=base)
                with Solver(name=name,bootstrap_with=ref.cnf) as s:
                    expected[p]=s.solve(assumptions=inc.assume(rr,p))
            for pre in ((),(0,),(0,0),(0,1),*parts):
                want=any(v and p[:len(pre)]==pre for p,v in expected.items())
                got=sol.solve(assumptions=inc.assume(raw,pre))
                assert got==want,(lo,hi,pre,got,want)
                if got is False:
                    ass=inc.assume(raw,pre)
                    core=sol.get_core()
                    sol.add_clause([-x for x in (ass if core is None else core)])
    print("BATCH MDD SELF TEST OK",flush=True)

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--top-count",type=int,default=7)
    ap.add_argument("--or-min",type=int,default=6)
    ap.add_argument("--or-max",type=int,default=6)
    ap.add_argument("--prefix-depth",type=int,default=8)
    ap.add_argument("--jobs",type=int,default=8)
    ap.add_argument("--seconds",type=float,default=2,help="per non-leaf prefix")
    ap.add_argument("--leaf-seconds",type=float,default=15)
    ap.add_argument("--wall-seconds",type=float,default=600)
    ap.add_argument("--chunk",type=int,default=3000)
    ap.add_argument("--solver",default="cadical195")
    ap.add_argument("--mode",choices=("compact","canonical"),default="compact")
    ap.add_argument("--seed-v2",type=Path)
    ap.add_argument("--checkpoint",type=Path)
    ap.add_argument("--self-test",action="store_true")
    a=ap.parse_args()
    if a.self_test:self_test(a.solver);return
    k,lo,hi=a.top_count,a.or_min,a.or_max
    n,edges=sw.v1.CASES["l2260"]
    if (k<1 or not 0<=lo<=hi or 2*k+1+hi>21 or
        not 0<=a.prefix_depth<=n or min(a.jobs,a.chunk)<1 or
        min(a.seconds,a.leaf_seconds,a.wall_seconds)<=0):
        ap.error("invalid limits")
    if a.seed_v2 and lo!=hi:ap.error("v2 seed only for exact OR count")
    start=time.monotonic()
    parts,generic=sw.candidates(n,edges,k,hi)
    if (k,hi) in dbv2.EXPECTED and (generic,len(parts))!=dbv2.EXPECTED[k,hi]:
        raise ValueError("enumeration cross-check failed")
    # Fixed full domain, independent of resume state; an inherited
    # UNSAT never becomes an unverified SAT clause in the new formula.
    byb=defaultdict(list)
    for p in parts:byb[max(p)+1].append(p)
    diagrams={b:diagram(ps) for b,ps in sorted(byb.items())}
    if not all(accepts(diagrams[max(p)+1],p) for p in parts):
        raise ValueError("MDD dropped candidate")
    oldkey=inc.fingerprint(Path(__file__).resolve().parent,n,edges,k,hi,a.mode,parts)
    h=hashlib.sha256(json.dumps([oldkey,lo,hi]).encode())
    h.update(Path(inc.__file__).read_bytes())
    h.update(Path(__file__).read_bytes())
    path=a.checkpoint or Path(f"sat-results/l2260-graph-batch-k{k}-r{lo}-{hi}-{a.mode}.sqlite3")
    path.parent.mkdir(parents=True,exist_ok=True)
    print("[DOMAIN]",json.dumps({"partitions":len(parts),"generic":generic,
          "by_blocks":{b:len(ps) for b,ps in sorted(byb.items())},
          "mdd_nodes":{b:len(d[0])-1 for b,d in diagrams.items()},
          "build_seconds":round(time.monotonic()-start,3)}),flush=True)
    with open(str(path)+".lock","a") as lock:
        fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
        db=dbv2.open_db(path,h.hexdigest())
        ctx=mp.get_context("spawn")
        outq=ctx.Queue()
        workers=[]
        try:
            imported=inc.import_v2(db,a.seed_v2,oldkey,parts) if a.seed_v2 else 0
            states=dbv2.load(db,parts)
            pending=[i for i in range(1,len(parts)+1) if states.get(i)!="UNSAT"]
            todo=deque(group_prefix(parts,pending,a.prefix_depth))
            prior=len(parts)-len(pending)
            print("[CONFIG]",json.dumps({"pending":len(pending),"prior_unsat":prior,
                "imported":imported,"initial_groups":len(todo),"jobs":a.jobs,
                "or_min":lo,"or_max":hi,"prefix_depth":a.prefix_depth,
                "seconds":a.seconds,"leaf_seconds":a.leaf_seconds,
                "wall_limit":a.wall_seconds,"checkpoint":str(path)}),flush=True)
            unsat=prior
            calls=splits=batched=leaf_timeouts=0
            errors=[]
            stop="SAT" in states.values()
            active={}
            next_job=0
            config=(k,lo,hi,a.solver,a.seconds,a.leaf_seconds,a.chunk,a.mode)
            def dispatch(w):
                nonlocal next_job
                if stop or not todo or time.monotonic()-start>=a.wall_seconds:return
                b,pre,ids=todo.popleft()
                next_job+=1
                active[next_job]=(w,b,pre,ids)
                workers[w][1].put((next_job,b,pre))
            for w in range(min(a.jobs,len(todo)) if not stop else 0):
                q=ctx.Queue(maxsize=1)
                p=ctx.Process(target=worker,args=(q,outq,config,diagrams),daemon=True)
                p.start()
                workers.append((p,q))
                dispatch(w)
            last=time.monotonic()
            while active and not stop and time.monotonic()-start<a.wall_seconds:
                try:job,out=outq.get(timeout=min(1,max(.01,a.wall_seconds-(time.monotonic()-start))))
                except queue.Empty:
                    if any(not workers[w][0].is_alive() for w,b,pre,ids in active.values()):
                        errors.append("worker exited without result");break
                    continue
                if job is None:errors.append(out["error"]);break
                if job not in active:raise ValueError("unknown worker result")
                w,b,pre,ids=active.pop(job)
                calls+=1
                st=out["status"]
                if st=="UNSAT":
                    # The entire prefix is UNSAT, not just a sampled
                    # partition. Record every still-pending leaf.
                    rows=[]
                    for idx in ids:
                        result={**out,"partition":idx,"assignment":list(parts[idx-1]),
                                "batch_size":len(ids)}
                        rows.append((idx,st,json.dumps(result,separators=(",",":"))))
                    with db:
                        db.executemany("INSERT OR REPLACE INTO results VALUES(?,?,?)",rows)
                    for idx in ids:states[idx]=st
                    unsat+=len(ids)
                    if len(ids)>1:batched+=len(ids)
                elif st=="TIMEOUT":
                    if len(pre)<n:
                        children=group_prefix(parts,ids,len(pre)+1)
                        if len(children)<2:raise ValueError("prefix did not split")
                        todo.extendleft(reversed(children))
                        splits+=1
                    else:
                        assert len(ids)==1
                        idx=ids[0]
                        dbv2.save(db,idx,{**out,"partition":idx,"assignment":list(parts[idx-1])})
                        states[idx]=st
                        leaf_timeouts+=1
                else:
                    print("[TARGET]",json.dumps(out),flush=True)
                    # Store the actual admitted assignment if it belongs
                    # to this job; otherwise report and stop explicitly.
                    p=tuple(out.get("assignment",()))
                    idx=next((i for i in ids if parts[i-1]==p),None)
                    if idx is None:
                        errors.append("SAT/model-invalid result outside pending leaves")
                    else:
                        dbv2.save(db,idx,{**out,"partition":idx})
                        states[idx]=st
                    stop=True
                dispatch(w)
                if time.monotonic()-last>=10:
                    print("[PROGRESS]",json.dumps({"calls":calls,"unsat":unsat,
                        "total":len(parts),"batch_unsat":batched,"splits":splits,
                        "leaf_timeouts":leaf_timeouts,"queued":len(todo),"elapsed":round(time.monotonic()-start,3)}),flush=True)
                    last=time.monotonic()
            rem=len(parts)-unsat
            state=("ERROR" if errors or any(s in ("ERROR","MODEL_INVALID") for s in states.values())
                   else "SAT" if "SAT" in states.values() else "UNRESOLVED" if rem else "ALL_PARTITIONS_UNSAT")
            elapsed=round(time.monotonic()-start,3)
            print("[SUMMARY]",json.dumps({"status":state,"k":k,"or_min":lo,"or_max":hi,
                "total":len(parts),"prior_unsat":prior,"calls":calls,"unsat":unsat,
                "new_unsat":unsat-prior,"batch_unsat":batched,"splits":splits,
                "leaf_timeouts":leaf_timeouts,"remaining_count":rem,
                "wall_seconds":elapsed,"errors":errors,"lean_verified":False}),flush=True)
            if state=="ERROR":raise SystemExit(1)
        finally:
            for p,q in workers:
                if p.is_alive():p.terminate()
            for p,q in workers:
                p.join(1)
                if p.is_alive():p.kill();p.join()
                q.cancel_join_thread();q.close()
            outq.cancel_join_thread();outq.close()
            db.close()

if __name__=="__main__":main()
