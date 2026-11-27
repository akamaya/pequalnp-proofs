#!/usr/bin/env python3
"""Persistent component SAT + explicit first-merge clauses.

One solver per worker/current block count. A partition is a set of
positive label assumptions, not a new CNF. One OR budget can cover
several exact OR counts at once. All results remain conditional on
the unformalized normalization/graph bounds.
"""
import argparse
import hashlib
import json
import multiprocessing as mp
from pathlib import Path
import queue
import sqlite3
import time
import fcntl

import pnp_graph_partition_sweep_v1 as sw
import pnp_graph_partition_sweep_v2 as dbv2

def onehot(enc, n):
    p=[enc.fresh() for _ in range(n)]
    enc.add(*p)
    enc.atmost(p,1)
    return p

def singleton_sides(enc):
    """Effective singleton truth of every AND operand, including junk."""
    n=enc.n
    sides=[]
    junk=[]
    for j,pair in enumerate(enc.ands):
        ss=[]
        for _,S in pair:
            if j==0:
                ss.append(S[:n])
            else:
                ss.append([enc.disj([S[v]]+
                    [enc.conj([S[n+h],junk[h][v]]) for h in range(min(j,2))])
                    for v in range(n)])
        sides.append(ss)
        if j<2:
            junk.append([enc.conj([a,b]) for a,b in zip(*ss)])
    return sides,junk

def first_merge(enc,edges,sides):
    # Any positive edge first becomes pair-only true at an AND:
    # its two operands are true on opposite singletons and neither
    # operand is true on the other singleton. Include ALL ANDs.
    for u,v in edges:
        possible=[]
        for j,(A,B) in enumerate(sides):
            if j<2:
                possible.extend([enc.conj([A[u],B[v],-A[v],-B[u]]),
                                 enc.conj([A[v],B[u],-A[u],-B[v]])])
            else:
                # Clean ANDs are false on every singleton.
                # Therefore the two positive literals suffice.
                possible.extend([enc.conj([A[u],B[v]]),
                                 enc.conj([A[v],B[u]])])
        enc.add(*possible)
    # Explicit clean-singleton/nonedge implications, already implied
    # by boundary truth. Useful for propagation in the new variables.
    es={tuple(sorted(e)) for e in edges}
    for A,B in sides[2:]:
        for u in range(enc.n):
            for v in range(enc.n):
                if u==v or tuple(sorted((u,v))) not in es:
                    enc.add(-A[u],-B[v])

def universal_components(enc,b,junk_truth):
    """Every true final component partition has a satisfying extension.

    Original component labels 0..b-1, two optional junk-only labels.
    Inactive ORs receive no label. For each label a:
      #originals + #nonbearing junk <= #active ORs + 1.
    This is the component rank bound; connectivity itself is relaxed.
    """
    n,m=enc.n,enc.m
    L=b+2
    raw=[onehot(enc,b) for _ in range(n)]
    junk=[onehot(enc,L) for _ in range(2)]
    bearing=[enc.disj(s) for s in junk_truth]
    for h,s in enumerate(junk_truth):
        for v,z in enumerate(s):
            for a in range(b):
                enc.add(-z,-raw[v][a],junk[h][a])
    ors=[]
    for active,S in zip(enc.active,enc.support):
        P=[enc.fresh() for _ in range(L)]
        enc.add(-active,*P)
        enc.atmost(P,1)
        for z in P:enc.add(-z,active)
        ors.append(P)
        for a in range(L):
            for v in range(n):
                if a<b:enc.add(-S[v],-P[a],raw[v][a])
                else:enc.add(-S[v],-P[a])
            for h in range(2):
                enc.add(-S[n+h],-P[a],junk[h][a])
    for a in range(L):
        attached=[enc.conj([junk[h][a],-bearing[h]]) for h in range(2)]
        originals=[p[a] for p in raw] if a<b else []
        enc.atmost(originals+attached+[-P[a] for P in ors],m+1)
    return raw

def build(n,edges,k,rlo,rhi,b,mode="compact",minimal=True,base=17):
    enc,_,_,meta=sw.v19.build(n,edges,2*k+1+rhi,k,base,rhi,[],minimal,mode)
    before=len(enc.cnf)
    sides,junk=singleton_sides(enc)
    first_merge(enc,edges,sides)
    raw=universal_components(enc,b,junk)
    if rlo:enc.add(enc.active[enc.m-rlo])
    meta.update(variables=enc.max_var,clauses=len(enc.cnf),
                new_clauses=len(enc.cnf)-before,blocks=b,or_min=rlo,or_max=rhi)
    return enc,raw,meta

def assume(raw,part):
    return [raw[v][a] for v,a in enumerate(part)]

def worker(inq,outq,config):
    from pysat.solvers import Solver
    k,rlo,rhi,name,seconds,chunk,mode=config
    n,edges=sw.v1.CASES["l2260"]
    sol=None
    b0=None
    try:
        while True:
            task=inq.get()
            if task is None:return
            idx,part=task
            b=max(part)+1
            t=time.monotonic()
            if b!=b0:
                if sol is not None:sol.delete()
                enc,raw,meta=build(n,edges,k,rlo,rhi,b,mode)
                sol=Solver(name=name,bootstrap_with=enc.cnf)
                b0=b
            ass=assume(raw,part)
            before=sol.accum_stats()
            st=time.monotonic()
            while True:
                sol.conf_budget(chunk)
                answer=sol.solve_limited(assumptions=ass)
                if answer is not None or time.monotonic()-st>=seconds:break
            after=sol.accum_stats()
            out={**meta,"partition":idx,"assignment":list(part),"solver":name,
                 "status":"TIMEOUT" if answer is None else "SAT" if answer else "UNSAT",
                 "solve_seconds":round(time.monotonic()-st,3),
                 "wall_seconds":round(time.monotonic()-t,3),
                 "stats":{x:y-before.get(x,0) for x,y in after.items()}}
            if answer is False:
                core=sol.get_core()
                if core is None:core=ass
                if not set(core)<=set(ass):
                    raise ValueError("unexpected assumption core")
                # Base entails the negated core. Safe across partitions.
                sol.add_clause([-x for x in core])
                out["core_size"]=len(core)
            elif answer is True:
                w=enc.decode(sol.get_model())
                chk=sw.v4.check_star(n,enc.masks,w,17,True)
                ok=(sw.v1.verify(n,enc.masks,w) and chk["valid"] and
                    rlo<=w["internal_or_gates"]<=rhi)
                out.update(witness=w,structure_check=chk,verified_full_truth_table=ok)
                if not ok:out["status"]="MODEL_INVALID"
            outq.put((idx,out))
    except BaseException as e:
        outq.put((None,{"status":"ERROR","error":repr(e)}))
    finally:
        if sol is not None:sol.delete()

def fingerprint(root,n,edges,k,r,mode,parts):
    # Identical to sweep v2: only for importing an exact-r checkpoint.
    h=hashlib.sha256(json.dumps([n,edges,k,r,mode,parts]).encode())
    for name in sw.v19.DEPS+("pnp_sat_solve_v19.py","pnp_graph_partition_exact_v1.py",
            "pnp_graph_partition_sweep_v1.py","pnp_graph_partition_sweep_v2.py"):
        h.update((root/name).read_bytes())
    return h.hexdigest()

def import_v2(db,path,key,parts):
    # Snapshot/read-only import. Never modify the original database.
    old=sqlite3.connect(path.resolve().as_uri()+"?mode=ro",uri=True)
    try:
        if old.execute("SELECT fingerprint FROM meta WHERE id=1").fetchone()!=(key,):
            raise ValueError("v2 seed fingerprint mismatch")
        dbv2.load(old,parts)
        count=0
        with db:
            for idx,st,payload in old.execute("SELECT id,status,payload FROM results WHERE status='UNSAT'"):
                out=json.loads(payload)
                out["inherited_from_v2"]=True
                cur=db.execute("INSERT OR IGNORE INTO results VALUES(?,?,?)",
                               (idx,st,json.dumps(out,separators=(",",":"))))
                count+=cur.rowcount
        return count
    finally:old.close()

def self_test(name):
    from pysat.solvers import Solver
    # Compare to the old exact partition formula for every partition
    # and exact OR count of a small case, both SAT and UNSAT.
    n,edges,k,base=3,[(0,1)],1,2
    parts=[(0,0,0),(0,0,1),(0,1,0),(0,1,1),(0,1,2)]
    ss=[2,4,2,11,1,16] # known nonminimal witness from exact v1
    sat=unsat=0
    for r in (0,1,2):
        for b in (1,2,3):
            enc,raw,_=build(n,edges,k,r,r,b,minimal=False,base=base)
            with Solver(name=name,bootstrap_with=enc.cnf) as sol:
                for part in [p for p in parts if max(p)+1==b]:
                    old,_,_,_=sw.v19.build(n,edges,2*k+1+r,k,base,r,[],False,"compact")
                    sw.ex.constrain_partition(old,part)
                    with Solver(name=name,bootstrap_with=old.cnf) as ref:
                        expected=ref.solve()
                    ass=assume(raw,part)
                    got=sol.solve(assumptions=ass)
                    assert got==expected,(r,part,got,expected)
                    if got:sat+=1
                    else:
                        unsat+=1
                        core=sol.get_core()
                        sol.add_clause([-x for x in (ass if core is None else core)])
                # Revisit all partitions to catch assumption leakage.
                for part in [p for p in parts if max(p)+1==b]:
                    old,_,_,_=sw.v19.build(n,edges,2*k+1+r,k,base,r,[],False,"compact")
                    sw.ex.constrain_partition(old,part)
                    with Solver(name=name,bootstrap_with=old.cnf) as ref:
                        assert sol.solve(assumptions=assume(raw,part))==ref.solve()
    assert sat and unsat,(sat,unsat)
    enc,raw,_=build(n,edges,k,2,2,2,minimal=False,base=base)
    fixed=[x if S&(1<<i) else -x for S,bits in zip(ss,enc.sidebits)
           for i,x in enumerate(bits)]
    with Solver(name=name,bootstrap_with=enc.cnf) as sol:
        assert sol.solve(assumptions=assume(raw,(0,0,1))+fixed)
    # Range encoding must agree with the OR of all exact counts.
    for part in parts:
        b=max(part)+1
        enc,raw,_=build(n,edges,k,0,2,b,minimal=False,base=base)
        expected=False
        for r in (0,1,2):
            old,_,_,_=sw.v19.build(n,edges,2*k+1+r,k,base,r,[],False,"compact")
            sw.ex.constrain_partition(old,part)
            with Solver(name=name,bootstrap_with=old.cnf) as ref:expected|=ref.solve()
        with Solver(name=name,bootstrap_with=enc.cnf) as sol:
            assert sol.solve(assumptions=assume(raw,part))==expected,part
    print("INCREMENTAL COMPONENT SELF TEST OK",{"sat":sat,"unsat":unsat},flush=True)

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--top-count",type=int,default=7)
    ap.add_argument("--or-min",type=int,default=6)
    ap.add_argument("--or-max",type=int,default=6)
    ap.add_argument("--jobs",type=int,default=8)
    ap.add_argument("--seconds",type=float,default=10)
    ap.add_argument("--wall-seconds",type=float,default=600,
                    help="hard overall search budget, including enumeration")
    ap.add_argument("--chunk",type=int,default=3000)
    ap.add_argument("--solver",default="cadical195")
    ap.add_argument("--mode",choices=("compact","canonical"),default="compact")
    ap.add_argument("--seed-v2",type=Path)
    ap.add_argument("--checkpoint",type=Path)
    ap.add_argument("--self-test",action="store_true")
    a=ap.parse_args()
    if a.self_test:self_test(a.solver);return
    k,lo,hi=a.top_count,a.or_min,a.or_max
    if k<1 or not 0<=lo<=hi or 2*k+1+hi>21 or min(a.jobs,a.chunk)<1 or min(a.seconds,a.wall_seconds)<=0:
        ap.error("invalid limits")
    if a.seed_v2 and lo!=hi:ap.error("v2 seed only for an exact OR count")
    start=time.monotonic()
    n,edges=sw.v1.CASES["l2260"]
    parts,generic=sw.candidates(n,edges,k,hi)
    if (k,hi) in dbv2.EXPECTED and (generic,len(parts))!=dbv2.EXPECTED[k,hi]:
        raise ValueError("enumeration cross-check failed")
    # For smaller r, its true partition is in the max-r candidate set:
    # b>=n-r>=n-hi; if b=n-hi then necessarily r=hi.
    root=Path(__file__).resolve().parent
    oldkey=fingerprint(root,n,edges,k,hi,a.mode,parts)
    h=hashlib.sha256(json.dumps([oldkey,lo,hi]).encode())
    h.update(Path(__file__).read_bytes())
    path=a.checkpoint or Path(f"sat-results/l2260-graph-inc-k{k}-r{lo}-{hi}-{a.mode}.sqlite3")
    path.parent.mkdir(parents=True,exist_ok=True)
    with open(str(path)+".lock","a") as lock:
        fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
        db=dbv2.open_db(path,h.hexdigest())
        workers=[]
        ctx=mp.get_context("spawn")
        outq=ctx.Queue()
        try:
            imported=import_v2(db,a.seed_v2,oldkey,parts) if a.seed_v2 else 0
            states=dbv2.load(db,parts)
            pending=[i for i in range(1,len(parts)+1) if states.get(i)!="UNSAT"]
            # Process similar formulas consecutively; prioritize previously
            # timed-out partitions inside each component-count class.
            pending.sort(key=lambda i:(max(parts[i-1]),parts[i-1]))
            prior=len(parts)-len(pending)
            print("[CONFIG]",json.dumps({"k":k,"or_min":lo,"or_max":hi,
                "total":len(parts),"pending":len(pending),"prior_unsat":prior,
                "imported":imported,"jobs":a.jobs,"seconds":a.seconds,
                "wall_limit":a.wall_seconds,"checkpoint":str(path)}),flush=True)
            unsat=prior
            count=0
            errors=[]
            stop="SAT" in states.values()
            todo=iter(pending)
            active={}
            config=(k,lo,hi,a.solver,a.seconds,a.chunk,a.mode)
            for w in range(min(a.jobs,len(pending)) if not stop else 0):
                q=ctx.Queue(maxsize=1)
                p=ctx.Process(target=worker,args=(q,outq,config),daemon=True)
                p.start()
                workers.append((p,q))
                idx=next(todo)
                active[idx]=w
                q.put((idx,parts[idx-1]))
            last=time.monotonic()
            def accept(idx,out):
                nonlocal unsat,count,stop
                if idx not in active:raise ValueError("unknown worker result")
                w=active.pop(idx)
                dbv2.save(db,idx,out)
                states[idx]=out["status"]
                count+=1
                if out["status"]=="UNSAT":unsat+=1
                elif out["status"]!="TIMEOUT":
                    print("[TARGET]",idx,json.dumps(out),flush=True)
                    stop=True
                if not stop and time.monotonic()-start<a.wall_seconds:
                    nxt=next(todo,None)
                    if nxt is not None:
                        active[nxt]=w
                        workers[w][1].put((nxt,parts[nxt-1]))
            while active and not stop and time.monotonic()-start<a.wall_seconds:
                try:idx,out=outq.get(timeout=min(1,max(.01,a.wall_seconds-(time.monotonic()-start))))
                except queue.Empty:
                    if any(not workers[w][0].is_alive() for w in active.values()):
                        errors.append("worker exited without result");break
                    continue
                if idx is None:errors.append(out["error"]);break
                accept(idx,out)
                if time.monotonic()-last>=10:
                    print("[PROGRESS]",json.dumps({"attempted":count,"unsat":unsat,
                        "total":len(parts),"elapsed":round(time.monotonic()-start,3)}),flush=True)
                    last=time.monotonic()
            # Deadline is not UNSAT. In-flight tasks without committed
            # results stay pending, and are retried on the next invocation.
            rem=[i for i in range(1,len(parts)+1) if states.get(i)!="UNSAT"]
            state=("ERROR" if errors or any(s in ("ERROR","MODEL_INVALID") for s in states.values())
                   else "SAT" if "SAT" in states.values() else
                   "UNRESOLVED" if rem else "ALL_PARTITIONS_UNSAT")
            print("[SUMMARY]",json.dumps({"status":state,"k":k,"or_min":lo,"or_max":hi,
                "total":len(parts),"prior_unsat":prior,"attempted":count,
                "unsat":unsat,"remaining_count":len(rem),
                "wall_seconds":round(time.monotonic()-start,3),"errors":errors,
                "lean_verified":False}),flush=True)
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
