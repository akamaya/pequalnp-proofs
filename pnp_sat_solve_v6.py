#!/usr/bin/env python3
"""SAT v6: minimum-circuit pruning plus parallel dirty-position cubes.

Uses v4 full / star constraints and necessary conditions for minimum AO2 circuits.
Pruning is experimental; its soundness has not been formalized in Lean.
"""
import argparse
import concurrent.futures as cf
import copy
import fcntl
import hashlib
import itertools
import json
import multiprocessing as mp
import os
import time
from pathlib import Path
import pnp_sat_solve_v1 as v1
import pnp_sat_solve_v2 as v2
import pnp_sat_solve_v4 as v4

# Initialized once before the fork pool; inherited by worker processes.
ENC = None


def add_minimality(enc, prune):
    """Exclude syntactically redundant gates, using IsLeastAO minimality.

    If a wire b has an OR-only path to a, then a <= b pointwise.
    If it has an AND-only path to a, then b <= a. A gate using both
    operands is redundant for either operation. Replace it by one of
    its earlier operands, redirect readers/output and remove it.
    Reachability variables need only forward implication: paths must
    be marked, non-paths can be false, so valid circuits are not lost.
    """
    if prune=="none":
        return
    n,s,v=enc.n,enc.s,enc.v
    high=max(abs(x) for c in enc.cnf for x in c)
    def fresh():
        nonlocal high
        high+=1
        return high
    if prune=="absorb-dup":
        for j in range(s):
            for i in range(j):
                for a,b in itertools.combinations(range(n+i),2):
                    for op in (0,1):
                        enc.add(-v(0,i,op),-v(0,j,op),
                                -v(1,i,a),-v(2,i,b),
                                -v(1,j,a),-v(2,j,b))
    reach=[[],[]]
    for j in range(s):
        for op in (0,1):
            row=[fresh() for _ in range(n+j)]
            reach[op].append(row)
            for e in (1,2):
                for k in range(n+j):
                    sel=v(e,j,k)
                    enc.add(-v(0,j,op),-sel,row[k])
                    if k>=n:
                        for a,old in enumerate(reach[op][k-n]):
                            enc.add(-v(0,j,op),-sel,-old,row[a])
        # fOrd enforces strictly increasing sources for nonpadding.
        for i in range(j):
            b=n+i
            for a in range(b):
                for op in (0,1):
                    enc.add(-v(1,j,a),-v(2,j,b),-reach[op][i][a])
    essential=0
    for m in enc.masks:
        essential|=m
    for a in range(n):
        if essential&(1<<a):
            enc.add(v(6,0,a),*(v(e,j,a) for j in range(s) for e in (1,2)))


def check_minimality(n,w,prune):
    if prune=="none":
        return True
    reach=[[],[]]
    seen=set()
    for j,(op,a,b) in enumerate(w["gates"]):
        if a==b:
            return False
        a,b=sorted((a,b))
        if b>=n and any(a in reach[k][b-n] for k in (0,1)):
            return False
        key=(op,a,b)
        if prune=="absorb-dup" and key in seen:
            return False
        seen.add(key)
        for k,name in enumerate(("and","or")):
            r=set()
            if op==name:
                for x in (a,b):
                    r.add(x)
                    if x>=n:r|=reach[k][x-n]
            reach[k].append(r)
    return True


def build(n, edges, s, profile="full", lex=False, base=17, prune="absorb"):
    masks = v1.graph(n, edges)
    orig = v1.Encoding(n, s, masks, v1.rows_for(n,masks), lex).build()
    v2.add_onehot(orig)
    high = max(abs(x) for c in orig.cnf for x in c)
    # v2.add_topform allocates the s dirty flags first. Verify that
    # the pinned implementation is compatible; these equivalences
    # also guard against accidental future changes in the numbering.
    v2.add_topform(orig)
    d0 = list(range(high+1, high+s+1))
    clause_set = {tuple(c) for c in orig.cnf}
    for j,d in enumerate(d0):
        a = orig.v(0,j,0)
        neg = [orig.v(3,j,r) for r in orig.rows if not v1.target(r,masks)]
        assert (-d,a) in clause_set and tuple([-d]+neg) in clause_set
        assert all((-a,-z,d) in clause_set for z in neg)
    del clause_set
    v4.add_star(orig, base, profile=="full")
    add_minimality(orig,prune)
    enc = v2.Compact(orig, "topform")
    forward = {v:i for i,v in enumerate(enc.reverse) if i}
    return enc, [forward[d] for d in d0]


def make_cubes(dirty, split):
    s = len(dirty)
    if split=="second":
        # j is the later dirty gate. Exactly two dirty gates are already
        # enforced; all other gates after j are not dirty.
        return [(f"second-{j:02d}", [dirty[j]]+[-x for x in dirty[j+1:]])
                for j in range(1,s)]
    return [(f"pair-{i:02d}-{j:02d}",[dirty[i],dirty[j]])
            for i,j in itertools.combinations(range(s),2)]


def fingerprint(enc, cubes, profile, base):
    h=hashlib.sha256()
    h.update(json.dumps({"format":1,"profile":profile,"base":base,
                         "n":enc.n,"masks":enc.masks,"cubes":cubes},
                        separators=(",",":")).encode())
    for c in enc.cnf:
        h.update((" ".join(map(str,c))+" 0\n").encode("ascii"))
    return h.hexdigest()


def solve_cube(task):
    name,units,profile,base,solver,seconds,chunk,prune=task
    enc=copy.copy(ENC)
    # Explicit unit clauses, not temporary assumptions; a future
    # certificate checker can reproduce the identical subproblem.
    enc.cnf=ENC.cnf+[[x] for x in units]
    r=v4.solve(enc,profile,base,solver,seconds,chunk)
    if r["status"]=="SAT" and not check_minimality(enc.n,r["witness"],prune):
        r["status"]="MODEL_INVALID"
        r["error"]="independent minimality pruning check failed"
    return name,r


def save(path,data):
    if path is None:
        return
    tmp=path.with_name(path.name+".tmp")
    tmp.write_text(json.dumps(data,indent=2)+"\n")
    os.replace(tmp,path)


def summarize(results,cubes):
    counts={}
    for name,_ in cubes:
        status=results.get(name,{}).get("status","PENDING")
        counts[status]=counts.get(status,0)+1
    if counts.get("MODEL_INVALID") or counts.get("ERROR"):
        outcome="ERROR"
    elif counts.get("SAT"):
        outcome="SAT"
    elif counts.get("UNSAT",0)==len(cubes):
        outcome="UNSAT"
    else:
        outcome="UNRESOLVED"
    return {"status":outcome,"cubes":len(cubes),"counts":counts}


def execute(n,edges,s,profile,lex,base,split,solver,seconds,chunk,jobs,path=None,prune="absorb"):
    global ENC
    if s<2:
        raise ValueError("cube driver requires at least two gate slots")
    start=time.monotonic()
    ENC,dirty=build(n,edges,s,profile,lex,base,prune)
    cubes=make_cubes(dirty,split)
    key=fingerprint(ENC,cubes,profile,base)
    data={"fingerprint":key,"profile":profile,"prune":prune,"split":split,"gates":s,
          "cube_units":dict(cubes),"results":{}}
    if path is not None and path.exists():
        old=json.loads(path.read_text())
        if old.get("fingerprint")!=key or old.get("cube_units")!=dict(cubes):
            raise ValueError("checkpoint formula differs; choose a new checkpoint path")
        data=old
    results=data["results"]
    print("[CUBE CONFIG]",json.dumps({"profile":profile,"prune":prune,"split":split,"gates":s,
          "clauses":len(ENC.cnf),"variables":ENC.max_var,"cubes":len(cubes),
          "jobs":jobs,"seconds_per_cube":seconds,"solver":solver,
          "fingerprint":key,"build_seconds":round(time.monotonic()-start,3)}),flush=True)
    if any(x.get("status")=="SAT" for x in results.values()):
        out=summarize(results,cubes)
        print("[SUMMARY]",json.dumps(out),flush=True)
        return out
    pending=[(name,units,profile,base,solver,seconds,chunk,prune)
             for name,units in cubes if results.get(name,{}).get("status")!="UNSAT"]
    # Save the initial manifest, then commit each completed result atomically.
    save(path,data)
    if pending:
        with cf.ProcessPoolExecutor(max_workers=jobs,mp_context=mp.get_context("fork")) as pool:
            todo=iter(pending)
            active={}
            def fill():
                while len(active)<jobs:
                    task=next(todo,None)
                    if task is None:
                        break
                    active[pool.submit(solve_cube,task)]=task[0]
            fill()
            stop=False
            while active:
                done,_=cf.wait(active,return_when=cf.FIRST_COMPLETED)
                for f in done:
                    name=active.pop(f)
                    try:
                        got,r=f.result()
                        assert got==name
                    except Exception as e:
                        r={"status":"ERROR","error":repr(e)}
                    r["solver"]=solver
                    r["seconds_per_cube"]=seconds
                    results[name]=r
                    save(path,data)
                    print("[CUBE]",name,json.dumps(r),flush=True)
                    if r["status"] in ("SAT","ERROR","MODEL_INVALID"):
                        stop=True
                # Do not start new cubes after SAT or a validation/engine error.
                # Already running workers finish within their bounded timeout.
                if not stop:
                    fill()
    out=summarize(results,cubes)
    out["wall_seconds"]=round(time.monotonic()-start,3)
    print("[SUMMARY]",json.dumps(out),flush=True)
    return out


def self_test(solver,seconds,chunk):
    # Cover/disjointness by enumerating every possible pair of dirty slots.
    for s in range(2,22):
        ids=list(range(1,s+1))
        for split in ("second","pair"):
            cubes=make_cubes(ids,split)
            for i,j in itertools.combinations(ids,2):
                assignment={i,j}
                count=sum(all((x in assignment) if x>0 else (-x not in assignment)
                              for x in units) for _,units in cubes)
                assert count==1,(s,split,i,j,count)
    # Check both split modes against small known cases, including
    # actual multiprocessing and v4's independent witness verifier.
    for split in ("second","pair"):
        for s,expected in ((2,"UNSAT"),(5,"SAT")):
            r=execute(3,[(0,1)],s,"full",False,0,split,solver,seconds,chunk,2,prune="none")
            assert r["status"]==expected,r
    # Checkpoint resume: all solved cubes skipped on second invocation.
    import tempfile
    with tempfile.TemporaryDirectory() as tmp:
        p=Path(tmp)/"test.json"
        for _ in range(2):
            r=execute(3,[(0,1)],2,"full",False,0,"second",solver,seconds,chunk,2,p,prune="none")
            assert r["status"]=="UNSAT",r
    from pysat.solvers import Solver
    def forced(n,edges,w,prune):
        masks=v1.graph(n,edges)
        assert v1.verify(n,masks,w)
        s=len(w["gates"])
        enc=v1.Encoding(n,s,masks,v1.rows_for(n,masks),False).build()
        v2.add_onehot(enc)
        add_minimality(enc,prune)
        assumptions=[]
        for j,(op,a,b) in enumerate(w["gates"]):
            assumptions.extend(enc.v(k,j,z) for k,z in
                               ((0,0 if op=="and" else 1),(1,min(a,b)),(2,max(a,b))))
        assumptions.append(enc.v(6,0,w["output"]))
        compact=v2.Compact(enc,"dense")
        forward={x:i for i,x in enumerate(compact.reverse) if i}
        with Solver(name=solver,bootstrap_with=compact.cnf) as sol:
            return sol.solve(assumptions=[forward[x] for x in assumptions])
    direct={"gates":[("and",0,1),("and",0,2)],"output":3}
    transitive={"gates":[("or",0,1),("or",2,4),("and",0,5),("and",3,6)],"output":7}
    dup={"gates":[("and",0,1),("and",0,1),("or",2,3)],"output":4}
    for n,edges,w in ((2,[(0,1)],direct),(4,[(0,3)],transitive)):
        assert forced(n,edges,w,"none")
        assert not forced(n,edges,w,"absorb")
        assert not check_minimality(n,w,"absorb")
    assert forced(2,[(0,1)],dup,"absorb")
    assert not forced(2,[(0,1)],dup,"absorb-dup")
    assert not check_minimality(2,dup,"absorb-dup")
    for case,minimum in (("edge",1),("path3",2),("triangle",4)):
        n,edges=v1.CASES[case]
        masks=v1.graph(n,edges)
        for prune in ("absorb","absorb-dup"):
            for s in (minimum-1,minimum):
                enc=v1.Encoding(n,s,masks,v1.rows_for(n,masks),False).build()
                v2.add_onehot(enc)
                add_minimality(enc,prune)
                compact=v2.Compact(enc,"dense")
                with Solver(name=solver,bootstrap_with=compact.cnf) as sol:
                    assert sol.solve()==(s==minimum),(case,s,prune)
                    if s==minimum:
                        w=compact.decode(sol.get_model())
                        assert v1.verify(n,masks,w)
                        assert check_minimality(n,w,prune)
    print("SAT V6 SELF TEST OK",flush=True)


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--case",choices=v1.CASES,default="l2260")
    ap.add_argument("--gates",type=int,default=21)
    ap.add_argument("--profile",choices=("star","full"),default="full")
    ap.add_argument("--split",choices=("second","pair"),default="second")
    ap.add_argument("--lex",action="store_true",help="optional experimental lex constraints")
    ap.add_argument("--prune",choices=("none","absorb","absorb-dup"),default="absorb")
    ap.add_argument("--jobs",type=int,default=4)
    ap.add_argument("--seconds",type=float,default=8,help="wall seconds per cube")
    ap.add_argument("--chunk",type=int,default=20000)
    ap.add_argument("--solver",default="g4")
    ap.add_argument("--checkpoint",type=Path)
    ap.add_argument("--self-test",action="store_true")
    a=ap.parse_args()
    if a.gates<2 or a.jobs<1 or a.seconds<=0 or a.chunk<1:
        ap.error("invalid limits")
    if a.self_test:
        self_test(a.solver,a.seconds,a.chunk)
        return
    n,edges=v1.CASES[a.case]
    base=17 if a.case=="l2260" else 0
    def run():
        return execute(n,edges,a.gates,a.profile,a.lex,base,a.split,
                       a.solver,a.seconds,a.chunk,a.jobs,a.checkpoint,a.prune)
    if a.checkpoint:
        a.checkpoint.parent.mkdir(parents=True,exist_ok=True)
        with open(str(a.checkpoint)+".lock","a") as lock:
            fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
            r=run()
    else:
        r=run()
    if r["status"]=="ERROR":
        raise SystemExit(1)


if __name__=="__main__":
    main()
