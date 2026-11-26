#!/usr/bin/env python3
"""SAT v5: exhaustive dirty-AND-position cubes, bounded parallel search.

Uses v4 full / star constraints. All cubes together cover the original
experimental CNF (exactly two dirty ANDs). No Lean proof is produced.
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


def build(n, edges, s, profile="full", lex=False, base=17):
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
    name,units,profile,base,solver,seconds,chunk=task
    enc=copy.copy(ENC)
    # Explicit unit clauses, not temporary assumptions; a future
    # certificate checker can reproduce the identical subproblem.
    enc.cnf=ENC.cnf+[[x] for x in units]
    r=v4.solve(enc,profile,base,solver,seconds,chunk)
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


def execute(n,edges,s,profile,lex,base,split,solver,seconds,chunk,jobs,path=None):
    global ENC
    if s<2:
        raise ValueError("cube driver requires at least two gate slots")
    start=time.monotonic()
    ENC,dirty=build(n,edges,s,profile,lex,base)
    cubes=make_cubes(dirty,split)
    key=fingerprint(ENC,cubes,profile,base)
    data={"fingerprint":key,"profile":profile,"split":split,"gates":s,
          "cube_units":dict(cubes),"results":{}}
    if path is not None and path.exists():
        old=json.loads(path.read_text())
        if old.get("fingerprint")!=key or old.get("cube_units")!=dict(cubes):
            raise ValueError("checkpoint formula differs; choose a new checkpoint path")
        data=old
    results=data["results"]
    print("[CUBE CONFIG]",json.dumps({"profile":profile,"split":split,"gates":s,
          "clauses":len(ENC.cnf),"variables":ENC.max_var,"cubes":len(cubes),
          "jobs":jobs,"seconds_per_cube":seconds,"solver":solver,
          "fingerprint":key,"build_seconds":round(time.monotonic()-start,3)}),flush=True)
    if any(x.get("status")=="SAT" for x in results.values()):
        out=summarize(results,cubes)
        print("[SUMMARY]",json.dumps(out),flush=True)
        return out
    pending=[(name,units,profile,base,solver,seconds,chunk)
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
            r=execute(3,[(0,1)],s,"full",False,0,split,solver,seconds,chunk,2)
            assert r["status"]==expected,r
    # Checkpoint resume: all solved cubes skipped on second invocation.
    import tempfile
    with tempfile.TemporaryDirectory() as tmp:
        p=Path(tmp)/"test.json"
        for _ in range(2):
            r=execute(3,[(0,1)],2,"full",False,0,"second",solver,seconds,chunk,2,p)
            assert r["status"]=="UNSAT",r
    print("SAT V5 SELF TEST OK",flush=True)


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--case",choices=v1.CASES,default="l2260")
    ap.add_argument("--gates",type=int,default=21)
    ap.add_argument("--profile",choices=("star","full"),default="full")
    ap.add_argument("--split",choices=("second","pair"),default="second")
    ap.add_argument("--lex",action="store_true",help="optional experimental lex constraints")
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
                       a.solver,a.seconds,a.chunk,a.jobs,a.checkpoint)
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
