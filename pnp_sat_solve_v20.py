#!/usr/bin/env python3
"""SAT v20: persistent incremental SAT across exact OR-count cubes.

Identical v19 base CNF; use exact count assumptions in one solver per k.
Retain globally valid learned clauses and solved-cube blocking clauses
within the process. Only resolved cube statuses survive process exits.
No verified Lean proof is implied.
"""
import argparse
import hashlib
import json
import multiprocessing as mp
from multiprocessing.connection import wait
import os
import time
from pathlib import Path
import pnp_sat_solve_v1 as v1
import pnp_sat_solve_v4 as v4
import pnp_sat_solve_v11 as v11
import pnp_sat_solve_v19 as v19

DEPS=v19.DEPS


def delta_stats(before,after):
    return {key:value-before.get(key,0) for key,value in after.items()}


def group_worker(task,conn):
    n,edges,total,k,base,budget,name,seconds,chunk,cuts,minimal,mode,rs,rounds=task
    from pysat.solvers import Solver
    try:
        t=time.monotonic()
        enc,_,_,meta=v19.build(n,edges,total,k,base,budget,cuts,minimal,mode)
        meta.update(solver=name,build_seconds=round(time.monotonic()-t,3))
        conn.send(("CNF",meta))
        pending=list(rs)
        with Solver(name=name,bootstrap_with=enc.cnf) as sol:
            for rnd in range(1,rounds+1):
                later=[]
                for r in pending:
                    ass=v11.exact_units(enc.active,r)
                    t=time.monotonic()
                    before=sol.accum_stats()
                    answer=None
                    last=t
                    conn.send(("START",r,rnd))
                    while True:
                        sol.conf_budget(chunk)
                        answer=sol.solve_limited(assumptions=ass)
                        now=time.monotonic()
                        if answer is not None or now-t>=seconds:break
                        if now-last>=5:
                            conn.send(("HEARTBEAT",r,rnd))
                            last=now
                    after=sol.accum_stats()
                    out={**meta,"round":rnd,"exact_or_count":r,
                         "status":"TIMEOUT" if answer is None else "SAT" if answer else "UNSAT",
                         "solve_seconds":round(time.monotonic()-t,3),
                         "stats":delta_stats(before,after),"cumulative_stats":after}
                    if answer is True:
                        try:
                            w=enc.decode(sol.get_model())
                            check=v4.check_star(n,enc.masks,w,base,True)
                            ok=(v1.verify(n,enc.masks,w) and check["valid"]
                                and w["internal_or_gates"]==r)
                            out.update(witness=w,structure_check=check,verified_full_truth_table=ok)
                            if not ok:out["status"]="MODEL_INVALID"
                        except Exception as e:
                            out.update(status="MODEL_INVALID",error=repr(e))
                    if answer is False:
                        # F & assumptions UNSAT implies the negated cube.
                        # Explicitly remember it for subsequent solves.
                        sol.add_clause([-x for x in ass])
                    elif answer is None:
                        later.append(r)
                    conn.send(("RESULT",r,out))
                    if out["status"] in ("SAT","MODEL_INVALID"):return
                pending=later
                if not pending:break
    except Exception as e:
        conn.send(("ERROR",repr(e)))
    finally:
        try:conn.send(("DONE",))
        except (OSError,BrokenPipeError):pass
        conn.close()


def execute_groups(tasks,jobs,seconds,accept):
    ctx=mp.get_context("fork")
    todo=iter(tasks)
    workers={}
    failures=[]
    stop=False
    def fill():
        while len(workers)<jobs and not stop:
            task=next(todo,None)
            if task is None:break
            recv,send=ctx.Pipe(False)
            proc=ctx.Process(target=group_worker,args=(task,send),daemon=True)
            proc.start();send.close()
            workers[recv]={"proc":proc,"k":task[3],"last":time.monotonic(),"done":False}
    def close(recv):
        w=workers.pop(recv)
        recv.close()
        p=w["proc"]
        p.join(.2)
        if p.is_alive():p.terminate();p.join(1)
        if p.is_alive():p.kill();p.join()
    try:
        fill()
        while workers:
            ready=wait(list(workers),timeout=1)
            for recv in ready:
                w=workers[recv]
                try:m=recv.recv()
                except EOFError:
                    if not w["done"]:
                        failures.append((w["k"],"worker exited unexpectedly"))
                        stop=True
                    close(recv)
                    continue
                w["last"]=time.monotonic()
                tag=m[0]
                if tag=="CNF":print("[CNF]",json.dumps(m[1]),flush=True)
                elif tag=="START":print("[START]",w["k"],m[1],"round",m[2],flush=True)
                elif tag=="RESULT":
                    accept(w["k"],m[1],m[2])
                    if m[2]["status"] in ("SAT","MODEL_INVALID"):stop=True
                elif tag=="ERROR":
                    failures.append((w["k"],m[1]));stop=True
                elif tag=="DONE":
                    w["done"]=True
                    close(recv)
            # solve_limited normally returns at each conflict budget.
            # A hung backend is an ERROR, never UNSAT.
            for recv,w in list(workers.items()):
                if time.monotonic()-w["last"]>max(120,seconds+60):
                    failures.append((w["k"],"worker unresponsive"))
                    stop=True
                    close(recv)
            if stop:
                for recv in list(workers):close(recv)
            else:fill()
    finally:
        for recv in list(workers):close(recv)
    return failures


def self_test(solver,seconds,chunk):
    from pysat.solvers import Solver
    # Compare each assumption cube to a fresh solver with unit clauses.
    # Exercise order changes and UNSAT reuse on a known small instance.
    enc,_,_,_=v19.build(3,[(0,1)],5,1,0,2,[],False,"compact")
    expected={}
    for r in range(3):
        ass=v11.exact_units(enc.active,r)
        with Solver(name=solver,bootstrap_with=enc.cnf+[[x] for x in ass]) as sol:
            expected[r]=sol.solve()
    assert expected[0] is False and expected[2] is True,expected
    with Solver(name=solver,bootstrap_with=enc.cnf) as sol:
        for r in (2,0,1,2,0,1):
            ass=v11.exact_units(enc.active,r)
            while True:
                sol.conf_budget(chunk)
                ans=sol.solve_limited(assumptions=ass)
                if ans is not None:break
            assert ans==expected[r],(r,ans,expected)
            if ans is False:sol.add_clause([-x for x in ass])
    # Check actual group worker, including pipe, result validation, and
    # no cross-cube assumption leakage. SAT stops the group.
    seen={}
    task=(3,[(0,1)],5,1,0,2,solver,seconds,chunk,[],False,"compact",[0,2],1)
    errs=execute_groups([task],1,seconds,lambda k,r,out:seen.update({r:out}))
    assert not errs,errs
    assert seen[0]["status"]=="UNSAT" and seen[2]["status"]=="SAT",seen
    assert seen[2]["verified_full_truth_table"],seen
    print("SAT V20 SELF TEST OK",expected,flush=True)


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--case",choices=v1.CASES,default="l2260")
    ap.add_argument("--gates",type=int,default=21)
    ap.add_argument("--jobs",type=int,default=3)
    ap.add_argument("--seconds",type=float,default=300)
    ap.add_argument("--solver",default="cadical195")
    ap.add_argument("--solver-for",action="append",default=[],metavar="K=SOLVER")
    ap.add_argument("--chunk",type=int,default=20000)
    ap.add_argument("--outer-mode",choices=("compact","canonical"),default="compact")
    ap.add_argument("--seed-v11",type=Path)
    ap.add_argument("--seed-v16",type=Path)
    ap.add_argument("--seed-v19",type=Path)
    ap.add_argument("--rounds",type=int,default=1)
    ap.add_argument("--checkpoint",type=Path)
    ap.add_argument("--no-minimality",action="store_true")
    ap.add_argument("--self-test",action="store_true")
    a=ap.parse_args()
    if a.gates<3 or a.jobs<1 or a.seconds<=0 or a.chunk<1 or a.rounds<1:ap.error("invalid limits")
    if a.self_test:self_test(a.solver,a.seconds,a.chunk);return
    n,edges=v1.CASES[a.case]
    base=17 if a.case=="l2260" else 0
    counts=list(range((a.gates-1)//2,0,-1))
    minimal=not a.no_minimality
    prior=set()
    if a.seed_v11:
        old=json.loads(a.seed_v11.read_text())
        expected=v11.digest([n,edges,a.gates,base,counts,"exact"],
                            v11.FILES+("pnp_sat_solve_v11.py",))
        if old.get("fingerprint")!=expected:raise ValueError("v11 seed mismatch")
        for k in counts:
            for r in range(a.gates-2*k):
                if str(k) in old["inherited"] or old["results"].get(f"{k}:{r}",{}).get("status")=="UNSAT":
                    prior.add((k,r))
    jobs=[]
    for k in counts:
        rr=[r for r in range(a.gates-2*k) if (k,r) not in prior]
        if rr:jobs.append((k,max(rr)))
    params=[n,edges,a.gates,base,jobs,minimal]
    seed={}
    if a.seed_v16:
        old=json.loads(a.seed_v16.read_text())
        if old.get("fingerprint")!=v11.digest(params,DEPS):
            raise ValueError("v16 seed mismatch")
        for k,r in jobs:
            prev=old.get("results",{}).get(str(k),{})
            if prev.get("status") in ("UNSAT","TIMEOUT"):
                seed[str(k)]=prev
    seed_hash=hashlib.sha256(json.dumps(seed,sort_keys=True).encode()).hexdigest()
    p19=params+[a.outer_mode,seed_hash,"exact-cubes"]
    k19=v11.digest(p19,DEPS+("pnp_sat_solve_v19.py",))
    seed19={}
    if a.seed_v19:
        old=json.loads(a.seed_v19.read_text())
        if old.get("fingerprint")!=k19:raise ValueError("v19 seed mismatch")
        for k,b in jobs:
            for r in range(b+1):
                name=f"{k}:{r}"
                prev=old.get("results",{}).get(name,{})
                if prev.get("status")=="UNSAT":
                    seed19[name]={**prev,"inherited_from_v19":True}
    key=v11.digest(p19+["incremental"],DEPS+("pnp_sat_solve_v19.py","pnp_sat_solve_v20.py"))
    overrides={}
    for entry in a.solver_for:
        k,sep,name=entry.partition("=")
        if not sep or not k.isdigit() or int(k) not in counts or not name:
            ap.error("solver override must be K=SOLVER")
        overrides[int(k)]=name
    path=a.checkpoint
    def execute():
        start=time.monotonic()
        data={"fingerprint":key,"results":{}}
        if path and path.exists():
            data=json.loads(path.read_text())
            if data.get("fingerprint")!=key:raise ValueError("checkpoint mismatch")
        results=data["results"]
        for name in list(results):
            if name.startswith("worker:"):del results[name]
        for k,r in jobs:
            prev=seed.get(str(k),{})
            if prev.get("status")=="UNSAT":
                results.setdefault(str(k),{"status":"UNSAT","inherited_from_v16":True})
        for name,prev in seed19.items():
            results.setdefault(name,prev)
        def save():
            if path:
                tmp=path.with_name(path.name+".tmp")
                tmp.write_text(json.dumps(data,indent=2)+"\n")
                os.replace(tmp,path)
        save()
        def known(k,r):
            return ((k,r) in prior or
                    results.get(str(k),{}).get("status")=="UNSAT" or
                    results.get(f"{k}:{r}",{}).get("status")=="UNSAT")
        pending=[(k,budget,[r for r in range(budget+1) if not known(k,r)])
                 for k,budget in jobs]
        pending=[p for p in pending if p[2]]
        print("[CONFIG]",json.dumps({"pending":pending,"prior_unsat":len(prior),
            "imported_v19_unsat":len(seed19),
            "imported_cuts":sum(len(seed.get(str(k),{}).get("cuts",[]))
                                for k,b,rs in pending),
            "jobs":a.jobs,"seconds_per_cube":a.seconds,"rounds":a.rounds,
            "solver":a.solver,"solver_for":overrides,"outer_mode":a.outer_mode}),flush=True)
        if not any(x.get("status")=="SAT" for x in results.values()):
            tasks=[]
            for k,budget,rs in pending:
                cuts=seed.get(str(k),{}).get("cuts",[])
                tasks.append((n,edges,a.gates,k,base,budget,
                    overrides.get(k,a.solver),a.seconds,a.chunk,cuts,minimal,
                    a.outer_mode,rs,a.rounds))
            def accept(k,r,out):
                results[f"{k}:{r}"]=out
                save()
                print("[INCREMENTAL CUBE]",k,r,json.dumps(out),flush=True)
            failures=execute_groups(tasks,a.jobs,a.seconds,accept)
            for k,error in failures:
                results[f"worker:{k}"]={"status":"ERROR","error":error}
                save()
        remaining=[[k,r] for k in counts for r in range(a.gates-2*k)
                   if not known(k,r)]
        states=[x.get("status") for x in results.values()]
        state=("ERROR" if any(s in ("ERROR","MODEL_INVALID") for s in states) else
               "SAT" if "SAT" in states else "UNRESOLVED" if remaining else "UNSAT")
        print("[SUMMARY]",json.dumps({"status":state,"remaining":remaining,
            "remaining_count":len(remaining),"wall_seconds":round(time.monotonic()-start,3)}),flush=True)
        if state=="ERROR":raise SystemExit(1)
    if path:
        import fcntl
        path.parent.mkdir(parents=True,exist_ok=True)
        with open(str(path)+".lock","a") as lock:
            fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
            execute()
    else:execute()


if __name__=="__main__":main()
