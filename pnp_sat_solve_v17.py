#!/usr/bin/env python3
"""SAT v17: fuse outer support and exact OR-DAG formulas.

The outer support variables are identified with the corresponding inner
variables. Saved v16 cuts are remapped to those shared variables.
This solves the conjunction in one CDCL engine instead of CEGAR loops.
No Lean reduction or certificate verification is implied.
"""
import argparse
import concurrent.futures as cf
import hashlib
import json
import multiprocessing as mp
import os
import time
from pathlib import Path
import pnp_sat_solve_v1 as v1
import pnp_sat_solve_v4 as v4
import pnp_sat_solve_v11 as v11
import pnp_sat_solve_v12 as v12
import pnp_sat_solve_v14 as v14
import pnp_sat_solve_v16 as v16

DEPS=v11.FILES+("pnp_sat_solve_v11.py","pnp_sat_solve_v12.py",
    "pnp_sat_solve_v13.py","pnp_sat_solve_v14.py","pnp_or_budget_v1.py",
    "pnp_sat_solve_v15.py","pnp_or_projection_v1.py","pnp_sat_solve_v16.py")


def build(n,edges,total,k,base,r,cuts,minimal=True,mode="light"):
    inner=v14.Oracle(n,edges,2*k+1+r,k,base).build()
    outer=(v12.Relax if mode=="light" else v14.Relax)(
        n,edges,total,k,base,r,minimal).build()
    outer_bits=[x for group in outer.sides for x in group]
    inner_bits=[x for group in inner.sidebits for x in group]
    if len(outer_bits)!=len(inner_bits) or len(set(outer_bits))!=len(outer_bits):
        raise ValueError("side variable mismatch")
    # v12 and v14 allocate all support bits before any other variables.
    expected=list(range(1,2*(k+2)*(n+2)+1))
    if outer_bits!=expected:
        raise ValueError("support variable layout changed")
    mapping=dict(zip(outer_bits,inner_bits))
    allowed=set(mapping)
    old_inner_max=inner.max_var
    for x in range(1,outer.max_var+1):
        if x not in mapping:
            inner.max_var+=1
            mapping[x]=inner.max_var
    def remap(c):
        return [mapping[x] if x>0 else -mapping[-x] for x in c]
    old_inner_clauses=len(inner.cnf)
    inner.cnf.extend(remap(c) for c in outer.cnf)
    seen=set()
    for cut in cuts:
        if any(abs(x) not in allowed for x in cut):
            raise ValueError("checkpoint cut outside support variables")
        cc=tuple(sorted(set(cut),key=lambda x:(abs(x),x)))
        if cc in seen:continue
        seen.add(cc)
        inner.cnf.append(remap(cc))
    meta={"top_count":k,"or_budget":r,"outer_mode":mode,
          "variables":inner.max_var,"clauses":len(inner.cnf),
          "inner_variables":old_inner_max,"inner_clauses":old_inner_clauses,
          "outer_clauses":len(outer.cnf),"shared_variables":len(outer_bits),
          "imported_cuts":len(seen)}
    return inner,outer,mapping,meta


def run(task):
    n,edges,total,k,base,r,solver,seconds,chunk,cuts,minimal,mode=task
    t=time.monotonic()
    enc,_,_,meta=build(n,edges,total,k,base,r,cuts,minimal,mode)
    meta.update(solver=solver,build_seconds=round(time.monotonic()-t,3))
    print("[CNF]",json.dumps(meta),flush=True)
    out=v4.solve(enc,"full",base,solver,seconds,chunk)
    return {**meta,**out}


def self_test(solver,seconds,chunk):
    from pysat.solvers import Solver
    # Exercise mapping, sign preservation, both modes and exact cuts
    # using a known nonminimal v9 boundary witness.
    ss=[2,4,2,11,1,16]
    for mode in ("light","strong"):
        inner,outer,mapping,meta=build(3,[(0,1)],5,1,2,2,[],False,mode)
        ass=v14.bits_for(ss,inner.sidebits)
        with Solver(name=solver,bootstrap_with=inner.cnf) as s:
            assert s.solve(assumptions=ass)
            w=inner.decode(s.get_model())
            assert v1.verify(3,inner.masks,w)
            assert v4.check_star(3,inner.masks,w,2,True)["valid"]
        cut=[-x for x in v14.bits_for(ss,outer.sides)]
        blocked,_,_,_=build(3,[(0,1)],5,1,2,2,[cut],False,mode)
        with Solver(name=solver,bootstrap_with=blocked.cnf) as s:
            assert not s.solve(assumptions=ass)
        for total,r,expected in ((3,0,"UNSAT"),(5,2,"SAT")):
            got=run((3,[(0,1)],total,1,0,r,solver,seconds,chunk,[],False,mode))
            print("[TEST]",json.dumps(got),flush=True)
            assert got["status"]==expected,got
    print("SAT V17 SELF TEST OK",flush=True)


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--case",choices=v1.CASES,default="l2260")
    ap.add_argument("--gates",type=int,default=21)
    ap.add_argument("--jobs",type=int,default=3)
    ap.add_argument("--seconds",type=float,default=600)
    ap.add_argument("--solver",default="cadical195")
    ap.add_argument("--solver-for",action="append",default=[],metavar="K=SOLVER")
    ap.add_argument("--chunk",type=int,default=20000)
    ap.add_argument("--outer-mode",choices=("light","strong"),default="light")
    ap.add_argument("--seed-v11",type=Path)
    ap.add_argument("--seed-v16",type=Path)
    ap.add_argument("--checkpoint",type=Path)
    ap.add_argument("--no-minimality",action="store_true")
    ap.add_argument("--self-test",action="store_true")
    a=ap.parse_args()
    if a.gates<3 or a.jobs<1 or a.seconds<=0 or a.chunk<1:ap.error("invalid limits")
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
    key=v11.digest(params+[a.outer_mode,seed_hash],DEPS+("pnp_sat_solve_v17.py",))
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
        for k,r in jobs:
            prev=seed.get(str(k),{})
            if prev.get("status")=="UNSAT":
                results.setdefault(str(k),{"status":"UNSAT","inherited_from_v16":True})
        def save():
            if path:
                tmp=path.with_name(path.name+".tmp")
                tmp.write_text(json.dumps(data,indent=2)+"\n")
                os.replace(tmp,path)
        save()
        pending=[(k,r) for k,r in jobs if results.get(str(k),{}).get("status")!="UNSAT"]
        print("[CONFIG]",json.dumps({"pending":pending,"prior_unsat":len(prior),
            "imported_cuts":sum(len(seed.get(str(k),{}).get("cuts",[])) for k,r in pending),
            "jobs":a.jobs,"seconds":a.seconds,"solver":a.solver,"solver_for":overrides,
            "outer_mode":a.outer_mode}),flush=True)
        if not any(x.get("status")=="SAT" for x in results.values()):
            with cf.ProcessPoolExecutor(max_workers=a.jobs,mp_context=mp.get_context("fork")) as pool:
                fs={}
                for k,r in pending:
                    cuts=seed.get(str(k),{}).get("cuts",[])
                    task=(n,edges,a.gates,k,base,r,overrides.get(k,a.solver),a.seconds,a.chunk,
                          cuts,minimal,a.outer_mode)
                    fs[pool.submit(run,task)]=k
                for f in cf.as_completed(fs):
                    k=fs[f]
                    try:out=f.result()
                    except Exception as e:out={"status":"ERROR","error":repr(e)}
                    results[str(k)]=out
                    save()
                    print("[FUSED]",k,json.dumps(out),flush=True)
        remaining=[[k,r] for k in counts for r in range(a.gates-2*k)
                   if (k,r) not in prior and results.get(str(k),{}).get("status")!="UNSAT"]
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
