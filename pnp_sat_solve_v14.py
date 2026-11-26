#!/usr/bin/env python3
"""SAT v14: corrected CEGAR oracle with resumable v13 cuts.

The outer solver proposes supports; the inner solver either realizes them
or returns an UNSAT assumption core. The negated core becomes an outer
clause. All cuts are from the exact oracle, not from heuristics.
The reduction has not been formalized in Lean.
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
import pnp_sat_solve_v9 as v9
import pnp_sat_solve_v11 as v11
import pnp_sat_solve_v12 as v12


class Oracle(v9.Encoding):
    def pair(self,count,active=None):
        # Outer operands are sorted by support mask, not source index.
        # Keep OR source ordering, but remove AND source ordering.
        if active is None:
            A,B=self.source(count),self.source(count)
            # Remove ordering only, not the distinct-input constraint.
            for a,b in zip(A[0],B[0]):self.add(-a,-b)
            return A,B
        return super().pair(count,active)

    def build(self):
        super().build()
        # Remove v9's terminal top order by source index, which need not
        # agree with v12's order by support mask. No semantic constraints
        # are removed by this change of symmetry convention.
        remove=set()
        for j in range(2,self.k+1):
            for a,x in enumerate(self.ands[j][0][0]):
                for b in range(a):
                    remove.add((-x,-self.ands[j+1][0][0][b]))
        self.cnf=[c for c in self.cnf if tuple(c) not in remove]
        self.sidebits=[bits for pair in self.ands for _,bits in pair]
        return self


class Relax(v12.Relax):
    def build(self):
        super().build()
        # For a root S the union cone must contain >= |S|-1 ORs.
        # Distinct composite roots outside that cone each need another
        # OR. Every OR in the cone has support contained in S.
        # Thus |S| + #distinct composite roots not subset S <= budget+1.
        reps=[]
        for i,S in enumerate(self.sides):
            multi=self.disj([self.conj([a,b]) for ai,a in enumerate(S)
                              for b in S[ai+1:]])
            reps.append(self.conj([multi]+[-self.equal(S,T) for T in self.sides[:i]]))
        for S in self.sides:
            outside=[self.conj([rep,self.difference(T,S)])
                     for rep,T in zip(reps,self.sides)]
            self.atmost(S+outside,self.budget+1)
        return self


def bits_for(ss,groups):
    return [x if S&(1<<i) else -x for S,bits in zip(ss,groups)
            for i,x in enumerate(bits)]


def core_clause(core,ass,mapping):
    # A missing core falls back to the full fixed assignment. An empty
    # core means the oracle itself is UNSAT.
    if core is None:core=ass
    if not set(core)<=set(ass):raise ValueError("invalid assumption core")
    return sorted(set(-mapping[x] for x in core),key=lambda x:(abs(x),x))


def worker(task,conn):
    n,edges,total,k,base,r,outer_name,inner_name,old_cuts,minimal=task
    t=time.monotonic()
    outer=Relax(n,edges,total,k,base,r,minimal).build()
    inner=Oracle(n,edges,2*k+1+r,k,base).build()
    ovars=[x for S in outer.sides for x in S]
    ivars=[x for S in inner.sidebits for x in S]
    mapping={sign*i:sign*o for i,o in zip(ivars,ovars) for sign in (-1,1)}
    if len(ivars)!=len(ovars):raise ValueError("side variable mismatch")
    if any(any(abs(x) not in set(ovars) for x in cut) for cut in old_cuts):
        raise ValueError("invalid checkpoint cut")
    from pysat.solvers import Solver
    cuts=list(old_cuts)
    sent=len(cuts)
    candidates=0
    start=time.monotonic()
    meta={"top_count":k,"or_budget":r,"outer_clauses":len(outer.cnf),
          "inner_clauses":len(inner.cnf),"outer_variables":outer.max_var,
          "inner_variables":inner.max_var,"build_seconds":round(start-t,3)}
    try:
        with Solver(name=outer_name,bootstrap_with=outer.cnf+cuts) as osol, \
             Solver(name=inner_name,bootstrap_with=inner.cnf) as isol:
            last=0
            def report(status,**kwargs):
                nonlocal sent,last
                out={**meta,"status":status,"candidates":candidates,
                     "cut_count":len(cuts),"new_cuts":cuts[sent:],
                     "solve_seconds":round(time.monotonic()-start,3),
                     "outer_stats":osol.accum_stats(),"inner_stats":isol.accum_stats(),**kwargs}
                conn.send(out)
                sent=len(cuts)
                last=time.monotonic()
            report("PROGRESS")
            while True:
                if not osol.solve():
                    report("UNSAT")
                    break
                ss=outer.decode_supports(osol.get_model())
                # A SAT candidate is checked against all original v12
                # relaxation conditions before it is passed to the oracle.
                outer.verify_supports(ss)
                ass=bits_for(ss,inner.sidebits)
                candidates+=1
                if isol.solve(assumptions=ass):
                    w=inner.decode(isol.get_model())
                    check=v4.check_star(n,inner.masks,w,base,True)
                    if not v1.verify(n,inner.masks,w) or not check["valid"]:
                        report("MODEL_INVALID",witness=w,structure_check=check)
                    else:
                        report("SAT",witness=w,structure_check=check,
                               verified_full_truth_table=True,
                               support_candidate=ss)
                    break
                cut=core_clause(isol.get_core(),ass,mapping)
                if cut in cuts:raise RuntimeError("repeated blocked core")
                cuts.append(cut)
                osol.add_clause(cut)
                if not cut:
                    report("UNSAT")
                    break
                if time.monotonic()-last>=.5 or len(cuts)-sent>=32:
                    report("PROGRESS")
    finally:
        conn.close()


def guarded(task,conn):
    try:
        worker(task,conn)
    except Exception as e:
        try:conn.send({"status":"ERROR","error":repr(e)})
        except (OSError,BrokenPipeError):pass
    finally:conn.close()


def run(task,seconds):
    ctx=mp.get_context("fork")
    recv,send=ctx.Pipe(False)
    proc=ctx.Process(target=guarded,args=(task,send),daemon=True)
    start=time.monotonic()
    proc.start();send.close()
    cuts=list(task[-2])
    last={}
    out={}
    try:
        while True:
            left=seconds-(time.monotonic()-start)
            if left<=0 or not recv.poll(left):
                out={**last,"status":"TIMEOUT"}
                break
            try:r=recv.recv()
            except EOFError:
                out={"status":"ERROR","error":"worker exited"}
                break
            cuts.extend(r.pop("new_cuts",[]))
            last=r
            if r["status"]!="PROGRESS":
                out=r
                break
    finally:
        recv.close()
        proc.join(.1)
        if proc.is_alive():proc.terminate();proc.join(1)
        if proc.is_alive():proc.kill();proc.join()
    return {**out,"cuts":cuts,"cut_count":len(cuts),
            "wall_seconds":round(time.monotonic()-start,3)}


def self_test(outer_name,inner_name):
    from pysat.solvers import Solver
    # A v9 witness; support order differs from source order for junk1.
    n,edges,k,r,base=3,[(0,1)],1,2,2
    outer=Relax(n,edges,5,k,base,r,False).build()
    inner=Oracle(n,edges,5,k,base).build()
    ss=[2,4,2,11,1,16]
    ass=bits_for(ss,inner.sidebits)
    with Solver(name=outer_name,bootstrap_with=outer.cnf) as s:
        assert s.solve(assumptions=bits_for(ss,outer.sides))
        outer.verify_supports(ss)
    with Solver(name=inner_name,bootstrap_with=inner.cnf) as s:
        assert s.solve(assumptions=ass)
        w=inner.decode(s.get_model())
        assert v1.verify(n,inner.masks,w)
        assert v4.check_star(n,inner.masks,w,base,True)["valid"]
        # An empty mandatory operand must be impossible; test the core
        # mapping and that the resulting clause blocks this assignment.
        bad=ss[:];bad[0]=0
        ass=bits_for(bad,inner.sidebits)
        assert not s.solve(assumptions=ass)
        mapping={sign*i:sign*o for I,O in zip(inner.sidebits,outer.sides)
                 for i,o in zip(I,O) for sign in (-1,1)}
        core=s.get_core()
        cut=core_clause(core,ass,mapping)
        assert all(-x in bits_for(bad,outer.sides) for x in cut)
        # Recheck the returned core independently against the oracle.
        if core is not None:assert not s.solve(assumptions=core)
    for total,budget,expected in ((3,0,"UNSAT"),(5,2,"SAT")):
        got=run((3,[(0,1)],total,1,0,budget,outer_name,inner_name,[],False),10)
        print("[TEST]",json.dumps({k:v for k,v in got.items() if k!="cuts"}),flush=True)
        assert got["status"]==expected,got
    # Regression for the reported v13 model:
    # junk0 = x1 & x1, junk1 = junk0 & junk0.
    # Equal-source gates are forbidden even in --no-minimality mode.
    inner=Oracle(3,[(0,1)],3,1,0).build()
    with Solver(name=inner_name,bootstrap_with=inner.cnf) as s:
        assert not s.solve(assumptions=bits_for([2,2,8,8,1,16],inner.sidebits))
    print("SAT V14 SELF TEST OK",flush=True)


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--case",choices=v1.CASES,default="l2260")
    ap.add_argument("--gates",type=int,default=21)
    ap.add_argument("--jobs",type=int,default=4)
    ap.add_argument("--seconds",type=float,default=60)
    ap.add_argument("--outer",default="cadical195")
    ap.add_argument("--inner",default="g4")
    ap.add_argument("--seed-v11",type=Path)
    ap.add_argument("--checkpoint",type=Path)
    ap.add_argument("--seed-v13",type=Path,help="import compatible v13 UNSAT results and cuts")
    ap.add_argument("--no-minimality",action="store_true")
    ap.add_argument("--self-test",action="store_true")
    a=ap.parse_args()
    if a.gates<3 or a.jobs<1 or a.seconds<=0:ap.error("invalid limits")
    if a.self_test:self_test(a.outer,a.inner);return
    n,edges=v1.CASES[a.case]
    base=17 if a.case=="l2260" else 0
    counts=list(range((a.gates-1)//2,0,-1))
    prior=set()
    if a.seed_v11:
        old=json.loads(a.seed_v11.read_text())
        expected=v11.digest([n,edges,a.gates,base,counts,"exact"],v11.FILES+("pnp_sat_solve_v11.py",))
        if old.get("fingerprint")!=expected:raise ValueError("v11 seed mismatch")
        for k in counts:
            for r in range(a.gates-2*k):
                if str(k) in old["inherited"] or old["results"].get(f"{k}:{r}",{}).get("status")=="UNSAT":
                    prior.add((k,r))
    jobs=[]
    for k in counts:
        rr=[r for r in range(a.gates-2*k) if (k,r) not in prior]
        if rr:jobs.append((k,max(rr)))
    params=[n,edges,a.gates,base,jobs,not a.no_minimality]
    deps=v11.FILES+("pnp_sat_solve_v11.py","pnp_sat_solve_v12.py")
    key=v11.digest(params,deps+("pnp_sat_solve_v13.py","pnp_sat_solve_v14.py"))
    seed={}
    if a.seed_v13:
        old=json.loads(a.seed_v13.read_text())
        if old.get("fingerprint")!=v11.digest(params,deps+("pnp_sat_solve_v13.py",)):
            raise ValueError("v13 seed mismatch")
        # Outer formula and variable numbering unchanged. The corrected
        # inner formula is strictly stronger. Old UNSAT cores remain valid.
        # Never import an old SAT witness or an ERROR status.
        for k,r in jobs:
            prev=old.get("results",{}).get(str(k),{})
            if prev.get("status") in ("UNSAT","TIMEOUT"):
                seed[str(k)]={**prev,"inherited_from_v13":True}
    path=a.checkpoint
    def execute():
        start=time.monotonic()
        data={"fingerprint":key,"results":{}}
        if path and path.exists():
            data=json.loads(path.read_text())
            if data.get("fingerprint")!=key:raise ValueError("checkpoint mismatch")
        results=data["results"]
        for k,r in seed.items():
            if k not in results:results[k]=r
        def save():
            if path:
                tmp=path.with_name(path.name+".tmp")
                tmp.write_text(json.dumps(data,indent=2)+"\n")
                os.replace(tmp,path)
        save()
        pending=[(k,r) for k,r in jobs if results.get(str(k),{}).get("status")!="UNSAT"]
        print("[CONFIG]",json.dumps({"pending":pending,"prior_unsat":len(prior),
              "jobs":a.jobs,"seconds":a.seconds,"outer":a.outer,"inner":a.inner,
              "resumed_cuts":sum(len(x.get("cuts",[])) for x in results.values())}),flush=True)
        if not any(x.get("status")=="SAT" for x in results.values()):
            with cf.ProcessPoolExecutor(max_workers=a.jobs,mp_context=mp.get_context("fork")) as pool:
                fs={}
                for k,r in pending:
                    task=(n,edges,a.gates,k,base,r,a.outer,a.inner,
                          results.get(str(k),{}).get("cuts",[]),not a.no_minimality)
                    fs[pool.submit(run,task,a.seconds)]=k
                for f in cf.as_completed(fs):
                    k=fs[f]
                    try:out=f.result()
                    except Exception as e:out={"status":"ERROR","error":repr(e)}
                    results[str(k)]=out
                    save()
                    print("[CEGAR]",k,json.dumps({x:y for x,y in out.items() if x!="cuts"}),flush=True)
        remaining=[[k,r] for k in counts for r in range(a.gates-2*k)
                   if (k,r) not in prior and results.get(str(k),{}).get("status")!="UNSAT"]
        states=[x.get("status") for x in results.values()]
        state=("ERROR" if any(s in ("ERROR","MODEL_INVALID") for s in states) else
               "SAT" if "SAT" in states else "UNRESOLVED" if remaining else "UNSAT")
        print("[SUMMARY]",json.dumps({"status":state,"remaining":remaining,
               "remaining_count":len(remaining),"cuts":sum(len(x.get("cuts",[])) for x in results.values()),
               "wall_seconds":round(time.monotonic()-start,3)}),flush=True)
        if state=="ERROR":raise SystemExit(1)
    if path:
        import fcntl
        path.parent.mkdir(parents=True,exist_ok=True)
        with open(str(path)+".lock","a") as lock:
            fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
            execute()
    else:execute()


if __name__=="__main__":main()
