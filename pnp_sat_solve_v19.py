#!/usr/bin/env python3
"""SAT v19: graph maximal-independent-set input exposure.

Add necessary direct-reader constraints for every maximal false row I
and vertex v outside I. Split the remaining exact OR counts, retaining
v16 support cuts that hold for the whole OR budget.
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


class Compact(v14.Oracle):
    def conj(self,xs):
        z=self.fresh()
        self.equiv_and(z,xs)
        return z

    def disj(self,xs):
        z=self.fresh()
        self.equiv_or(z,xs)
        return z

    def leq(self,A,B,strict=False):
        # At each higher bit z = majority(not a, b, previous).
        # Equal high bits preserve the lower-bit comparison.
        prev=self.fresh()
        self.add(-prev if strict else prev)
        for a,b in zip(A,B):
            z=self.fresh()
            for x,y in ((-a,b),(-a,prev),(b,prev)):
                self.add(-x,-y,z)
                self.add(x,y,-z)
            prev=z
        return prev

    def difference(self,A,B):
        return self.disj([self.conj([a,-b]) for a,b in zip(A,B)])

    def private_edges(self):
        # Only positive edge rows are needed for private-edge
        # minimality. The full boundary evaluation is already in v9.
        values=[]
        for row in self.masks:
            vals=[]
            for j,pair in enumerate(self.ands):
                sides=[]
                for _,S in pair:
                    terms=[S[a] for a in range(self.n) if row&(1<<a)]
                    terms += [self.conj([S[self.n+a],vals[a]])
                              for a in range(min(j,2))]
                    sides.append(self.disj(terms))
                vals.append(self.conj(sides))
            values.append(vals)
        for j in range(2,self.k+2):
            self.add(*(self.conj([vals[j]]+
                      [-vals[h] for h in range(2,self.k+2) if h!=j])
                       for vals in values))

    def graph_exposure(self):
        # For maximal independent I and v outside I, f(I)=0,
        # f(I+v)=1. If v has no direct AND reader, at least one
        # direct OR reader must have no original input atom in I.
        # Otherwise every first reader of v is unchanged (true) on
        # both inputs, and induction over the physical DAG implies
        # the output is unchanged. Dirty atoms need not be evaluated.
        n=self.n
        neg=[row for row in self.rows if not v1.target(row,self.masks)]
        for I in neg:
            for v in range(n):
                if not I&(1<<v) and not v1.target(I|(1<<v),self.masks):
                    raise ValueError("expected maximal independent boundary rows")
        direct_and=[self.disj([sel[v] for pair in self.ands for sel,_ in pair])
                    for v in range(n)]
        direct_or=[[self.disj([A[0][v],B[0][v]]) for A,B in self.ors]
                   for v in range(n)]
        count=0
        for I in neg:
            clear=[self.conj([-S[a] for a in range(n) if I&(1<<a)])
                   for S in self.support]
            for v in range(n):
                if I&(1<<v):continue
                # One-way witnesses suffice; no reverse implication.
                hits=[]
                for j in range(self.m):
                    z=self.fresh()
                    self.add(-z,direct_or[v][j])
                    self.add(-z,clear[j])
                    hits.append(z)
                self.add(direct_and[v],*hits)
                count+=1
        return count

    def prune(self,minimal,canonical):
        for A,B in self.ands:
            self.add(self.leq(A[1],B[1]))
            if minimal:
                self.add(self.difference(A[1],B[1]))
                self.add(self.difference(B[1],A[1]))
        for j in range(2,self.k+1):
            self.add(self.leq(self.ands[j][0][1],self.ands[j+1][0][1]))
        if minimal:
            for active,(A,B) in zip(self.active,self.ors):
                self.add(-active,self.difference(A[1],B[1]))
                self.add(-active,self.difference(B[1],A[1]))
            self.private_edges()
            if canonical:
                # In a minimum circuit OR masks are distinct and
                # increase strictly along every OR->OR dependency.
                for j in range(1,self.m):
                    self.add(-self.active[j-1],
                             self.leq(self.support[j-1],self.support[j],True))
        return self


def build(n,edges,total,k,base,r,cuts,minimal=True,mode="compact"):
    inner=Compact(n,edges,2*k+1+r,k,base).build()
    original_vars=inner.max_var
    original_clauses=len(inner.cnf)
    inner.prune(minimal,mode=="canonical")
    before_exposure=len(inner.cnf)
    exposure_count=inner.graph_exposure()
    exposure_clauses=len(inner.cnf)-before_exposure
    # v12/v14/v16 reserve consecutive operand support variables
    # before allocating anything else. Reconstruct that layout directly.
    inner_bits=[x for group in inner.sidebits for x in group]
    if len(inner_bits)!=2*(k+2)*(n+2) or len(set(inner_bits))!=len(inner_bits):
        raise ValueError("side variable mismatch")
    mapping=dict(enumerate(inner_bits,1))
    seen=set()
    for cut in cuts:
        if any(abs(x) not in mapping for x in cut):
            raise ValueError("checkpoint cut outside support variables")
        cc=tuple(sorted(set(cut),key=lambda x:(abs(x),x)))
        if cc in seen:continue
        seen.add(cc)
        inner.cnf.append([mapping[x] if x>0 else -mapping[-x] for x in cc])
    meta={"top_count":k,"or_budget":r,"outer_mode":mode,
          "variables":inner.max_var,"clauses":len(inner.cnf),
          "inner_variables":original_vars,"inner_clauses":original_clauses,
          "extra_prune_clauses":before_exposure-original_clauses,
          "exposure_conditions":exposure_count,"exposure_clauses":exposure_clauses,
          "shared_variables":len(inner_bits),"imported_cuts":len(seen)}
    return inner,None,mapping,meta


def run(task):
    n,edges,total,k,base,r,solver,seconds,chunk,cuts,minimal,mode,exact=task
    t=time.monotonic()
    enc,_,_,meta=build(n,edges,total,k,base,r,cuts,minimal,mode)
    if exact is not None:
        enc.cnf.extend([[x] for x in v11.exact_units(enc.active,exact)])
    meta.update(exact_or_count=exact,clauses=len(enc.cnf),solver=solver,
                build_seconds=round(time.monotonic()-t,3))
    print("[CNF]",json.dumps(meta),flush=True)
    out=v4.solve(enc,"full",base,solver,seconds,chunk)
    return {**meta,**out}


def self_test(solver,seconds,chunk):
    from pysat.solvers import Solver
    from itertools import product
    enc=Compact(3,[(0,1)],5,1,0)
    A=[enc.fresh() for _ in range(3)]
    B=[enc.fresh() for _ in range(3)]
    le=enc.leq(A,B)
    lt=enc.leq(A,B,True)
    with Solver(name=solver,bootstrap_with=enc.cnf) as s:
        for a,b in product(range(8),repeat=2):
            ass=v14.bits_for([a,b],[A,B])
            for x,t in ((le,a<=b),(lt,a<b)):
                assert s.solve(assumptions=ass+[x if t else -x])
                assert not s.solve(assumptions=ass+[-x if t else x])
    ss=[2,4,2,11,1,16]
    for mode in ("compact","canonical"):
        inner,_,mapping,meta=build(3,[(0,1)],5,1,2,2,[],False,mode)
        ass=v14.bits_for(ss,inner.sidebits)
        with Solver(name=solver,bootstrap_with=inner.cnf) as s:
            assert s.solve(assumptions=ass)
            w=inner.decode(s.get_model())
            assert v1.verify(3,inner.masks,w)
            assert v4.check_star(3,inner.masks,w,2,True)["valid"]
        groups=[list(range(i*5+1,i*5+6)) for i in range(6)]
        cut=[-x for x in v14.bits_for(ss,groups)]
        blocked,_,_,_=build(3,[(0,1)],5,1,2,2,[cut],False,mode)
        with Solver(name=solver,bootstrap_with=blocked.cnf) as s:
            assert not s.solve(assumptions=ass)
        # Same witness has a comparable AND operand pair, so
        # minimality must exclude it.
        pruned,_,_,_=build(3,[(0,1)],5,1,2,2,[],True,mode)
        with Solver(name=solver,bootstrap_with=pruned.cnf) as s:
            assert not s.solve(assumptions=ass)
        # Known support-antichain witness from v10:
        # junk0=x0&x2, junk1=x3&junk0, top=x1&(x0|junk1).
        good=[1,4,8,16,2,33]
        pruned,_,_,_=build(4,[(0,1)],4,1,0,1,[],True,mode)
        with Solver(name=solver,bootstrap_with=pruned.cnf) as s:
            assert s.solve(assumptions=v14.bits_for(good,pruned.sidebits))
            w=pruned.decode(s.get_model())
            assert v1.verify(4,pruned.masks,w)
            assert v4.check_star(4,pruned.masks,w,0,True)["valid"]
        for total,r,expected in ((3,0,"UNSAT"),(5,2,"SAT")):
            got=run((3,[(0,1)],total,1,0,r,solver,seconds,chunk,[],False,mode,None))
            print("[TEST]",json.dumps(got),flush=True)
            assert got["status"]==expected,got
    # Independently enumerate all 1..3-gate AND/OR circuits on 3
    # inputs. For every circuit computing a nonempty graph function,
    # check exposure directly on its concrete OR-support closure.
    import itertools
    checks=0
    n=3
    edges=list(itertools.combinations(range(n),2))
    targets={}
    for em in range(1,1<<len(edges)):
        masks=[(1<<a)|(1<<b) for i,(a,b) in enumerate(edges) if em&(1<<i)]
        truth=tuple(any(row&e==e for e in masks) for row in range(1<<n))
        targets[truth]=[I for I in range(1<<n) if not truth[I] and
            all(truth[I|(1<<v)] for v in range(n) if not I&(1<<v))]
    def walk(gates,values,supports):
        nonlocal checks
        if gates and values[-1] in targets:
            for I in targets[values[-1]]:
                for v in range(n):
                    if I&(1<<v):continue
                    assert any(v in (a,b) and
                        (op=="and" or not supports[n+j]&I)
                        for j,(op,a,b) in enumerate(gates)),(gates,I,v)
                    checks+=1
        if len(gates)==3:return
        for a,b in itertools.combinations(range(len(values)),2):
            for op in ("and","or"):
                val=tuple((x and y) if op=="and" else (x or y)
                          for x,y in zip(values[a],values[b]))
                sup=(supports[a]|supports[b]) if op=="or" else 0
                walk(gates+[(op,a,b)],values+[val],supports+[sup])
    walk([], [tuple(bool(row&(1<<v)) for row in range(1<<n))
              for v in range(n)], [1<<v for v in range(n)])
    assert checks>0
    print("GRAPH EXPOSURE SELF TEST OK",checks,flush=True)
    print("SAT V19 SELF TEST OK",flush=True)


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--case",choices=v1.CASES,default="l2260")
    ap.add_argument("--gates",type=int,default=21)
    ap.add_argument("--jobs",type=int,default=3)
    ap.add_argument("--seconds",type=float,default=600)
    ap.add_argument("--solver",default="cadical195")
    ap.add_argument("--solver-for",action="append",default=[],metavar="K=SOLVER")
    ap.add_argument("--chunk",type=int,default=20000)
    ap.add_argument("--outer-mode",choices=("compact","canonical"),default="compact")
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
    key=v11.digest(params+[a.outer_mode,seed_hash,"exact-cubes"],DEPS+("pnp_sat_solve_v19.py",))
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
        def known(k,r):
            return ((k,r) in prior or
                    results.get(str(k),{}).get("status")=="UNSAT" or
                    results.get(f"{k}:{r}",{}).get("status")=="UNSAT")
        pending=[(k,budget,r) for k,budget in jobs for r in range(budget+1)
                 if not known(k,r)]
        pending.sort(key=lambda t:(t[2],-t[0]))
        print("[CONFIG]",json.dumps({"pending":pending,"prior_unsat":len(prior),
            "imported_cuts":sum(len(seed.get(str(k),{}).get("cuts",[]))
                                for k,b in jobs if any(p[0]==k for p in pending)),
            "jobs":a.jobs,"seconds":a.seconds,"solver":a.solver,"solver_for":overrides,
            "outer_mode":a.outer_mode}),flush=True)
        if not any(x.get("status")=="SAT" for x in results.values()):
            with cf.ProcessPoolExecutor(max_workers=a.jobs,mp_context=mp.get_context("fork")) as pool:
                fs={}
                todo=iter(pending)
                def fill():
                    while len(fs)<a.jobs:
                        item=next(todo,None)
                        if item is None:break
                        k,budget,r=item
                        cuts=seed.get(str(k),{}).get("cuts",[])
                        task=(n,edges,a.gates,k,base,budget,overrides.get(k,a.solver),
                              a.seconds,a.chunk,cuts,minimal,a.outer_mode,r)
                        fs[pool.submit(run,task)]=(k,r)
                fill()
                stop=False
                while fs:
                    done,_=cf.wait(fs,return_when=cf.FIRST_COMPLETED)
                    for f in done:
                        k,r=fs.pop(f)
                        try:out=f.result()
                        except Exception as e:out={"status":"ERROR","error":repr(e)}
                        if out.get("status")=="SAT" and out["witness"]["internal_or_gates"]!=r:
                            out.update(status="MODEL_INVALID",error="wrong exact OR count")
                        results[f"{k}:{r}"]=out
                        save()
                        print("[GRAPH CUBE]",k,r,json.dumps(out),flush=True)
                        if out.get("status") in ("SAT","ERROR","MODEL_INVALID"):stop=True
                    if not stop:fill()
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
