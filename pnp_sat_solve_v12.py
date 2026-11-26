#!/usr/bin/env python3
"""SAT v12: support-only relaxation of the v9 OR network.

UNSAT excludes the corresponding minimum-circuit case (subject to the
unformalized reduction). RELAXED_SAT is only a set of candidate supports,
not an actual circuit. No proof submission or Lean certification.
"""
import argparse
import concurrent.futures as cf
import hashlib
import itertools
import json
import multiprocessing as mp
import os
import time
from pathlib import Path
import pnp_sat_solve_v1 as v1
import pnp_sat_solve_v9 as v9
import pnp_sat_solve_v11 as v11


class Relax(v9.Encoding):
    def __init__(self,n,edges,total,k,base,budget,minimal=True):
        super().__init__(n,edges,total,k,base)
        if not 0<=budget<=self.m:raise ValueError("invalid OR budget")
        self.budget=budget
        self.minimal=minimal

    def conj(self,xs):
        z=self.fresh()
        self.equiv_and(z,xs)
        return z

    def disj(self,xs):
        z=self.fresh()
        self.equiv_or(z,xs)
        return z

    def difference(self,A,B):
        return self.disj([self.conj([a,-b]) for a,b in zip(A,B)])

    def equal(self,A,B):
        return self.conj([-self.difference(A,B),-self.difference(B,A)])

    def leq(self,A,B):
        # Unsigned mask ordering, low bit first.
        z=self.fresh()
        self.add(z)
        for a,b in zip(A,B):
            eq=self.equal([a],[b])
            z=self.disj([self.conj([-a,b]),self.conj([eq,z])])
        return z

    def build(self):
        n,k,q,r=self.n,self.k,self.atoms,self.budget
        sides=[[self.fresh() for _ in range(q)] for _ in range(2*(k+2))]
        self.sides=sides
        pairs=[sides[i:i+2] for i in range(0,len(sides),2)]
        self.pairs=pairs
        for S in sides:
            self.add(*S)
            self.atmost(S,r+1)
        for j,(A,B) in enumerate(pairs):
            self.add(self.leq(A,B))
            if self.minimal:
                self.add(self.difference(A,B))
                self.add(self.difference(B,A))
            for S in (A,B):
                if j==0:self.add(-S[n]);self.add(-S[n+1])
                elif j==1:self.add(-S[n+1])
        self.add(pairs[1][0][n],pairs[1][1][n])
        # The later junk must reach a terminal top (all real gates used).
        self.add(*(S[n+1] for S in sides[4:]))
        for j in range(2,k+1):
            self.add(self.leq(pairs[j][0],pairs[j+1][0]))
        values=[[self.fresh() for _ in self.rows] for _ in pairs]
        for ri,row in enumerate(self.rows):
            for j,(A,B) in enumerate(pairs):
                sidevals=[]
                for S in (A,B):
                    terms=[S[a] for a in range(n) if row&(1<<a)]
                    terms += [self.conj([S[n+a],values[a][ri]]) for a in range(min(2,j))]
                    sidevals.append(self.disj(terms))
                self.equiv_and(values[j][ri],sidevals)
            if v1.target(row,self.masks):
                self.add(*(values[j][ri] for j in range(2,k+2)))
            else:
                for j in range(2,k+2):self.add(-values[j][ri])
        negatives=[i for i,row in enumerate(self.rows) if not v1.target(row,self.masks)]
        positives=[i for i,row in enumerate(self.rows) if v1.target(row,self.masks)]
        for j in (0,1):self.add(*(values[j][i] for i in negatives))
        if self.minimal:
            for j in range(2,k+2):
                self.add(*(self.conj([values[j][i]]+
                    [-values[h][i] for h in range(2,k+2) if h!=j]) for i in positives))
        # h4, h5 and edge coverage. h7 follows from star centres.
        edges=[tuple(i for i in range(n) if row&(1<<i)) for row in self.masks]
        eset=set(edges)
        cflags=[]
        eligible=[]
        cover=[[] for _ in edges]
        routed=[[] for _ in edges]
        for j,(A,B) in enumerate(pairs[2:],2):
            nonempty=[self.disj(S[:n]) for S in (A,B)]
            singles=[]
            for S,ne in zip((A,B),nonempty):
                multi=self.disj([self.conj([a,b]) for a,b in itertools.combinations(S[:n],2)])
                singles.append(self.conj([ne,-multi]))
            self.add(-self.disj([self.conj([a,b]) for a,b in itertools.combinations(A[:n],2)]),
                     -self.disj([self.conj([a,b]) for a,b in itertools.combinations(B[:n],2)]))
            cflags.append(self.disj([-x for x in nonempty]))
            eligible.extend([(A,singles[1]),(B,singles[0])])
            for a in range(n):
                for b in range(n):
                    if a==b or tuple(sorted((a,b))) not in eset:self.add(-A[a],-B[b])
            for ei,(a,b) in enumerate(edges):
                cover[ei].append(self.disj([self.conj([A[a],B[b]]),self.conj([A[b],B[a]])]))
                ri=self.rows.index(self.masks[ei])
                hit=self.disj([self.conj([S[n+h],values[h][ri]]) for S in (A,B) for h in (0,1)])
                routed[ei].append(self.conj([values[j][ri],hit]))
        covered=[]
        for xs,ys in zip(cover,routed):
            z=self.disj(xs)
            covered.append(z)
            self.add(z,*ys)
        # Every DISTINCT composite support needs at least one real OR.
        # Count the first occurrence of each nonsingleton mask.
        # An OR that could be Lambda must be contained in the support
        # of a terminal operand whose opposite side is a singleton.
        # It must also contain a direct input atom.
        reps=[]
        forced_nonlam=[]
        for i,S in enumerate(sides):
            multi=self.disj([self.conj([a,b]) for a,b in itertools.combinations(S,2)])
            rep=self.conj([multi]+[-self.equal(S,T) for T in sides[:i]])
            reps.append(rep)
            possible=self.conj([self.disj(S[:n]),
                self.disj([self.conj([flag,-self.difference(S,T)]) for T,flag in eligible])])
            forced_nonlam.append(self.conj([rep,-possible]))
        self.atmost(reps,r)
        # c+b <= k+1+E-base+lam, lam <= r-forced_nonlam.
        self.atmost(cflags+covered+forced_nonlam,k+1+len(edges)-self.base+r)
        return self

    def decode_supports(self,model):
        pos={x for x in model if x>0}
        return [sum(1<<i for i,x in enumerate(S) if x in pos) for S in self.sides]

    def verify_supports(self,ss):
        n,k,r=self.n,self.k,self.budget
        assert len(ss)==2*(k+2) and all(0<x<(1<<self.atoms) for x in ss)
        pairs=list(zip(ss[::2],ss[1::2]))
        assert all(a<=b for a,b in pairs)
        assert all(a.bit_count()<=r+1 for a in ss)
        if self.minimal:assert all(a&~b and b&~a for a,b in pairs)
        assert all(a<(1<<n) for a in pairs[0])
        assert all(a<(1<<(n+1)) for a in pairs[1])
        assert (pairs[1][0]|pairs[1][1])&(1<<n)
        assert any(x&(1<<(n+1)) for x in ss[4:])
        assert all(pairs[j][0]<=pairs[j+1][0] for j in range(2,k+1))
        def evalrow(row):
            atoms=row
            out=[]
            for j,(a,b) in enumerate(pairs):
                yes=bool(a&atoms) and bool(b&atoms)
                out.append(yes)
                if j<2 and yes:atoms|=1<<(n+j)
            return out
        vv={row:evalrow(row) for row in range(1<<n)}
        assert all(any(v[2:])==v1.target(row,self.masks) for row,v in vv.items())
        assert all(any(v[j] for row,v in vv.items() if not v1.target(row,self.masks)) for j in (0,1))
        if self.minimal:
            assert all(any(vv[row][j] and sum(vv[row][2:])==1 for row in self.masks)
                       for j in range(2,k+2))
        mask=(1<<n)-1
        edges=set(self.masks)
        covered=set()
        c=0
        eligible=[]
        for A,B in pairs[2:]:
            a,b=A&mask,B&mask
            assert min(a.bit_count(),b.bit_count())<=1
            c+=not a or not b
            for i in range(n):
                for j in range(n):
                    if a&(1<<i) and b&(1<<j):
                        e=(1<<i)|(1<<j)
                        assert e in edges
                        covered.add(e)
            if a.bit_count()==1:eligible.append(B)
            if b.bit_count()==1:eligible.append(A)
        for e in edges-covered:
            vals=vv[e]
            assert any(vals[j] and any(vals[h] and S&(1<<(n+h))
                        for S in pairs[j] for h in (0,1)) for j in range(2,k+2))
        roots={S for S in ss if S.bit_count()>1}
        nonlam={S for S in roots if not(S&mask) or not any(S&~T==0 for T in eligible)}
        assert len(roots)<=r
        assert c+len(covered)+len(nonlam)<=k+1+len(edges)-self.base+r
        return {"centreless":c,"covered_edges":len(covered),"distinct_composite_roots":len(roots),
                "forced_nonlam_roots":len(nonlam),"max_lam":r-len(nonlam),
                "supports":ss}


def worker(enc,solver,conn):
    try:
        from pysat.solvers import Solver
        start=time.monotonic()
        with Solver(name=solver,bootstrap_with=enc.cnf) as sol:
            sat=sol.solve()
            out={"status":"RELAXED_SAT" if sat else "UNSAT",
                 "solve_seconds":round(time.monotonic()-start,3),"stats":sol.accum_stats()}
            if sat:out["support_candidate"]=enc.verify_supports(enc.decode_supports(sol.get_model()))
            conn.send(out)
    except Exception as e:conn.send({"status":"ERROR","error":repr(e)})
    finally:conn.close()


def run(task):
    n,edges,total,k,base,r,solver,seconds,minimal=task
    start=time.monotonic()
    enc=Relax(n,edges,total,k,base,r,minimal).build()
    meta={"top_count":k,"or_budget":r,"variables":enc.max_var,"clauses":len(enc.cnf),
          "build_seconds":round(time.monotonic()-start,3)}
    ctx=mp.get_context("fork")
    recv,send=ctx.Pipe(False)
    proc=ctx.Process(target=worker,args=(enc,solver,send),daemon=True)
    start=time.monotonic()
    proc.start();send.close()
    try:
        if recv.poll(seconds):
            try:out=recv.recv()
            except EOFError:out={"status":"ERROR","error":"worker exited"}
        else:out={"status":"TIMEOUT"}
    finally:
        recv.close()
        proc.join(.1)
        if proc.is_alive():proc.terminate();proc.join(1)
        if proc.is_alive():proc.kill();proc.join()
    return {**meta,**out,"wall_seconds":round(time.monotonic()-start,3)}


def self_test(solver):
    from pysat.solvers import Solver
    # The known v9 nonminimal circuit: junk0=1&2,
    # junk1=1&(0|1|junk0), top=0&junk1.
    # h6 equality at base=2; it requires two OR gates in the actual DAG.
    ss=[2,4,2,11,1,16]
    for budget,base,expected in ((2,2,True),(1,2,False),(2,4,False)):
        enc=Relax(3,[(0,1)],5,1,base,budget,False).build()
        ass=[x if S&(1<<i) else -x for S,bits in zip(ss,enc.sides)
             for i,x in enumerate(bits)]
        with Solver(name=solver,bootstrap_with=enc.cnf) as sol:
            assert sol.solve(assumptions=ass)==expected,(budget,base)
            if expected:enc.verify_supports(enc.decode_supports(sol.get_model()))
    # Check representative counting with two equal composite roots.
    enc=Relax(3,[(0,1)],5,1,0,2,False)
    A=[enc.fresh() for _ in range(3)]
    B=[enc.fresh() for _ in range(3)]
    eq=enc.equal(A,B)
    le=enc.leq(A,B)
    with Solver(name=solver,bootstrap_with=enc.cnf) as sol:
        for a,b in itertools.product(range(8),repeat=2):
            ass=[x if a&(1<<i) else -x for i,x in enumerate(A)]
            ass += [x if b&(1<<i) else -x for i,x in enumerate(B)]
            for x,truth in ((eq,a==b),(le,a<=b)):
                assert sol.solve(assumptions=ass+[x if truth else -x])
                assert not sol.solve(assumptions=ass+[-x if truth else x])
    print("SAT V12 SELF TEST OK",flush=True)


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--case",choices=v1.CASES,default="l2260")
    ap.add_argument("--gates",type=int,default=21)
    ap.add_argument("--jobs",type=int,default=4)
    ap.add_argument("--seconds",type=float,default=15)
    ap.add_argument("--solver",default="cadical195")
    ap.add_argument("--seed-v11",type=Path)
    ap.add_argument("--checkpoint",type=Path)
    ap.add_argument("--no-minimality",action="store_true")
    ap.add_argument("--self-test",action="store_true")
    a=ap.parse_args()
    if a.gates<3 or a.jobs<1 or a.seconds<=0:ap.error("invalid limits")
    if a.self_test:self_test(a.solver);return
    n,edges=v1.CASES[a.case]
    base=17 if a.case=="l2260" else 0
    counts=list(range((a.gates-1)//2,0,-1))
    prior={}
    if a.seed_v11:
        old=json.loads(a.seed_v11.read_text())
        expected=v11.digest([n,edges,a.gates,base,counts,"exact"],v11.FILES+("pnp_sat_solve_v11.py",))
        if old.get("fingerprint")!=expected:raise ValueError("v11 seed mismatch")
        for k in counts:
            for r in range(a.gates-2*k):
                key=f"{k}:{r}"
                if str(k) in old["inherited"] or old["results"].get(key,{}).get("status")=="UNSAT":
                    prior[key]="UNSAT"
    key=v11.digest([n,edges,a.gates,base,not a.no_minimality,prior],
                   v11.FILES+("pnp_sat_solve_v11.py","pnp_sat_solve_v12.py"))
    path=a.checkpoint
    def execute():
        start=time.monotonic()
        data={"fingerprint":key,"results":{}}
        if path and path.exists():
            data=json.loads(path.read_text())
            if data.get("fingerprint")!=key:raise ValueError("checkpoint mismatch")
        results=data["results"]
        def save():
            if path:
                tmp=path.with_name(path.name+".tmp")
                tmp.write_text(json.dumps(data,indent=2)+"\n")
                os.replace(tmp,path)
        # Start from the maximum OR budget for each remaining k.
        # UNSAT at budget r excludes ALL counts <=r, since the
        # relaxation is monotone in r.
        pending=[]
        for k in counts:
            todo=[r for r in range(a.gates-2*k) if f"{k}:{r}" not in prior]
            if todo:
                hi=max(todo)
                if results.get(str(k),{}).get("status")!="UNSAT":
                    pending.append((k,hi))
        print("[CONFIG]",json.dumps({"pending":pending,"prior_unsat":len(prior),
            "minimality":not a.no_minimality,"jobs":a.jobs,"seconds":a.seconds}),flush=True)
        with cf.ProcessPoolExecutor(max_workers=a.jobs,mp_context=mp.get_context("fork")) as pool:
            fs={pool.submit(run,(n,edges,a.gates,k,base,r,a.solver,a.seconds,not a.no_minimality)):k
                for k,r in pending}
            for f in cf.as_completed(fs):
                k=fs[f]
                try:out=f.result()
                except Exception as e:out={"status":"ERROR","error":repr(e)}
                results[str(k)]=out
                save()
                print("[RELAX CASE]",k,json.dumps(out),flush=True)
        remaining=[]
        for k in counts:
            for r in range(a.gates-2*k):
                if f"{k}:{r}" in prior:continue
                out=results.get(str(k),{})
                if out.get("status")=="UNSAT" and r<=out["or_budget"]:continue
                remaining.append([k,r])
        print("[SUMMARY]",json.dumps({"remaining":remaining,"remaining_count":len(remaining),
          "status":"UNRESOLVED" if remaining else "UNSAT",
          "wall_seconds":round(time.monotonic()-start,3)}),flush=True)
        if any(x.get("status")=="ERROR" for x in results.values()):raise SystemExit(1)
    if path:
        import fcntl
        path.parent.mkdir(parents=True,exist_ok=True)
        with open(str(path)+".lock","a") as lock:
            fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
            execute()
    else:execute()


if __name__=="__main__":main()
