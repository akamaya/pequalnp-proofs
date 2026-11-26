#!/usr/bin/env python3
"""SAT v9: factor the two junk ANDs out as named OR atoms.

The OR network is an ordered union DAG over n input atoms and two junk
AND atoms. Junk operands cannot contain their own or later junk atom.
Top ANDs are terminal; their clean output OR network is reconstructed.
This is an experimental encoding, not a verified Lean reduction.
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
import pnp_sat_solve_v4 as v4


class Encoding:
    def __init__(self,n,edges,total,k,base):
        self.n=n
        self.masks=v1.graph(n,edges)
        self.rows=v1.rows_for(n,self.masks)
        self.total,self.k,self.base=total,k,base
        self.m=total-2*k-1
        if self.m<0 or not self.masks or k<1:raise ValueError("invalid case")
        self.atoms=n+2
        self.cnf=[]
        self.max_var=0
        self.support=[]
        self.active=[]
        self.ors=[]
        self.ands=[]

    def fresh(self):
        self.max_var+=1
        return self.max_var

    def add(self,*xs):self.cnf.append(list(xs))

    def equiv_or(self,z,xs):
        for x in xs:self.add(-x,z)
        self.add(-z,*xs)

    def equiv_and(self,z,xs):
        for x in xs:self.add(-z,x)
        self.add(z,*(-x for x in xs))

    def atmost(self,xs,b):
        from pysat.card import CardEnc,EncType
        if b<0:self.add()
        elif b<len(xs):
            f=CardEnc.atmost(lits=xs,bound=b,top_id=self.max_var,encoding=EncType.seqcounter)
            self.max_var=max(self.max_var,f.nv)
            self.cnf.extend(f.clauses)

    def source(self,count,active=None):
        sels=[self.fresh() for _ in range(count)]
        self.add(*sels) if active is None else self.add(-active,*sels)
        for a,b in itertools.combinations(sels,2):self.add(-a,-b)
        for i,x in enumerate(sels):
            if active is not None:self.add(-x,active)
            if i>=self.atoms:self.add(-x,self.active[i-self.atoms])
        bits=[self.fresh() for _ in range(self.atoms)]
        for i,x in enumerate(sels):
            for a,z in enumerate(bits):
                if i<self.atoms:self.add(-x,z if i==a else -z)
                else:
                    y=self.support[i-self.atoms][a]
                    self.add(-x,-z,y)
                    self.add(-x,z,-y)
        if active is not None:
            for z in bits:self.add(active,-z)
        return sels,bits

    def pair(self,count,active=None):
        A,B=(self.source(count,active) for _ in range(2))
        for a,x in enumerate(A[0]):
            for b in range(a+1):
                self.add(-x,-B[0][b])
        return A,B

    def build(self):
        n,k,m,q=self.n,self.k,self.m,self.atoms
        # ORs in topological order, with inactive prefix padding.
        for j in range(m):
            active=self.fresh()
            self.active.append(active)
            if j:self.add(-self.active[j-1],active)
            A,B=self.pair(q+j,active)
            bits=[self.fresh() for _ in range(q)]
            for a,z in enumerate(bits):self.equiv_or(z,[A[1][a],B[1][a]])
            self.support.append(bits)
            self.ors.append((A,B))
        # Named junk ANDs followed by terminal top ANDs.
        for j in range(k+2):
            A,B=self.pair(q+m)
            self.ands.append((A,B))
            for _,bits in (A,B):
                if j==0:self.add(-bits[n]);self.add(-bits[n+1])
                elif j==1:self.add(-bits[n+1])
        self.add(self.ands[1][0][1][n],self.ands[1][1][1][n])
        # Symmetry: the terminal top ANDs can be sorted by first source.
        for j in range(2,k+1):
            for a,x in enumerate(self.ands[j][0][0]):
                for b in range(a):self.add(-x,-self.ands[j+1][0][0][b])
        values=[[self.fresh() for _ in self.rows] for _ in self.ands]
        for ri,r in enumerate(self.rows):
            positive=v1.target(r,self.masks)
            for j,(A,B) in enumerate(self.ands):
                sides=[]
                for _,bits in (A,B):
                    terms=[bits[a] for a in range(n) if r&(1<<a)]
                    for a in range(min(j,2)):
                        x=self.fresh()
                        self.equiv_and(x,[bits[n+a],values[a][ri]])
                        terms.append(x)
                    z=self.fresh()
                    self.equiv_or(z,terms)
                    sides.append(z)
                self.equiv_and(values[j][ri],sides)
                if j>=2 and not positive:self.add(-values[j][ri])
            if positive:self.add(*(values[j][ri] for j in range(2,k+2)))
        neg=[i for i,r in enumerate(self.rows) if not v1.target(r,self.masks)]
        for j in (0,1):self.add(*(values[j][i] for i in neg))
        # h4: star sides; centreless; h5: uncovered edge reads a
        # dirty AND true at that pair, through ORs only.
        edges=[tuple(i for i in range(n) if r&(1<<i)) for r in self.masks]
        eset=set(edges)
        rowidx={r:i for i,r in enumerate(self.rows)}
        covered=[[] for _ in edges]
        routed=[[] for _ in edges]
        centreless=[]
        leaves=[[] for _ in range(m)]
        for j in range(2,k+2):
            (sa,A),(sb,B)=self.ands[j]
            ne=[]
            single=[]
            for bits in (A,B):
                z=self.fresh();self.equiv_or(z,bits[:n]);ne.append(z)
                pairs=[]
                for a,b in itertools.combinations(bits[:n],2):
                    p=self.fresh();self.equiv_and(p,[a,b]);pairs.append(p)
                z=self.fresh();self.equiv_and(z,[ne[-1]]+[-p for p in pairs])
                single.append(z)
            c=self.fresh();self.equiv_or(c,[-ne[0],-ne[1]])
            centreless.append(c)
            # Either side has at most one direct input.
            pick=self.fresh()
            for e,bits in enumerate((A,B)):
                for a,b in itertools.combinations(bits[:n],2):
                    self.add(pick if e==0 else -pick,-a,-b)
            for a in range(n):
                for b in range(n):
                    if a==b or tuple(sorted((a,b))) not in eset:self.add(-A[a],-B[b])
            # Sources of eligible leaf operands for Lambda reachability.
            for h in range(m):
                for sel,other in ((sa,single[1]),(sb,single[0])):
                    z=self.fresh();self.equiv_and(z,[sel[q+h],other])
                    leaves[h].append(z)
            for e,((u,w),r) in enumerate(zip(edges,self.masks)):
                x,y,z=self.fresh(),self.fresh(),self.fresh()
                self.equiv_and(x,[A[u],B[w]])
                self.equiv_and(y,[A[w],B[u]])
                self.equiv_or(z,[x,y]);covered[e].append(z)
                terms=[]
                ri=rowidx[r]
                for bits in (A,B):
                    for a in (0,1):
                        t=self.fresh()
                        self.equiv_and(t,[bits[n+a],values[a][ri]])
                        terms.append(t)
                z=self.fresh();self.equiv_or(z,terms)
                hit=self.fresh();self.equiv_and(hit,[z,values[j][ri]])
                routed[e].append(hit)
        edge_covered=[]
        for e in range(len(edges)):
            z=self.fresh();self.equiv_or(z,covered[e]);edge_covered.append(z)
            self.add(z,*routed[e])
        # h7 is implied by h4: select a singleton centre from each
        # non-centreless top. The resulting vertices cover starEdges.
        # Compute exact OR reachability backwards from eligible leaves.
        reach=[self.fresh() for _ in range(m)]
        lam=[self.fresh() for _ in range(m)]
        for h in reversed(range(m)):
            hits=leaves[h][:]
            for j in range(h+1,m):
                for sels,bits in self.ors[j]:
                    z=self.fresh();self.equiv_and(z,[reach[j],sels[q+h]])
                    hits.append(z)
            self.equiv_or(reach[h],hits)
            ne=[]
            for _,bits in self.ors[h]:
                z=self.fresh();self.equiv_or(z,bits[:n]);ne.append(z)
            self.equiv_and(lam[h],[self.active[h],reach[h],*ne])
        # Exact h6 after cancellation:
        # base+k+c+(active-lam) <= 2*k+1+active + (E-covered)
        # c+covered-lam <= k+1+E-base.
        self.atmost(centreless+edge_covered+[-x for x in lam],
                    k+1+len(edges)-self.base+m)
        return self

    def decode(self,model):
        pos={x for x in model if x>0}
        n,q,m=self.n,self.atoms,self.m
        gates=[]
        memo={i:i for i in range(n)}
        visiting=set()
        def resolve(w):
            if w in memo:return memo[w]
            if w in visiting:raise ValueError("cyclic symbolic network")
            visiting.add(w)
            if w<q:op="and";pair=self.ands[w-n]
            else:
                if self.active[w-q] not in pos:raise ValueError("inactive OR source")
                op="or";pair=self.ors[w-q]
            a,b=(resolve(next(i for i,x in enumerate(sels) if x in pos))
                 for sels,_ in pair)
            memo[w]=n+len(gates)
            gates.append((op,a,b))
            visiting.remove(w)
            return memo[w]
        resolve(n);resolve(n+1)
        for j in range(m):
            if self.active[j] in pos:resolve(q+j)
        tops=[]
        for A,B in self.ands[2:]:
            a,b=(resolve(next(i for i,x in enumerate(sels) if x in pos))
                 for sels,_ in (A,B))
            tops.append(n+len(gates));gates.append(("and",a,b))
        out=tops[0]
        for w in tops[1:]:
            gates.append(("or",out,w));out=n+len(gates)-1
        if len(gates)>self.total:raise ValueError("gate bound violated")
        return {"gates":gates,"output":out,"top_count":self.k,
                "internal_or_gates":sum(x in pos for x in self.active)}


def run(task):
    n,edges,total,k,base,solver,seconds,chunk=task
    t=time.monotonic()
    enc=Encoding(n,edges,total,k,base).build()
    meta={"top_count":k,"max_internal_or":enc.m,"variables":enc.max_var,
          "clauses":len(enc.cnf),"build_seconds":round(time.monotonic()-t,3)}
    r=v4.solve(enc,"full",base,solver,seconds,chunk)
    return {**meta,**r}


def self_test(solver,seconds,chunk):
    from pysat.solvers import Solver
    # Fixed symbolic models matching v4/v7 boundary witnesses.
    cases=[
        (3,[(0,1)],5,1,2,[(0,1),(5,3)],[(1,2),(1,6),(0,4)]),
        (6,[(0,1),(3,4),(3,5)],8,2,4,
         [(0,1),(8,6),(4,5)],[(1,2),(1,9),(0,7),(3,10)]),
    ]
    # In the first case q=5: OR0=0|1, OR1=junk0|OR0;
    # junk1=1&OR1, top=0&junk1.
    for n,edges,total,k,base,ors,ands in cases:
        for b,expected in ((base,True),(base+1,False)):
            enc=Encoding(n,edges,total,k,b).build()
            ass=enc.active[:]
            for pairs,choices in ((enc.ors,ors),(enc.ands,ands)):
                for pair,(a,c) in zip(pairs,choices):
                    for (sels,_),src in zip(pair,sorted((a,c))):ass.append(sels[src])
            with Solver(name=solver,bootstrap_with=enc.cnf) as s:
                assert s.solve(assumptions=ass)==expected,(n,b)
                if expected:
                    w=enc.decode(s.get_model())
                    assert v1.verify(n,enc.masks,w)
                    q=v4.check_star(n,enc.masks,w,b,True)
                    assert q["valid"] and q["h6_lhs"]==q["h6_rhs"],q
    for total,k,expected in ((3,1,"UNSAT"),(5,1,"SAT")):
        r=run((3,[(0,1)],total,k,0,solver,seconds,chunk))
        print("[TEST]",json.dumps(r),flush=True)
        assert r["status"]==expected,r
    print("SAT V9 SELF TEST OK",flush=True)


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--case",choices=v1.CASES,default="l2260")
    ap.add_argument("--gates",type=int,default=21)
    ap.add_argument("--top-count",type=int)
    ap.add_argument("--jobs",type=int,default=4)
    ap.add_argument("--seconds",type=float,default=30)
    ap.add_argument("--chunk",type=int,default=20000)
    ap.add_argument("--solver",default="g4")
    ap.add_argument("--checkpoint",type=Path)
    ap.add_argument("--self-test",action="store_true")
    a=ap.parse_args()
    if a.jobs<1 or a.seconds<=0 or a.chunk<1 or a.gates<3:ap.error("invalid limits")
    if a.self_test:self_test(a.solver,a.seconds,a.chunk);return
    n,edges=v1.CASES[a.case]
    base=17 if a.case=="l2260" else 0
    counts=list(range((a.gates-1)//2,0,-1))
    if a.top_count is not None:
        if a.top_count not in counts:ap.error("impossible top count")
        counts=[a.top_count]
    root=Path(__file__).resolve().parent
    h=hashlib.sha256(json.dumps([n,edges,a.gates,base,counts]).encode())
    for name in ("pnp_sat_solve_v1.py","pnp_sat_solve_v2.py","pnp_sat_solve_v4.py","pnp_sat_solve_v9.py"):
        h.update((root/name).read_bytes())
    key=h.hexdigest()
    path=a.checkpoint
    def execute():
        start=time.monotonic()
        data={"fingerprint":key,"results":{}}
        if path and path.exists():
            data=json.loads(path.read_text())
            if data["fingerprint"]!=key:raise ValueError("checkpoint mismatch")
        results=data["results"]
        def save():
            if path:
                tmp=path.with_name(path.name+".tmp")
                tmp.write_text(json.dumps(data,indent=2)+"\n")
                os.replace(tmp,path)
        pending=[k for k in counts if results.get(str(k),{}).get("status")!="UNSAT"]
        print("[CONFIG]",json.dumps({"top_counts":counts,"pending":pending,
              "jobs":a.jobs,"seconds":a.seconds,"solver":a.solver}),flush=True)
        if pending and not any(x.get("status")=="SAT" for x in results.values()):
            with cf.ProcessPoolExecutor(max_workers=a.jobs,mp_context=mp.get_context("fork")) as pool:
                todo=iter(pending)
                active={}
                def fill():
                    while len(active)<a.jobs:
                        k=next(todo,None)
                        if k is None:break
                        active[pool.submit(run,(n,edges,a.gates,k,base,a.solver,a.seconds,a.chunk))]=k
                fill()
                stop=False
                while active:
                    done,_=cf.wait(active,return_when=cf.FIRST_COMPLETED)
                    for f in done:
                        k=active.pop(f)
                        try:r=f.result()
                        except Exception as e:r={"status":"ERROR","error":repr(e)}
                        results[str(k)]=r
                        save()
                        print("[TOP CASE]",k,json.dumps(r),flush=True)
                        if r["status"] in ("SAT","ERROR","MODEL_INVALID"):stop=True
                    if not stop:fill()
        stats={}
        for k in counts:
            s=results.get(str(k),{}).get("status","PENDING")
            stats[s]=stats.get(s,0)+1
        status=("ERROR" if stats.get("ERROR") or stats.get("MODEL_INVALID") else
                "SAT" if stats.get("SAT") else "UNSAT" if stats.get("UNSAT")==len(counts) else "UNRESOLVED")
        print("[SUMMARY]",json.dumps({"status":status,"counts":stats,
                    "wall_seconds":round(time.monotonic()-start,3)}),flush=True)
        if status=="ERROR":raise SystemExit(1)
    if path:
        import fcntl
        path.parent.mkdir(parents=True,exist_ok=True)
        with open(str(path)+".lock","a") as lock:
            fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
            execute()
    else:execute()


if __name__=="__main__":main()
