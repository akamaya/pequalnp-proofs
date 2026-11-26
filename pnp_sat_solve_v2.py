#!/usr/bin/env python3
"""SAT v2: dense IDs, exactly-one selectors, optional TopForm/junk restrictions.

The dense profile is a variable renaming of v1. The onehot and topform
profiles add constraints, so their UNSAT results are not official enc2
certificates. No Lean verification or submission is performed.
"""
import argparse
import itertools
import json
import time
from pathlib import Path
import pnp_sat_solve_v1 as v1


def add_onehot(enc):
    n,s,v=enc.n,enc.s,enc.v
    groups=[]
    for j in range(s):
        groups.append([v(0,j,k) for k in range(3)])
        for e in (1,2):
            groups.append([v(e,j,k) for k in range(n+j+1)])
    groups.append([v(6,0,k) for k in range(n+s+1)])
    # At least one is already present in the original formula.
    for group in groups:
        for a,b in itertools.combinations(group,2):
            enc.add(-a,-b)


def add_topform(enc):
    """Exactly two dirty ANDs, one in the other's strict cone, and TopForm.

    The graph's maximal false rows suffice to classify a monotone gate
    as dirty. This is a relaxation of L-meta-2260's remaining hypotheses.
    """
    n,s,v=enc.n,enc.s,enc.v
    negatives=[r for r in enc.rows if not v1.target(r,enc.masks)]
    next_id=max(abs(x) for c in enc.cnf for x in c)
    def fresh():
        nonlocal next_id
        next_id+=1
        return next_id
    def eq_or(z, xs):
        for x in xs:
            enc.add(-x,z)
        enc.add(-z,*xs)
    dirty=[fresh() for _ in range(s)]
    top=[fresh() for _ in range(s)]
    dirty_anc=[fresh() for _ in range(s)]
    top_anc=[fresh() for _ in range(s)]
    hits=[]
    for j in range(s):
        a=v(0,j,0)
        d,t=dirty[j],top[j]
        vals=[v(3,j,r) for r in negatives]
        # d <-> AND and at least one false graph row evaluates true.
        enc.add(-d,a)
        enc.add(-d,*vals)
        for z in vals:
            enc.add(-a,-z,d)
        # t <-> AND and not dirty.
        enc.add(-t,a)
        enc.add(-t,-d)
        enc.add(-a,d,t)
        for labels,anc in ((dirty,dirty_anc),(top,top_anc)):
            sides=[]
            for e in (1,2):
                side=fresh()
                sides.append(side)
                for k in range(n+j+1):
                    sel=v(e,j,k)
                    if n<=k<n+j:
                        i=k-n
                        # selected source carries its own label or a strict ancestor.
                        enc.add(-sel,-labels[i],side)
                        enc.add(-sel,-anc[i],side)
                        enc.add(-sel,-side,labels[i],anc[i])
                    else:
                        enc.add(-sel,-side)
            eq_or(anc[j],sides)
        # A top AND must not occur strictly below any AND.
        enc.add(-a,-top_anc[j])
        hit=fresh()
        hits.append(hit)
        enc.add(-hit,d)
        enc.add(-hit,dirty_anc[j])
        enc.add(-d,-dirty_anc[j],hit)
    if s<2:
        enc.add()  # impossible to have two distinct dirty gates
    else:
        # At least two, and at most two.
        for j in range(s):
            enc.add(*(d for i,d in enumerate(dirty) if i!=j))
        for a,b,c in itertools.combinations(dirty,3):
            enc.add(-a,-b,-c)
    enc.add(*hits)


def verify_topform(n,masks,witness):
    """Independently recompute dirty ANDs and strict cones from decoded circuit."""
    full=(1<<(1<<n))-1
    values=[sum(1<<r for r in range(1<<n) if r&(1<<i)) for i in range(n)]
    false_rows=sum(1<<r for r in range(1<<n) if not v1.target(r,masks))
    cones=[set() for _ in range(n)]
    dirty=set()
    tops=set()
    for j,(op,a,b) in enumerate(witness["gates"]):
        if not (0<=a<n+j and 0<=b<n+j):
            raise ValueError("not a backwards-reading circuit")
        z=values[a]&values[b] if op=="and" else values[a]|values[b]
        values.append(z&full)
        cone=cones[a]|cones[b]|({a-n} if a>=n else set())|({b-n} if b>=n else set())
        cones.append(cone)
        if op=="and":
            if z&false_rows:
                dirty.add(j)
            else:
                tops.add(j)
    bad=any(op=="and" and cones[n+j]&tops
            for j,(op,a,b) in enumerate(witness["gates"]))
    linked=any(i in cones[n+j] for i in dirty for j in dirty if i!=j)
    return {"dirty_gates":sorted(dirty),"top_gates":sorted(tops),
            "topform":not bad,"dirty_cone_link":linked,
            "valid":len(dirty)==2 and not bad and linked}


class Compact:
    def __init__(self,enc,profile):
        self.original=enc
        self.n,self.masks=enc.n,enc.masks
        self.profile=profile
        active=sorted({abs(x) for c in enc.cnf for x in c})
        self.reverse=[0]+active
        forward={x:i+1 for i,x in enumerate(active)}
        self.cnf=[[forward[x] if x>0 else -forward[-x] for x in c] for c in enc.cnf]
        self.old_max=active[-1]
        self.max_var=len(active)
    def decode(self,model):
        old=[self.reverse[x] if x>0 else -self.reverse[-x]
             for x in model if 0<abs(x)<len(self.reverse)]
        w=self.original.decode(old)
        if self.profile=="topform":
            check=verify_topform(self.n,self.masks,w)
            if not check["valid"]:
                raise ValueError("decoded model violates structural constraints: "+str(check))
            w["structure_check"]=check
        return w


def run(n,edges,s,profile,solver,seconds,full=False,lex=True):
    masks=v1.graph(n,edges)
    if not masks:
        raise ValueError("empty graph is unsupported")
    rows=v1.rows_for(n,masks,full)
    t=time.monotonic()
    orig=v1.Encoding(n,s,masks,rows,lex).build()
    base_clauses=len(orig.cnf)
    if profile in ("onehot","topform"):
        add_onehot(orig)
    if profile=="topform":
        add_topform(orig)
    enc=Compact(orig,profile)
    meta={"profile":profile,"encoding":"enc2" if lex else "enc",
          "n":n,"edges":len(masks),"gate_bound":s,"rows":len(rows),
          "base_clauses":base_clauses,"clauses":len(enc.cnf),
          "old_max_var":enc.old_max,"active_variables":enc.max_var,
          "build_seconds":round(time.monotonic()-t,3)}
    print("[CNF]",json.dumps(meta),flush=True)
    r=v1.solve(enc,solver,seconds)
    print("[RESULT]",json.dumps(r),flush=True)
    return {**meta,**r}


def self_test(solver,seconds):
    for name,minimum in (("edge",1),("path3",2),("triangle",4)):
        n,edges=v1.CASES[name]
        for profile in ("dense","onehot"):
            for lex in (False,True):
                for k,expected in ((minimum-1,"UNSAT"),(minimum,"SAT")):
                    r=run(n,edges,k,profile,solver,seconds,lex=lex)
                    if r["status"]!=expected:
                        raise SystemExit("SELF TEST FAILED: "+str(r))
    # Known non-minimal circuit for x0 AND x1, with two linked dirty ANDs.
    # Gates: (x0 AND x2), (x0 AND g0), (x1 AND g1), (x0 AND x1),
    # then OR of the last two. Both top ANDs have no AND readers.
    w={"gates":[("and",0,2),("and",0,3),("and",1,4),("and",0,1),
                ("or",5,6)],"output":7}
    masks=v1.graph(3,[(0,1)])
    assert v1.verify(3,masks,w)
    assert verify_topform(3,masks,w)["valid"]
    for s,expected in ((1,"UNSAT"),(5,"SAT")):
        r=run(3,[(0,1)],s,"topform",solver,seconds,lex=False)
        if r["status"]!=expected:
            raise SystemExit("STRUCTURE SELF TEST FAILED: "+str(r))
    print("SAT V2 SELF TEST OK",flush=True)


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--case",choices=v1.CASES,default="l2260")
    ap.add_argument("--graph-json",type=Path)
    ap.add_argument("--gates",type=int,default=21)
    ap.add_argument("--seconds",type=float,default=30,help="per run")
    ap.add_argument("--solver",default="g4")
    ap.add_argument("--profile",choices=("dense","onehot","topform"),default="dense")
    ap.add_argument("--compare",action="store_true",help="six runs: 3 profiles x enc/enc2")
    ap.add_argument("--no-lex",action="store_true")
    ap.add_argument("--full-rows",action="store_true")
    ap.add_argument("--self-test",action="store_true")
    ap.add_argument("--json-out",type=Path)
    a=ap.parse_args()
    if a.gates<0 or a.seconds<=0:
        ap.error("invalid bound or time")
    if a.self_test:
        self_test(a.solver,a.seconds)
        return
    n,edges=v1.CASES[a.case]
    if a.graph_json:
        d=json.loads(a.graph_json.read_text())
        n,edges=d["n"],d["edges"]
    cases=list(itertools.product(("dense","onehot","topform"),(True,False))) if a.compare else [(a.profile,not a.no_lex)]
    results=[]
    for profile,lex in cases:
        r=run(n,edges,a.gates,profile,a.solver,a.seconds,a.full_rows,lex)
        results.append(r)
        if r["status"] in ("ERROR","MODEL_INVALID"):
            raise SystemExit(1)
    if a.json_out:
        a.json_out.write_text(json.dumps(results,indent=2)+"\n")
    print("[SUMMARY]",json.dumps([{k:r.get(k) for k in ("profile","encoding","clauses","active_variables","status","wall_seconds")} for r in results]),flush=True)


if __name__=="__main__":
    main()
