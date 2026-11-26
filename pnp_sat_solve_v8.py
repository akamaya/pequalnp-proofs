#!/usr/bin/env python3
"""SAT v8: reduced TopForm search with private edges and semantic pruning.

For a minimum TopForm AO2 circuit computing a nonempty simple graph
edge function, all top ANDs reach the output through ORs only. All
clean ORs form the output network. With k top ANDs, that network can
be replaced by a chain of k-1 OR gates. The remaining gates can be
topologically reordered with all k top ANDs last.

Experimental reduction; the normalization lemma and CNF soundness
are not yet formally proved in Lean. UNSAT is not a Lean proof.
"""
import argparse
import concurrent.futures as cf
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
import pnp_sat_solve_v6 as v6


class Reduced(v2.Compact):
    def __init__(self,orig,k,total):
        super().__init__(orig,"dense")
        self.k=k
        self.total=total

    def decode(self,model):
        pos={self.reverse[x] for x in model if 0<x<len(self.reverse)}
        orig=self.original
        v,n,s=orig.v,orig.n,orig.s
        wires={i:i for i in range(n)}
        gates=[]
        tops=[]
        for j in range(s):
            if v(7,j,0) in pos:
                continue
            op=next(k for k in (0,1) if v(0,j,k) in pos)
            a,b=(next(k for k in range(n+j) if v(e,j,k) in pos)
                 for e in (1,2))
            wires[n+j]=n+len(gates)
            gates.append(("and" if op==0 else "or",wires[a],wires[b]))
            if j>=s-self.k:
                if op!=0:raise ValueError("top suffix is not AND")
                tops.append(wires[n+j])
        if len(tops)!=self.k:raise ValueError("incorrect top count")
        internal=len(gates)
        out=tops[0]
        for w in tops[1:]:
            gates.append(("or",out,w))
            out=n+len(gates)-1
        if len(gates)>self.total:raise ValueError("size bound violated")
        return {"gates":gates,"output":out,"internal_gates":internal,
                "output_or_gates":self.k-1,"top_count":self.k}


def add_private_edges(orig, k):
    """Each top must be the sole true top on at least one edge input.

    Otherwise removing that top from the output union preserves every
    positive row and all negative rows; by monotonicity it preserves
    the entire edge function. This contradicts minimum circuit size.
    """
    v,s=orig.v,orig.s
    positives=[r for r in orig.rows if v1.target(r,orig.masks)]
    high=max(abs(x) for c in orig.cnf for x in c)
    for j in range(s-k,s):
        hits=[]
        for r in positives:
            high+=1
            p=high
            hits.append(p)
            orig.add(-p,v(3,j,r))
            for i in range(s-k,s):
                if i!=j:orig.add(-p,-v(3,i,r))
        orig.add(*hits)


def add_semantic(orig):
    """For each real gate, operands must differ in both directions on
    the sampled rows. Otherwise that gate equals one of its operands
    on every sampled row and can be removed. Replacing the gate
    preserves the output on the boundary rows and thus on ALL inputs
    (monotone circuit + minimal true / maximal false rows).
    """
    v,s=orig.v,orig.s
    high=max(abs(x) for c in orig.cnf for x in c)
    for j in range(s):
        for e in (4,5):
            hits=[]
            for r in orig.rows:
                high+=1
                p=high
                hits.append(p)
                orig.add(-p,v(e,j,r))
                orig.add(-p,-v(9-e,j,r))
            orig.add(v(7,j,0),*hits)


def check_semantic(n,masks,w,mode):
    if mode=="none":return True
    rows=v1.rows_for(n,masks)
    vals=[sum(1<<i for i,r in enumerate(rows) if r&(1<<a))
          for a in range(n)]
    top_vals=[]
    for j,(op,a,b) in enumerate(w["gates"]):
        A,B=vals[a],vals[b]
        if mode=="semantic" and j<w["internal_gates"]:
            if not(A&~B) or not(B&~A):return False
        z=A&B if op=="and" else A|B
        vals.append(z)
        if w["internal_gates"]-w["top_count"]<=j<w["internal_gates"]:
            top_vals.append(z)
    for i,x in enumerate(top_vals):
        rest=0
        for j,y in enumerate(top_vals):
            if i!=j:rest|=y
        if not(x&~rest):return False
    return True


def build(n,edges,total,k,base=17,prune="none",mode="none"):
    masks=v1.graph(n,edges)
    if not masks:raise ValueError("nonempty simple graph required")
    # A minimum circuit has k top ANDs, two dirty ANDs, k-1 clean ORs.
    s=total-k+1
    if k<1 or s<k+2:raise ValueError("impossible top count")
    orig=v1.Encoding(n,s,masks,v1.rows_for(n,masks),False).build()
    v=orig.v
    # Remove the original single-output clauses and original fUsed.
    # Their replacements allow the k top ANDs to be terminal wires.
    outvars={v(6,0,i) for i in range(n+s+1)}
    used={tuple([v(1,h,n+j) for h in range(j+1,s)]
                +[v(2,h,n+j) for h in range(j+1,s)]+[v(7,j,0)])
          for j in range(s-1)}
    orig.cnf=[c for c in orig.cnf if tuple(c) not in used
              and not any(abs(x) in outvars for x in c)]
    v2.add_onehot(orig)
    orig.cnf=[c for c in orig.cnf if not any(abs(x) in outvars for x in c)]
    high=max(abs(x) for c in orig.cnf for x in c)
    v2.add_topform(orig)
    dirty=list(range(high+1,high+s+1))
    top=list(range(high+s+1,high+2*s+1))
    negatives=[r for r in orig.rows if not v1.target(r,masks)]
    positives=[r for r in orig.rows if v1.target(r,masks)]
    # Verify the allocation contract with the existing v2 encoder.
    clauses={tuple(c) for c in orig.cnf}
    for j,(d,t) in enumerate(zip(dirty,top)):
        a=v(0,j,0)
        assert (-t,a) in clauses and (-t,-d) in clauses and (-a,d,t) in clauses
        assert (-d,a) in clauses
    del clauses
    first=s-k
    for j in range(s):
        orig.add(top[j] if j>=first else -top[j])
        # Every retained OR must be dirty. Padding uses op 2, not OR.
        orig.add(-v(0,j,1),*(v(3,j,r) for r in negatives))
        # Retained non-top, non-padding gates must have a reader.
        if j<first:
            orig.add(v(7,j,0),*(v(e,h,n+j) for e in (1,2)
                                  for h in range(j+1,s)))
        # No gate may read a top; their only readers are in the
        # clean output OR network reconstructed after SAT.
        for i in range(first,j):
            for e in (1,2):orig.add(-v(e,j,n+i))
    # All top ANDs are known to be clean. Their OR must cover every edge.
    for r in positives:
        orig.add(*(v(3,j,r) for j in range(first,s)))
    # Independent terminal tops may be sorted by the first input.
    # No need to constrain ties or pay the full enc2 lex cost.
    for j in range(first,s-1):
        for a in range(n+first):
            for b in range(a):
                orig.add(-v(1,j,a),-v(1,j+1,b))
    # v4's size inequality counts retained gates. Credit the k-1 ORs
    # that are not encoded. Everything else (Ustar, lam, cones) is
    # unchanged when terminal clean ORs are added.
    v4.add_star(orig,base-(k-1),True)
    if prune!="none":
        v6.add_minimality(orig,prune)
        # v6's essential-input clause permits a direct output wire.
        # Here the output is an OR of top ANDs, never an input.
        for a in range(n):orig.add(-v(6,0,a))
    if mode!="none":add_private_edges(orig,k)
    if mode=="semantic":add_semantic(orig)
    return Reduced(orig,k,total)


def run_case(task):
    n,edges,total,k,base,prune,solver,seconds,chunk,mode=task
    start=time.monotonic()
    enc=build(n,edges,total,k,base,prune,mode)
    meta={"mode":mode,"top_count":k,"internal_slots":enc.original.s,
          "output_or_gates":k-1,"clauses":len(enc.cnf),
          "variables":enc.max_var,"build_seconds":round(time.monotonic()-start,3)}
    result=v4.solve(enc,"full",base,solver,seconds,chunk)
    if result["status"]=="SAT" and not check_semantic(n,enc.masks,result["witness"],mode):
        result.update(status="MODEL_INVALID",error="semantic pruning check failed")
    return {**meta,**result}


def fingerprint(n,edges,total,base,prune,mode):
    # Include all source files that define the formula or decoding.
    root=Path(__file__).resolve().parent
    h=hashlib.sha256(json.dumps([n,edges,total,base,prune,mode]).encode())
    for name in ("pnp_sat_solve_v1.py","pnp_sat_solve_v2.py",
                 "pnp_sat_solve_v4.py","pnp_sat_solve_v6.py",
                 "pnp_sat_solve_v8.py"):
        h.update((root/name).read_bytes())
    return h.hexdigest()


def execute(n,edges,total,base,prune,solver,seconds,chunk,jobs,path=None,mode="semantic",seed=None):
    # k>=1 and k+2+(k-1)<=total.
    counts=list(range(1,(total-1)//2+1))
    key=fingerprint(n,edges,total,base,prune,mode)
    data={"fingerprint":key,"top_counts":counts,"results":{}}
    if path is not None and path.exists():
        old=json.loads(path.read_text())
        if old.get("fingerprint")!=key or old.get("top_counts")!=counts:
            raise ValueError("checkpoint mismatch; choose a new path")
        data=old
    results=data["results"]
    if seed is not None:
        # Only accept v7 results if the exact v7 fingerprint matches
        # the corresponding unpruned formula. Adding necessary clauses
        # cannot make an UNSAT formula satisfiable.
        import pnp_sat_solve_v7 as oldv
        old=json.loads(seed.read_text())
        if old.get("fingerprint")!=oldv.fingerprint(n,edges,total,base,prune) or old.get("top_counts")!=counts:
            raise ValueError("v7 seed checkpoint mismatch")
        for k in counts:
            prev=old.get("results",{}).get(str(k),{})
            if prev.get("status")=="UNSAT" and results.get(str(k),{}).get("status")!="UNSAT":
                results[str(k)]={**prev,"inherited_from_v7":True}
    def save():
        if path is None:return
        temp=path.with_name(path.name+".tmp")
        temp.write_text(json.dumps(data,indent=2)+"\n")
        os.replace(temp,path)
    start=time.monotonic()
    pending=[k for k in reversed(counts) if results.get(str(k),{}).get("status")!="UNSAT"]
    print("[REDUCED CONFIG]",json.dumps({"gates":total,"top_counts":counts,
          "pending":pending,"jobs":jobs,"solver":solver,"seconds_per_case":seconds,
          "prune":prune,"mode":mode,"seed":str(seed) if seed else None}),flush=True)
    save()
    if not any(r.get("status")=="SAT" for r in results.values()) and pending:
        with cf.ProcessPoolExecutor(max_workers=jobs,mp_context=mp.get_context("fork")) as pool:
            todo=iter(pending)
            active={}
            stop=False
            def fill():
                while len(active)<jobs:
                    k=next(todo,None)
                    if k is None:break
                    task=(n,edges,total,k,base,prune,solver,seconds,chunk,mode)
                    active[pool.submit(run_case,task)]=k
            fill()
            while active:
                done,_=cf.wait(active,return_when=cf.FIRST_COMPLETED)
                for future in done:
                    k=active.pop(future)
                    try:r=future.result()
                    except Exception as e:r={"status":"ERROR","error":repr(e)}
                    results[str(k)]=r
                    save()
                    print("[TOP CASE]",k,json.dumps(r),flush=True)
                    if r["status"] in ("SAT","ERROR","MODEL_INVALID"):stop=True
                if not stop:fill()
    stats={}
    for k in counts:
        status=results.get(str(k),{}).get("status","PENDING")
        stats[status]=stats.get(status,0)+1
    if not counts:status="UNSAT"
    elif stats.get("ERROR") or stats.get("MODEL_INVALID"):status="ERROR"
    elif stats.get("SAT"):status="SAT"
    elif stats.get("UNSAT")==len(counts):status="UNSAT"
    else:status="UNRESOLVED"
    out={"status":status,"counts":stats,"wall_seconds":round(time.monotonic()-start,3)}
    print("[SUMMARY]",json.dumps(out),flush=True)
    return out


def self_test(solver,seconds,chunk):
    from pysat.solvers import Solver
    # Forced models exercise the h6 adjustment and reconstructed OR.
    cases=[
        (3,[(0,1)],5,1,2,
         [("or",0,1),("and",1,2),("or",3,4),("and",1,5),("and",0,6)]),
        (6,[(0,1),(3,4),(3,5)],8,2,4,
         [("or",0,1),("and",1,2),("or",6,7),("and",1,8),
          ("or",4,5),("and",0,9),("and",3,10)]),
    ]
    for n,edges,total,k,base,gates in cases:
        for b,expected in ((base,True),(base+1,False)):
            enc=build(n,edges,total,k,b)
            orig=enc.original
            fwd={v:i for i,v in enumerate(enc.reverse) if i}
            assumptions=[]
            for j,(op,a,c) in enumerate(gates):
                assumptions.extend(fwd[orig.v(kind,j,z)] for kind,z in
                                   ((0,0 if op=="and" else 1),(1,min(a,c)),(2,max(a,c))))
            with Solver(name=solver,bootstrap_with=enc.cnf) as sol:
                assert sol.solve(assumptions=assumptions)==expected,(k,b)
                if expected:
                    w=enc.decode(sol.get_model())
                    assert len(w["gates"])==total
                    assert v1.verify(n,enc.masks,w)
                    check=v4.check_star(n,enc.masks,w,b,True)
                    assert check["valid"] and len(check["top_gates"])==k,check
                    assert check["h6_lhs"]==check["h6_rhs"],check
    for total,k,expected in ((3,1,"UNSAT"),(5,1,"SAT")):
        r=run_case((3,[(0,1)],total,k,0,"none",solver,seconds,chunk,"none"))
        print("[TEST]",json.dumps(r),flush=True)
        assert r["status"]==expected,r
    # Minimal known circuits must survive semantic pruning, even with
    # padding at a bound larger than their minimum.
    for case,minimum in (("edge",1),("path3",2),("triangle",4)):
        n,edges=v1.CASES[case]
        masks=v1.graph(n,edges)
        for s in (minimum-1,minimum,minimum+1):
            orig=v1.Encoding(n,s,masks,v1.rows_for(n,masks),False).build()
            v2.add_onehot(orig)
            add_semantic(orig)
            enc=v2.Compact(orig,"dense")
            with Solver(name=solver,bootstrap_with=enc.cnf) as sol:
                assert sol.solve()==(s>=minimum),(case,s)
                if s>=minimum:
                    assert v1.verify(n,masks,enc.decode(sol.get_model()))
    # Check private-edge encoding with synthetic, fixed top truth values:
    # two disjoint edges assigned to different tops are necessary and
    # sufficient here; equal top truth values cannot pass.
    masks=v1.graph(4,[(0,1),(2,3)])
    for overlap in (False,True):
        orig=v1.Encoding(4,2,masks,v1.rows_for(4,masks),False)
        for j in range(2):
            for r in masks:
                val=(r==masks[j]) or overlap
                orig.add(orig.v(3,j,r) if val else -orig.v(3,j,r))
        add_private_edges(orig,2)
        enc=v2.Compact(orig,"dense")
        with Solver(name=solver,bootstrap_with=enc.cnf) as sol:
            assert sol.solve()==(not overlap)
    # Force a redundant circuit (x0 & x1) & x0: must be excluded.
    masks=v1.graph(2,[(0,1)])
    orig=v1.Encoding(2,2,masks,v1.rows_for(2,masks),False).build()
    v2.add_onehot(orig)
    add_semantic(orig)
    enc=v2.Compact(orig,"dense")
    fwd={v:i for i,v in enumerate(enc.reverse) if i}
    ass=[orig.v(0,0,0),orig.v(1,0,0),orig.v(2,0,1),
         orig.v(0,1,0),orig.v(1,1,0),orig.v(2,1,2),orig.v(6,0,3)]
    with Solver(name=solver,bootstrap_with=enc.cnf) as sol:
        assert not sol.solve(assumptions=[fwd[x] for x in ass])
    print("SAT V8 SELF TEST OK",flush=True)


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--case",choices=v1.CASES,default="l2260")
    ap.add_argument("--gates",type=int,default=21)
    ap.add_argument("--top-count",type=int)
    ap.add_argument("--jobs",type=int,default=4)
    ap.add_argument("--seconds",type=float,default=20)
    ap.add_argument("--chunk",type=int,default=20000)
    ap.add_argument("--solver",default="g4")
    ap.add_argument("--prune",choices=("none","absorb","absorb-dup"),default="none")
    ap.add_argument("--checkpoint",type=Path)
    ap.add_argument("--mode",choices=("none","private","semantic"),default="semantic")
    ap.add_argument("--seed-v7",type=Path,help="inherit verified formula-matched UNSAT statuses")
    ap.add_argument("--self-test",action="store_true")
    a=ap.parse_args()
    if a.gates<3 or a.jobs<1 or a.seconds<=0 or a.chunk<1:ap.error("invalid limits")
    if a.self_test:self_test(a.solver,a.seconds,a.chunk);return
    n,edges=v1.CASES[a.case]
    base=17 if a.case=="l2260" else 0
    if a.top_count is not None:
        if a.checkpoint or a.seed_v7:ap.error("checkpoint/seed is for all top-count cases")
        r=run_case((n,edges,a.gates,a.top_count,base,a.prune,a.solver,a.seconds,a.chunk,a.mode))
        print("[TOP CASE]",json.dumps(r),flush=True)
    elif a.checkpoint:
        a.checkpoint.parent.mkdir(parents=True,exist_ok=True)
        with open(str(a.checkpoint)+".lock","a") as lock:
            fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
            r=execute(n,edges,a.gates,base,a.prune,a.solver,a.seconds,a.chunk,a.jobs,a.checkpoint,a.mode,a.seed_v7)
    else:
        r=execute(n,edges,a.gates,base,a.prune,a.solver,a.seconds,a.chunk,a.jobs,mode=a.mode,seed=a.seed_v7)
    if r["status"] in ("ERROR","MODEL_INVALID"):raise SystemExit(1)


if __name__=="__main__":
    main()
