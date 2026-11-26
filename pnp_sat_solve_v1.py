#!/usr/bin/env python3
"""Experimental SAT search for monotone graph edge functions.

Mirrors PEqualNP.Defs.LratEncoding.enc / enc2, at source commit
0de59327773efd273802742186878101f478184b.
SAT models are independently evaluated on every input. UNSAT is a solver
result only, NOT a Lean proof. No submission or changes to the proof repo.
"""
import argparse
import itertools
import json
import multiprocessing as mp
import time
from pathlib import Path

L2260 = (11, [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
              (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)])
CASES = {"edge": (2, [(0,1)]), "path3": (3, [(0,1),(1,2)]),
         "triangle": (3, [(0,1),(0,2),(1,2)]),
         "l2260": L2260}

def graph(n, edges):
    if not 1 <= n <= 16:
        raise ValueError("n must be 1..16")
    es = sorted(set(tuple(sorted(e)) for e in edges))
    if any(len(e)!=2 or not 0<=e[0]<e[1]<n for e in es):
        raise ValueError("invalid edge")
    return tuple((1<<a)|(1<<b) for a,b in es)

def target(r, masks):
    return any(r&m == m for m in masks)

def rows_for(n, masks, full=False):
    if full:
        return list(range(1<<n))
    independent = [r for r in range(1<<n) if not target(r,masks)]
    maximal = [r for r in independent if all(
        r&(1<<i) or target(r|(1<<i),masks) for i in range(n))]
    return sorted(set(masks)|set(maximal))

class Encoding:
    def __init__(self,n,s,masks,rows,lex=True):
        self.n,self.s,self.masks,self.rows = n,s,masks,rows
        self.wd=(1<<n)+n+s+1
        self.cnf=[]
        self.lex=lex

    def v(self,k,j,a):
        # Lean P(ix) = 2*ix+2; DIMACS positive variable is ix+1.
        return (k*(self.s+1)+j)*self.wd+a+1

    def add(self,*lits):
        self.cnf.append(list(lits))

    def build(self):
        n,s,rs,v,add=self.n,self.s,self.rows,self.v,self.add
        # Keep clause ordering exactly as in the Lean definitions.
        for j in range(s):
            add(v(0,j,0),v(0,j,1),v(0,j,2))
        for e in (1,2):
            for j in range(s):
                add(*(v(e,j,k) for k in range(n+j+1)))
        for e in (1,2):
            for j in range(s):
                for r in rs:
                    z=v(e+3,j,r)
                    for k in range(n+j+1):
                        a=v(e,j,k)
                        if k<n:
                            add(-a,z if r&(1<<k) else -z)
                        elif k<n+j:
                            w=v(3,k-n,r)
                            add(-a,-z,w)
                            add(-a,z,-w)
                        else:
                            add(-a,-z)
        for j in range(s):
            for r in rs:
                a,o,t=(v(0,j,k) for k in range(3))
                z,x,y=(v(k,j,r) for k in (3,4,5))
                add(-a,-z,x)
                add(-a,-z,y)
                add(-a,z,-x,-y)
                add(-o,z,-x)
                add(-o,z,-y)
                add(-o,-z,x,y)
                add(-t,z)
        add(*(v(6,0,k) for k in range(n+s+1)))
        for r in rs:
            g=target(r,self.masks)
            for k in range(n+s+1):
                a=v(6,0,k)
                if k<n:
                    if bool(r&(1<<k))!=g:
                        add(-a)
                elif k<n+s:
                    z=v(3,k-n,r)
                    add(-a,z if g else -z)
                elif g:
                    add(-a)
        if s:
            add(v(6,0,n+s-1),v(7,s-1,0))
        for j in range(s):
            p=v(7,j,0)
            a,x,y=v(0,j,2),v(1,j,n+j),v(2,j,n+j)
            add(-p,a);add(-p,x);add(-p,y)
            add(p,-a);add(p,-x);add(p,-y)
        for j in range(s-1):
            add(-v(7,j+1,0),v(7,j,0))
        for j in range(s):
            for i in range(j):
                add(-v(7,i,0),-v(1,j,n+i))
                add(-v(7,i,0),-v(2,j,n+i))
        for j in range(s):
            for k in range(n+j+1):
                for l in range(k+1):
                    add(-v(1,j,k),-v(2,j,l),v(7,j,0))
        for j in range(s-1):
            add(*( [v(1,k,n+j) for k in range(j+1,s)]
                  +[v(2,k,n+j) for k in range(j+1,s)]+[v(7,j,0)] ))
        if self.lex:
            for j in range(s-1):
                base=[v(7,j,0),v(1,j+1,n+j),v(2,j+1,n+j)]
                for a in range(n+j+1):
                    for b in range(a):
                        add(-v(1,j,a),-v(1,j+1,b),*base)
                    for c in range(n+j+1):
                        prefix=[-v(1,j,a),-v(1,j+1,a),-v(2,j,c)]
                        for d in range(c):
                            add(*prefix,-v(2,j+1,d),*base)
                        add(*prefix,-v(2,j+1,c),-v(0,j,1),*base)
                        add(*prefix,-v(2,j+1,c),-v(0,j+1,0),*base)
        return self

    def dimacs(self,path):
        with open(path,"w",encoding="ascii") as f:
            f.write(f"p cnf {max(abs(x) for c in self.cnf for x in c)} {len(self.cnf)}\n")
            for c in self.cnf:
                f.write(" ".join(map(str,c))+" 0\n")

    def decode(self, model):
        # The official encoding uses at-least-one, not exactly-one.
        # Any selected source / operation gives the required row values.
        pos={x for x in model if x>0}
        v,n,s=self.v,self.n,self.s
        wires={i:i for i in range(n)}
        gates=[]
        for j in range(s):
            if v(7,j,0) in pos:
                continue
            op=next(k for k in (0,1) if v(0,j,k) in pos)
            a,b=(next(k for k in range(n+j) if v(e,j,k) in pos)
                 for e in (1,2))
            wires[n+j]=n+len(gates)
            gates.append(("and" if op==0 else "or",wires[a],wires[b]))
        out=next(k for k in range(n+s+1) if v(6,0,k) in pos)
        # A constant false output or a selected padding wire can occur only
        # for a constant target; handle separately, don't call it an AO2 witness.
        if out not in wires:
            raise ValueError("selected output is not an input/non-padding wire")
        return {"gates":gates,"output":wires[out]}

def verify(n,masks,witness):
    gates,out=witness["gates"],witness["output"]
    for r in range(1<<n):
        w=[bool(r&(1<<i)) for i in range(n)]
        for op,a,b in gates:
            if not(0<=a<len(w) and 0<=b<len(w)) or op not in ("and","or"):
                return False
            w.append(w[a] and w[b] if op=="and" else w[a] or w[b])
        if not 0<=out<len(w) or w[out]!=target(r,masks):
            return False
    return True

def worker(enc,solver_name,conn):
    try:
        from pysat.solvers import Solver
        t=time.monotonic()
        with Solver(name=solver_name,bootstrap_with=enc.cnf) as solver:
            ans=solver.solve()
            result={"status":"SAT" if ans else "UNSAT" if ans is False else "UNKNOWN",
                    "solve_seconds":round(time.monotonic()-t,3),
                    "stats":solver.accum_stats()}
            if ans:
                try:
                    w=enc.decode(solver.get_model())
                    result["witness"]=w
                    result["verified_full_truth_table"]=verify(enc.n,enc.masks,w)
                    if not result["verified_full_truth_table"]:
                        result["status"]="MODEL_INVALID"
                except Exception as e:
                    result.update(status="MODEL_INVALID",error=str(e))
            conn.send(result)
    except Exception as e:
        conn.send({"status":"ERROR","error":repr(e)})
    finally:
        conn.close()

def solve(enc,name,seconds):
    # Use a separate CPU process so wall-clock termination works even if
    # a particular SAT backend cannot be interrupted inside its native solver.
    ctx=mp.get_context("fork")
    recv,send=ctx.Pipe(duplex=False)
    proc=ctx.Process(target=worker,args=(enc,name,send),daemon=True)
    t=time.monotonic()
    proc.start()
    send.close()
    try:
        if recv.poll(seconds):
            try:
                result=recv.recv()
            except EOFError:
                result={"status":"ERROR","error":"worker exited without result"}
        else:
            result={"status":"TIMEOUT"}
    finally:
        recv.close()
        proc.join(0.2)
        if proc.is_alive():
            proc.terminate()
            proc.join(1)
        if proc.is_alive():
            proc.kill()
            proc.join()
    result["wall_seconds"]=round(time.monotonic()-t,3)
    return result

def run_case(n,edges,s,solver,seconds,full=False,lex=True,dimacs=None):
    masks=graph(n,edges)
    if not masks:
        raise ValueError("empty graph/constant output is not supported by this prototype")
    rows=rows_for(n,masks,full)
    t=time.monotonic()
    enc=Encoding(n,s,masks,rows,lex).build()
    meta={"n":n,"edges":len(masks),"gate_bound":s,"rows":len(rows),
          "positive_rows":sum(target(r,masks) for r in rows),
          "negative_rows":sum(not target(r,masks) for r in rows),
          "encoding":"enc2" if lex else "enc",
          "clauses":len(enc.cnf),"max_var":max(abs(x) for c in enc.cnf for x in c),
          "build_seconds":round(time.monotonic()-t,3)}
    print("[CNF]",json.dumps(meta),flush=True)
    if dimacs:
        enc.dimacs(dimacs)
    result=solve(enc,solver,seconds)
    print("[RESULT]",json.dumps(result),flush=True)
    return {**meta,**result}

def self_test(name,seconds):
    # Check every full row is covered by a positive minimal or negative maximal row.
    for n,edges in CASES.values():
        masks=graph(n,edges)
        rows=rows_for(n,masks)
        for r in range(1<<n):
            assert any(target(q,masks) and q&r==q for q in rows)==target(r,masks)
            assert any(not target(q,masks) and q&r==r for q in rows)==(not target(r,masks))
    # Known exact minima: edge 1; path3 2; triangle 4
    # (triangle has the 4-gate implementation (a|b)&c | (a&b)).
    for case,min_gates in (("edge",1),("path3",2),("triangle",4)):
        n,edges=CASES[case]
        for full in (False,True):
            for lex in (False,True):
                for s,expected in ((min_gates-1,"UNSAT"),(min_gates,"SAT"),(min_gates+1,"SAT")):
                    r=run_case(n,edges,s,name,seconds,full,lex)
                    if r["status"]!=expected:
                        raise SystemExit(f"SELF TEST FAILED: {case} {s} expected {expected}: {r}")
    print("SAT SELF TEST OK",flush=True)

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--case",choices=CASES,default="l2260")
    ap.add_argument("--graph-json",type=Path,help='JSON object {"n":11,"edges":[[0,9],...]}')
    ap.add_argument("--gates",type=int,default=21)
    ap.add_argument("--solver",default="g4",help="PySAT backend; g4=Glucose4, cadical195=CaDiCaL")
    ap.add_argument("--seconds",type=float,default=30)
    ap.add_argument("--full-rows",action="store_true")
    ap.add_argument("--no-lex",action="store_true",help="use official enc instead of enc2")
    ap.add_argument("--dimacs",type=Path)
    ap.add_argument("--json-out",type=Path)
    ap.add_argument("--self-test",action="store_true")
    args=ap.parse_args()
    if args.gates<0 or args.seconds<=0:
        ap.error("gates must be nonnegative and seconds positive")
    if args.self_test:
        self_test(args.solver,args.seconds)
        return
    n,edges=CASES[args.case]
    if args.graph_json:
        obj=json.loads(args.graph_json.read_text())
        n,edges=obj["n"],obj["edges"]
    r=run_case(n,edges,args.gates,args.solver,args.seconds,args.full_rows,not args.no_lex,args.dimacs)
    if args.json_out:
        args.json_out.write_text(json.dumps(r,indent=2)+"\n")
    if r["status"] in ("ERROR","MODEL_INVALID"):
        raise SystemExit(1)

if __name__=="__main__":
    main()
