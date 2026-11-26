#!/usr/bin/env python3
"""SAT v3: graph-specific structural relaxation, measurable limited search.

Adds L-meta-2260 h4, h5, h7 and the weaker h6 with orN\\lam omitted.
All constraints are experimental. UNSAT is NOT a Lean proof.
"""
import argparse
import itertools
import json
import multiprocessing as mp
import time
from pathlib import Path
import pnp_sat_solve_v1 as v1
import pnp_sat_solve_v2 as v2


def add_star(enc,base=17):
    from pysat.card import CardEnc, EncType
    n,s,v=enc.n,enc.s,enc.v
    edges=[tuple(i for i in range(n) if r&(1<<i)) for r in enc.masks]
    eset=set(edges)
    negatives=[r for r in enc.rows if not v1.target(r,enc.masks)]
    high=max(abs(x) for c in enc.cnf for x in c)
    def fresh():
        nonlocal high
        high+=1
        return high
    def eq_or(z,xs):
        for x in xs: enc.add(-x,z)
        enc.add(-z,*xs)
    def eq_and(z,xs):
        for x in xs: enc.add(-z,x)
        enc.add(z,*(-x for x in xs))
    def atmost(lits,bound):
        nonlocal high
        if bound<0:
            enc.add()
        elif bound<len(lits):
            cnf=CardEnc.atmost(lits=lits,bound=bound,top_id=high,encoding=EncType.seqcounter)
            high=max(high,cnf.nv)
            enc.cnf.extend(cnf.clauses)
    def mux(z,e,j,inputs,gates):
        # z is the Boolean attribute of selected source; sentinel is false.
        for k in range(n+j+1):
            a=v(e,j,k)
            if k<n:
                enc.add(-a,z if inputs[k] else -z)
            elif k<n+j:
                x=gates[k-n]
                enc.add(-a,-z,x)
                enc.add(-a,z,-x)
            else:
                enc.add(-a,-z)

    dirty=[fresh() for _ in range(s)]
    top=[fresh() for _ in range(s)]
    sides=[]
    # OR-input reachability for each gate output.
    reaches=[]
    # For each positive edge row, some dirty AND true on that row
    # is in the OR-closure of this gate's wire.
    dirty_reach=[]
    centreless=[]
    centred=[]
    covered_by=[[] for _ in edges]
    routed_by=[[] for _ in edges]
    for j in range(s):
        a,o=v(0,j,0),v(0,j,1)
        d,t=dirty[j],top[j]
        vals=[v(3,j,r) for r in negatives]
        enc.add(-d,a)
        enc.add(-d,*vals)
        for z in vals: enc.add(-a,-z,d)
        eq_and(t,[a,-d])
        lr=[[fresh() for _ in range(n)] for _ in (1,2)]
        sides.append(lr)
        for e in (1,2):
            for i in range(n):
                mux(lr[e-1][i],e,j,[k==i for k in range(n)],
                    [r[i] for r in reaches])
        out=[]
        for i in range(n):
            z=fresh()
            union=fresh()
            eq_or(union,[lr[0][i],lr[1][i]])
            eq_and(z,[o,union])
            out.append(z)
        reaches.append(out)
        nonempty=[fresh(),fresh()]
        for e in (0,1): eq_or(nonempty[e],lr[e])
        c=fresh()
        c_empty=fresh()
        eq_or(c_empty,[-nonempty[0],-nonempty[1]])
        eq_and(c,[t,c_empty])
        centreless.append(c)
        q=fresh()
        eq_and(q,[t,nonempty[0],nonempty[1]])
        centred.append(q)
        # h4: every cross pair of a top is an edge.
        for i in range(n):
            for k in range(n):
                if i==k or tuple(sorted((i,k))) not in eset:
                    enc.add(-t,-lr[0][i],-lr[1][k])
        # h4: at least one side of each top has cardinality <= 1.
        choose=fresh()
        for e in (0,1):
            for x,y in itertools.combinations(lr[e],2):
                enc.add(-t,choose if e==0 else -choose,-x,-y)
        out_dirty=[]
        for k,((u,w),r) in enumerate(zip(edges,enc.masks)):
            # Is this edge a top cross pair?
            ab,ba,cv=fresh(),fresh(),fresh()
            eq_and(ab,[lr[0][u],lr[1][w]])
            eq_and(ba,[lr[0][w],lr[1][u]])
            union=fresh()
            eq_or(union,[ab,ba])
            eq_and(cv,[t,union])
            covered_by[k].append(cv)
            # OR-closure reaches a dirty AND which is true on this pair.
            ds=[fresh(),fresh()]
            for e in (1,2):
                mux(ds[e-1],e,j,[False]*n,[r0[k] for r0 in dirty_reach])
            du,via,own,z=fresh(),fresh(),fresh(),fresh()
            eq_or(du,ds)
            eq_and(via,[o,du])
            eq_and(own,[d,v(3,j,r)])
            eq_or(z,[via,own])
            out_dirty.append(z)
            # h5: some top true at this edge reads such a dirty AND.
            hit=fresh()
            eq_and(hit,[t,v(3,j,r),du])
            routed_by[k].append(hit)
        dirty_reach.append(out_dirty)
    covered=[]
    cover=[fresh() for _ in range(n)]
    for k,(u,w) in enumerate(edges):
        z=fresh()
        eq_or(z,covered_by[k])
        covered.append(z)
        enc.add(z,*routed_by[k])  # uncovered -> routed
        # h7: a vertex cover of the graph after deletion of Ustar exists.
        enc.add(-z,cover[u],cover[w])
    # Existence of a cover of size <= number of centred tops is equivalent
    # to the bound on the minimum cover in h7 (finite graph).
    atmost(cover+[-x for x in centred],s)
    # h6: base + tops + centreless <= real gates + uncovered edges.
    # Drops the nonnegative |orN \ lam| term, so this is only necessary.
    atmost(top+centreless+covered+[v(7,j,0) for j in range(s)],
           s+len(edges)-base)


def check_star(n,masks,w,base=17):
    """Independent evaluator for all new constraints, using full inputs."""
    st=v2.verify_topform(n,masks,w)
    rows=range(1<<n)
    values=[sum(1<<r for r in rows if r&(1<<i)) for i in range(n)]
    reaches=[{i} for i in range(n)]
    closure=[set() for _ in range(n)]
    dirty=set(st["dirty_gates"])
    tops=set(st["top_gates"])
    edges=[tuple(i for i in range(n) if r&(1<<i)) for r in masks]
    eset=set(edges)
    covered=set()
    routed=set()
    c=0
    h4=True
    for j,(op,a,b) in enumerate(w["gates"]):
        A,B=reaches[a],reaches[b]
        val=values[a]&values[b] if op=="and" else values[a]|values[b]
        values.append(val)
        reaches.append(A|B if op=="or" else set())
        closure.append({j}|closure[a]|closure[b] if op=="or" else {j})
        if j in tops:
            c+=not A or not B
            cross={tuple(sorted((u,v))) for u in A for v in B}
            h4=h4 and cross<=eset and min(len(A),len(B))<=1
            covered|=cross&eset
            for edge,r in zip(edges,masks):
                if (val>>r)&1 and any((values[n+k]>>r)&1 for k in (closure[a]|closure[b])&dirty):
                    routed.add(edge)
    uncovered=eset-covered
    t=len(tops)-c
    tau=min((x.bit_count() for x in rows if all(
        x&((1<<u)|(1<<v)) for u,v in covered)),default=n)
    h5=uncovered<=routed
    h7=tau<=t
    h6=base+len(tops)+c<=len(w["gates"])+len(uncovered)
    return {**st,"star_h4":h4,"routing_h5":h5,"relaxed_h6":h6,"cover_h7":h7,
            "covered_edges":len(covered),"ustar":len(uncovered),"centred":t,
            "centreless":c,"min_cover":tau,
            "valid":st["valid"] and h4 and h5 and h6 and h7}


def build(n,edges,s,profile,lex,base=17):
    masks=v1.graph(n,edges)
    if not masks: raise ValueError("empty graph unsupported")
    orig=v1.Encoding(n,s,masks,v1.rows_for(n,masks),lex).build()
    if profile!="dense":
        v2.add_onehot(orig)
    if profile in ("topform","star"):
        v2.add_topform(orig)
    if profile=="star":
        add_star(orig,base)
    return v2.Compact(orig,"topform" if profile in ("topform","star") else profile)


def limited_worker(enc,profile,base,solver_name,chunk,conn):
    try:
        from pysat.solvers import Solver
        t=time.monotonic()
        with Solver(name=solver_name,bootstrap_with=enc.cnf) as sol:
            last=0
            while True:
                sol.conf_budget(chunk)
                ans=sol.solve_limited()
                now=time.monotonic()
                if ans is not None:
                    break
                if now-last>=0.5:
                    conn.send({"status":"PROGRESS","solve_seconds":round(now-t,3),
                               "stats":sol.accum_stats()})
                    last=now
            r={"status":"SAT" if ans else "UNSAT",
               "solve_seconds":round(time.monotonic()-t,3),"stats":sol.accum_stats()}
            if ans:
                try:
                    w=enc.decode(sol.get_model())
                    ok=v1.verify(enc.n,enc.masks,w)
                    if profile=="star":
                        w["star_check"]=check_star(enc.n,enc.masks,w,base)
                        ok=ok and w["star_check"]["valid"]
                    r.update(witness=w,verified_full_truth_table=ok)
                    if not ok:r["status"]="MODEL_INVALID"
                except Exception as e:
                    r.update(status="MODEL_INVALID",error=repr(e))
            conn.send(r)
    except Exception as e:
        conn.send({"status":"ERROR","error":repr(e)})
    finally:
        conn.close()


def solve(enc,profile,base,name,seconds,chunk):
    ctx=mp.get_context("fork")
    recv,send=ctx.Pipe(False)
    proc=ctx.Process(target=limited_worker,args=(enc,profile,base,name,chunk,send),daemon=True)
    start=time.monotonic()
    proc.start()
    send.close()
    last={}
    try:
        while True:
            remain=seconds-(time.monotonic()-start)
            if remain<=0 or not recv.poll(remain):
                result={"status":"TIMEOUT","last_progress":last}
                break
            try:r=recv.recv()
            except EOFError:
                result={"status":"ERROR","error":"worker exited without result","last_progress":last}
                break
            if r["status"]!="PROGRESS":
                result=r
                break
            last=r
    finally:
        recv.close()
        proc.join(.15)
        if proc.is_alive():
            proc.terminate();proc.join(1)
        if proc.is_alive():
            proc.kill();proc.join()
    result["wall_seconds"]=round(time.monotonic()-start,3)
    return result


def run(n,edges,s,profile,lex,solver,seconds,chunk,base=17):
    t=time.monotonic()
    enc=build(n,edges,s,profile,lex,base)
    meta={"profile":profile,"encoding":"enc2" if lex else "enc",
          "solver":solver,"gates":s,"clauses":len(enc.cnf),
          "variables":enc.max_var,"build_seconds":round(time.monotonic()-t,3)}
    print("[CNF]",json.dumps(meta),flush=True)
    r=solve(enc,profile,base,solver,seconds,chunk)
    print("[RESULT]",json.dumps(r),flush=True)
    return {**meta,**r}


def self_test(solver,seconds,chunk):
    # Same edge-function witness used in v2; offset 0 permits small tests.
    n,edges=3,[(0,1)]
    w={"gates":[("and",0,2),("and",0,3),("and",1,4),("and",0,1),
                ("or",5,6)],"output":7}
    assert v1.verify(n,v1.graph(n,edges),w)
    assert check_star(n,v1.graph(n,edges),w,0)["valid"]
    # Force known witness on all selectors: check no new constraint excludes it.
    from pysat.solvers import Solver
    enc=build(n,edges,5,"star",False,0)
    orig=enc.original
    fwd={x:i for i,x in enumerate(enc.reverse) if i}
    assumptions=[]
    for j,(op,a,b) in enumerate(w["gates"]):
        assumptions.extend(fwd[orig.v(k,j,z)] for k,z in
                           ((0,0 if op=="and" else 1),(1,min(a,b)),(2,max(a,b))))
    assumptions.append(fwd[orig.v(6,0,w["output"])])
    with Solver(name=solver,bootstrap_with=enc.cnf) as sol:
        assert sol.solve(assumptions=assumptions),"known witness excluded"
        decoded=enc.decode(sol.get_model())
        assert check_star(n,enc.masks,decoded,0)["valid"]
    for s,expected in ((1,"UNSAT"),(5,"SAT")):
        r=run(n,edges,s,"star",False,solver,seconds,chunk,0)
        assert r["status"]==expected,r
    for s,expected in ((3,"UNSAT"),(4,"SAT")):
        n,edges=v1.CASES["triangle"]
        r=run(n,edges,s,"dense",True,solver,seconds,chunk,0)
        assert r["status"]==expected,r
    print("SAT V3 SELF TEST OK",flush=True)


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--case",choices=v1.CASES,default="l2260")
    ap.add_argument("--gates",type=int,default=21)
    ap.add_argument("--solver",default="g4")
    ap.add_argument("--seconds",type=float,default=20)
    ap.add_argument("--chunk",type=int,default=1000)
    ap.add_argument("--profile",choices=("dense","onehot","topform","star"),default="star")
    ap.add_argument("--no-lex",action="store_true")
    ap.add_argument("--compare",action="store_true",help="topform and star, no lex, both solvers")
    ap.add_argument("--json-out",type=Path)
    ap.add_argument("--self-test",action="store_true")
    a=ap.parse_args()
    if a.gates<0 or a.seconds<=0 or a.chunk<=0:ap.error("invalid bound")
    if a.self_test:
        self_test(a.solver,a.seconds,a.chunk)
        return
    n,edges=v1.CASES[a.case]
    cases=list(itertools.product(("topform","star"),("g4","cadical195"))) if a.compare else [(a.profile,a.solver)]
    results=[]
    for p,name in cases:
        r=run(n,edges,a.gates,p,False if a.compare else not a.no_lex,name,a.seconds,a.chunk)
        results.append(r)
        if r["status"] in ("ERROR","MODEL_INVALID"):raise SystemExit(1)
    if a.json_out:a.json_out.write_text(json.dumps(results,indent=2)+"\n")
    print("[SUMMARY]",json.dumps([{"profile":r["profile"],"solver":r["solver"],
          "status":r["status"],"stats":r.get("stats",r.get("last_progress",{}).get("stats",{}))}
          for r in results]),flush=True)


if __name__=="__main__":
    main()
