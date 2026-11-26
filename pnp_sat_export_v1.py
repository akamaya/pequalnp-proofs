#!/usr/bin/env python3
"""Export resolved experimental formulas as DIMACS for certificate replay.

Exports only v9/v11 formulas and cut-free v14 outer formulas. A solver
status or DIMACS hash is NOT an UNSAT certificate, nor a Lean theorem.
No proof submission. All output stays under the selected directory.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import tempfile
import pnp_sat_solve_v1 as v1
import pnp_sat_solve_v9 as v9
import pnp_sat_solve_v11 as v11
import pnp_sat_solve_v14 as v14


def write_cnf(path,enc,extra=()):
    clauses=enc.cnf+list(extra)
    tmp=path.with_suffix(".cnf.tmp")
    with tmp.open("w",encoding="ascii",newline="\n") as f:
        f.write(f"p cnf {enc.max_var} {len(clauses)}\n")
        for c in clauses:
            if any(not 0<abs(x)<=enc.max_var for x in c):
                raise ValueError("invalid DIMACS literal")
            f.write(" ".join(map(str,c))+(" " if c else "")+"0\n")
    os.replace(tmp,path)
    return {"file":path.name,"variables":enc.max_var,"clauses":len(clauses),
            "sha256":hashlib.sha256(path.read_bytes()).hexdigest()}


def load(path,expected):
    data=json.loads(path.read_text())
    if data.get("fingerprint")!=expected:raise ValueError(f"checkpoint mismatch: {path}")
    return data


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--seed-v9",type=Path,default=Path("sat-results/l2260-v9.json"))
    ap.add_argument("--seed-v11",type=Path,default=Path("sat-results/l2260-v11-exact.json"))
    ap.add_argument("--seed-v14",type=Path,default=Path("sat-results/l2260-v14-cegar.json"))
    ap.add_argument("--out",type=Path,default=Path("sat-results/l2260-certificates"))
    ap.add_argument("--self-test",action="store_true")
    a=ap.parse_args()
    if a.self_test:
        from pysat.formula import CNF
        from pysat.solvers import Solver
        enc=v9.Encoding(3,[(0,1)],3,1,0).build()
        with tempfile.TemporaryDirectory() as d:
            path=Path(d)/"test.cnf"
            meta=write_cnf(path,enc)
            obj=CNF(from_file=str(path))
            assert obj.clauses==enc.cnf
            assert meta["clauses"]==len(obj.clauses)
            with Solver(name="g4",bootstrap_with=obj.clauses) as sol:
                assert not sol.solve()
        print("SAT EXPORT SELF TEST OK")
        return
    n,edges=v1.L2260
    total,base=21,17
    counts=list(range(10,0,-1))
    old9=load(a.seed_v9,v11.digest([n,edges,total,base,counts],v11.FILES))
    old11=load(a.seed_v11,v11.digest([n,edges,total,base,counts,"exact"],
                    v11.FILES+("pnp_sat_solve_v11.py",)))
    manifest={str(k):list(range(total-2*k)) for k in counts}
    if old11.get("manifest")!=manifest:raise ValueError("v11 partition mismatch")
    prior=set()
    for k in counts:
        if str(k) in old11["inherited"]:
            if old9["results"].get(str(k),{}).get("status")!="UNSAT":
                raise ValueError("missing inherited v9 UNSAT")
        for r in manifest[str(k)]:
            if str(k) in old11["inherited"] or old11["results"].get(f"{k}:{r}",{}).get("status")=="UNSAT":
                prior.add((k,r))
    jobs=[]
    for k in counts:
        rr=[r for r in manifest[str(k)] if (k,r) not in prior]
        if rr:jobs.append((k,max(rr)))
    deps=v11.FILES+("pnp_sat_solve_v11.py","pnp_sat_solve_v12.py",
                   "pnp_sat_solve_v13.py","pnp_sat_solve_v14.py")
    old14=load(a.seed_v14,v11.digest([n,edges,total,base,jobs,True],deps))
    a.out.mkdir(parents=True,exist_ok=True)
    records=[]
    covered=set()
    def emit(k,rs,kind,enc,extra,log,clausekey,varkey,name):
        if log.get("status")!="UNSAT":raise ValueError("not UNSAT")
        if len(enc.cnf)+len(extra)!=log[clausekey] or enc.max_var!=log[varkey]:
            raise ValueError(f"formula dimension mismatch: {name}")
        meta=write_cnf(a.out/name,enc,extra)
        row={**meta,"kind":kind,"top_count":k,"covered_or_counts":rs,
             "solver_report":"UNSAT","certificate_verified":False}
        records.append(row)
        covered.update((k,r) for r in rs)
        print("[EXPORTED]",json.dumps(row),flush=True)
    for k in counts:
        rs=manifest[str(k)]
        r9=old9["results"].get(str(k),{})
        if r9.get("status")=="UNSAT":
            enc=v9.Encoding(n,edges,total,k,base).build()
            emit(k,rs,"v9",enc,[],r9,"clauses","variables",f"k{k:02d}-v9.cnf")
            continue
        r14=old14["results"].get(str(k),{})
        budget=dict(jobs).get(k)
        if (budget is not None and r14.get("status")=="UNSAT"
                and r14.get("or_budget")==budget and r14.get("cut_count")==0
                and r14.get("cuts")==[] and r14.get("candidates")==0):
            enc=v14.Relax(n,edges,total,k,base,budget,True).build()
            emit(k,list(range(budget+1)),"v14-cut-free-relaxation",enc,[],r14,
                 "outer_clauses","outer_variables",f"k{k:02d}-v14-relax.cnf")
        # Export resolved exact cubes that are not covered by a broader formula.
        for r in rs:
            if (k,r) in covered:continue
            log=old11["results"].get(f"{k}:{r}",{})
            if log.get("status")!="UNSAT":continue
            enc=v9.Encoding(n,edges,total,k,base).build()
            units=[[x] for x in v11.exact_units(enc.active,r)]
            emit(k,[r],"v11-exact",enc,units,log,"clauses","variables",
                 f"k{k:02d}-r{r:02d}-v11.cnf")
    remaining=[[k,r] for k in counts for r in manifest[str(k)] if (k,r) not in covered]
    report={"case":"l2260","vertices":n,"edges":edges,"gate_bound":total,"base":base,
            "source_sha256":{name:hashlib.sha256((v11.ROOT/name).read_bytes()).hexdigest()
                             for name in deps},
            "formulas":records,"covered_cubes":len(covered),"remaining":remaining,
            "formal_reduction_verified":False,"certificates_verified":False}
    tmp=a.out/"manifest.json.tmp"
    tmp.write_text(json.dumps(report,indent=2)+"\n")
    os.replace(tmp,a.out/"manifest.json")
    print("[SUMMARY]",json.dumps({"formulas":len(records),"covered_cubes":len(covered),
        "remaining":len(remaining),"output":str(a.out),"certificates_verified":False}),flush=True)


if __name__=="__main__":main()
