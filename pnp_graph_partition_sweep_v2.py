#!/usr/bin/env python3
"""Graph partition sweep v2: same formulas as v1, SQLite checkpoints.

One atomic result transaction per partition instead of rewriting the
entire JSON checkpoint. No changes to enumeration or SAT constraints.
"""
import argparse
import concurrent.futures as cf
import hashlib
import json
import multiprocessing as mp
from pathlib import Path
import sqlite3
import tempfile
import time
import fcntl
import pnp_graph_partition_sweep_v1 as sweep

EXPECTED={(7,4):(82,0),(7,5):(11517,1272),(7,6):(111389,31692),
          (6,5):(1417,69),(6,6):(34179,6482),(6,7):(118793,60423),
          (6,8):(147131,139723),(5,6):(6349,878),(5,7):(44358,15188),
          (5,8):(69713,57080),(5,9):(70736,70736),(5,10):(70737,70737)}

def open_db(path,key):
    db=sqlite3.connect(path)
    try:
        db.execute("PRAGMA journal_mode=WAL")
        db.execute("PRAGMA synchronous=NORMAL")
        with db:
            db.execute("CREATE TABLE IF NOT EXISTS meta (id INTEGER PRIMARY KEY CHECK(id=1), fingerprint TEXT NOT NULL)")
            db.execute("CREATE TABLE IF NOT EXISTS results (id INTEGER PRIMARY KEY, status TEXT NOT NULL, payload TEXT NOT NULL)")
            old=db.execute("SELECT fingerprint FROM meta WHERE id=1").fetchone()
            if old is None:
                if db.execute("SELECT COUNT(*) FROM results").fetchone()[0]:
                    raise ValueError("checkpoint missing fingerprint")
                db.execute("INSERT INTO meta VALUES(1,?)",(key,))
            elif old[0]!=key:
                raise ValueError("checkpoint fingerprint mismatch")
        return db
    except BaseException:
        db.close()
        raise

def save(db,idx,out):
    with db:
        db.execute("INSERT OR REPLACE INTO results VALUES(?,?,?)",
                   (idx,out["status"],json.dumps(out,separators=(",",":"))))

def load(db,parts):
    states={}
    for idx,st,payload in db.execute("SELECT id,status,payload FROM results"):
        out=json.loads(payload)
        if not 1<=idx<=len(parts) or out.get("status")!=st:
            raise ValueError("invalid checkpoint row")
        if st=="UNSAT" and (out.get("partition")!=idx or out.get("assignment")!=list(parts[idx-1])):
            raise ValueError("checkpoint partition mismatch")
        states[idx]=st
    return states

def self_test(solver):
    sweep.ex.self_test(solver)
    with tempfile.TemporaryDirectory() as root:
        path=Path(root)/"test.sqlite3"
        parts=[(0,0,1),(0,1,2)]
        db=open_db(path,"test")
        save(db,1,{"status":"TIMEOUT"})
        save(db,1,{"status":"UNSAT","partition":1,"assignment":[0,0,1]})
        save(db,2,{"status":"TIMEOUT"})
        db.close()
        db=open_db(path,"test")
        assert load(db,parts)=={1:"UNSAT",2:"TIMEOUT"}
        db.close()
        try:open_db(path,"different")
        except ValueError:pass
        else:raise AssertionError("fingerprint mismatch not rejected")
    print("PARTITION SWEEP V2 SELF TEST OK",flush=True)

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--top-count",type=int,default=5)
    ap.add_argument("--or-count",type=int,default=7)
    ap.add_argument("--seconds",type=float,default=5)
    ap.add_argument("--jobs",type=int,default=8)
    ap.add_argument("--solver",default="cadical195")
    ap.add_argument("--chunk",type=int,default=20000)
    ap.add_argument("--mode",choices=("compact","canonical"),default="compact")
    ap.add_argument("--checkpoint",type=Path)
    ap.add_argument("--self-test",action="store_true")
    ap.add_argument("--list-only",action="store_true")
    a=ap.parse_args()
    k,r=a.top_count,a.or_count
    if k<1 or r<0 or 2*k+1+r>21 or min(a.jobs,a.chunk)<1 or a.seconds<=0:
        ap.error("invalid case or limits")
    if a.self_test:self_test(a.solver);return
    start=time.monotonic()
    n,edges=sweep.v1.CASES["l2260"]
    parts,generic=sweep.candidates(n,edges,k,r)
    if (k,r) in EXPECTED and (generic,len(parts))!=EXPECTED[k,r]:
        raise ValueError("v1 enumeration cross-check failed")
    counts={}
    for p in parts:
        b=max(p)+1
        counts[b]=counts.get(b,0)+1
    print("[PARTITIONS]",json.dumps({"k":k,"r":r,"generic":generic,
          "refined":len(parts),"by_blocks":counts,
          "enumeration_seconds":round(time.monotonic()-start,3)}),flush=True)
    if a.list_only:return
    root=Path(__file__).resolve().parent
    h=hashlib.sha256(json.dumps([n,edges,k,r,a.mode,parts]).encode())
    for name in sweep.v19.DEPS+("pnp_sat_solve_v19.py","pnp_graph_partition_exact_v1.py",
            "pnp_graph_partition_sweep_v1.py","pnp_graph_partition_sweep_v2.py"):
        h.update((root/name).read_bytes())
    path=a.checkpoint or Path(f"sat-results/l2260-graph-sweep-v2-k{k}-r{r}-{a.mode}.sqlite3")
    path.parent.mkdir(parents=True,exist_ok=True)
    with open(str(path)+".lock","a") as lock:
        fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
        db=open_db(path,h.hexdigest())
        try:
            states=load(db,parts)
            pending=[i for i in range(1,len(parts)+1) if states.get(i)!="UNSAT"]
            unsat=len(parts)-len(pending)
            print("[CONFIG]",json.dumps({"pending":len(pending),"prior_unsat":unsat,
                  "jobs":a.jobs,"seconds":a.seconds,"solver":a.solver,
                  "checkpoint":str(path)}),flush=True)
            count=0
            if pending and "SAT" not in states.values():
                # Workers must not inherit an open SQLite connection.
                # spawn also works with v1.run's nested fork-based solver.
                with cf.ProcessPoolExecutor(max_workers=a.jobs,mp_context=mp.get_context("spawn")) as pool:
                    todo=iter(pending)
                    fs={}
                    stop=False
                    def fill():
                        while len(fs)<a.jobs:
                            idx=next(todo,None)
                            if idx is None:break
                            task=(idx,parts[idx-1],k,r,a.solver,a.seconds,a.chunk,a.mode)
                            fs[pool.submit(sweep.run,task)]=idx
                    fill()
                    last_report=0
                    while fs:
                        done,_=cf.wait(fs,return_when=cf.FIRST_COMPLETED)
                        for f in done:
                            idx=fs.pop(f)
                            try:out=f.result()
                            except Exception as e:out={"status":"ERROR","error":repr(e)}
                            save(db,idx,out)
                            st=out["status"]
                            states[idx]=st
                            count+=1
                            if st=="UNSAT":unsat+=1
                            else:print("[TARGET]",idx,json.dumps(out),flush=True)
                            if st in ("SAT","ERROR","MODEL_INVALID"):stop=True
                        if count-last_report>=100 or stop:
                            print("[PROGRESS]",json.dumps({"attempted":count,"unsat":unsat,
                                  "total":len(parts),"elapsed":round(time.monotonic()-start,3)}),flush=True)
                            last_report=count
                        if not stop:fill()
            rem=[i for i in range(1,len(parts)+1) if states.get(i)!="UNSAT"]
            state=("ERROR" if any(s in ("ERROR","MODEL_INVALID") for s in states.values())
                   else "SAT" if "SAT" in states.values()
                   else "UNRESOLVED" if rem else "ALL_PARTITIONS_UNSAT")
            print("[SUMMARY]",json.dumps({"status":state,"k":k,"r":r,"remaining_count":len(rem),
                  "remaining_partitions":rem,"total":len(parts),
                  "wall_seconds":round(time.monotonic()-start,3),"lean_verified":False}),flush=True)
            if state=="ERROR":raise SystemExit(1)
        finally:db.close()

if __name__=="__main__":main()
