#!/usr/bin/env python3
"""Optimize signed-live-search sample pairs, with original Lean proof and guarded verification.
Uses existing Binary v3, Width v1 and Certificate v3 helpers. No submissions or repo edits.
"""
import argparse
import json
import random
import re
from pathlib import Path
import pnp_graph_binary_v3 as binary
import pnp_graph_binary_width_v1 as widthlib
import pnp_graph_certificate_v3 as guard

DEFAULT = Path.home() / 'dev/LeanDojo-v2/proof-logs'


def truth(n, edges, row):
    return any(row >> a & 1 and row >> b & 1 for a,b in edges)


def pairs(n, edges, width, seed):
    half = width // 2
    if not n <= half or not 2 <= n <= 8:
        raise ValueError('unsupported dimension')
    pos = [x for x in range(1 << n) if truth(n, edges, x)]
    neg = [x for x in range(1 << n) if not truth(n, edges, x)]
    essential = []
    for i in range(n):
        j = next((b if a == i else a for a,b in edges if i in (a,b)), None)
        if j is None:
            raise ValueError('isolated input')
        essential.append((1 << j, (1 << j) | (1 << i)))
    if len(set(essential)) != n or any(truth(n,edges,x) or not truth(n,edges,y) for x,y in essential):
        raise ValueError('bad essential pairs')
    required = set(essential)
    pool = [(x,y) for x in neg for y in pos if (x,y) not in required]
    rng = random.Random(seed)
    rng.shuffle(pool)
    pool.sort(key=lambda p: (p[0] ^ p[1]).bit_count())
    chosen = essential + pool[:half-n]
    # Very small graphs may have fewer distinct pairs than the requested width.
    if len(chosen) < half:
        chosen += [chosen[i % len(chosen)] for i in range(half-len(chosen))]
    assert len(chosen) == half
    assert all(not truth(n,edges,x) and truth(n,edges,y) for x,y in chosen)
    rows = [x for x,y in chosen] + [y for x,y in chosen]
    return rows, sum((x^y).bit_count()==1 for x,y in chosen)


def save(path, obj):
    tmp=path.with_suffix('.tmp'); tmp.write_text(json.dumps(obj,indent=2)+'\n',encoding='utf-8'); tmp.replace(path)


def self_test():
    e=[(0,4),(0,5),(1,5),(1,6),(2,6),(1,7),(2,7),(3,7)]
    rows,words=binary.make_rows(8,e)
    r,s,_=binary.screen(words,8,10,100000)
    assert (r,s)==('NO_RUN',3677),(r,s)
    print('[SELF TEST] original L_meta_14074 states=3677 PASS')
    for width in (128,256,512):
        rr,near=pairs(8,e,width,0); ww=widthlib.words_for(rr,8)
        r,s,_=widthlib.screen(ww,width,8,10,100000)
        assert r=='NO_RUN' and s<3677,(width,r,s)
        if width in (256,512): assert s==22,(width,s)
        print(f'[SELF TEST] near pairs width={width} states={s} adjacent={near} PASS')
    e=[(0,2),(0,3),(1,2),(1,3)]
    rr,_=pairs(4,e,512,0); ww=widthlib.words_for(rr,4)
    assert widthlib.screen(ww,512,2,10,100000)[0]=='NO_RUN'
    assert widthlib.screen(ww,512,3,10,100000)[0]=='REACHABLE'
    print('[SELF TEST] reachable control PASS')
    widthlib.self_test() # source rewrite preserves statement, mask restoration
    print('PAIR SELF TEST OK (Python only)')


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--self-test',action='store_true'); p.add_argument('--id',default='L_meta_14074')
    p.add_argument('--from-dir',type=Path,default=DEFAULT/'graph-binary-extra2')
    p.add_argument('--out',type=Path,default=DEFAULT/'graph-binary-pairs-v1')
    p.add_argument('--repo',type=Path,default=Path.home()/'dev/pequalnp-proofs')
    p.add_argument('--widths',type=int,nargs='+',default=[512]); p.add_argument('--seeds',type=int,default=2)
    p.add_argument('--seconds',type=float,default=10); p.add_argument('--max-states',type=int,default=500000)
    p.add_argument('--check',action='store_true'); p.add_argument('--profile',action='store_true')
    p.add_argument('--timeout',type=float,default=180); p.add_argument('--max-rss-gib',type=float,default=20)
    p.add_argument('--jobs',type=int,default=4)
    a=p.parse_args()
    if a.self_test: self_test(); return
    if not re.fullmatch(r'L_meta_\d+',a.id) or any(w not in (64,128,256,512) for w in a.widths): p.error('invalid id or width')
    if min(a.seeds,a.seconds,a.max_states,a.timeout,a.max_rss_gib,a.jobs)<=0: p.error('invalid limits')
    repo,src,out=(x.expanduser().resolve() for x in (a.repo,a.from_dir,a.out))
    if out.is_relative_to(repo) or out.is_relative_to(src): p.error('output must be outside repo and source')
    text=(src/(a.id+'.candidate.lean')).read_text(encoding='utf-8')
    _,n,edges,_=binary.parse_statement(a.id,text)
    rm=widthlib.ROW_RE.search(text); wm=widthlib.ROOT_RE.search(text)
    cm=re.search(r'^theorem noSearch : search (\d+) roots = false := by$',text,re.M)
    if not rm or not wm or not cm: raise ValueError('expected original Binary v3 candidate')
    cap=int(cm[1]); oldrows=[int(x.strip()) for x in rm[1].split(',')]; oldwords=[int(x.strip(),0) for x in wm[1].split(',')]
    if len(oldrows)!=512 or any(not 0<=x<1<<n or truth(n,edges,x)!=(i>=256) for i,x in enumerate(oldrows)) or oldwords!=widthlib.words_for(oldrows,n): raise ValueError('invalid original rows')
    out=out/a.id; out.mkdir(parents=True,exist_ok=True)
    status,states,sec=binary.screen(oldwords,cap,a.seconds,a.max_states)
    print(f'[BASELINE] width=512 {status} states={states} wall={sec:.3f}s',flush=True)
    result={'id':a.id,'n':n,'cap':cap,'baseline':{'status':status,'states':states,'seconds':sec},'trials':[],'checks':[]}
    save(out/'results.json',result)
    successes=attempted=0
    for width in dict.fromkeys(a.widths):
        best=None
        for seed in range(a.seeds):
            rr,near=pairs(n,edges,width,seed); ww=widthlib.words_for(rr,n)
            st,ns,elapsed=widthlib.screen(ww,width,cap,a.seconds,a.max_states)
            print(f'[SCREEN] width={width} seed={seed} adjacent={near}/{width//2} {st} states={ns} wall={elapsed:.3f}s',flush=True)
            result['trials'].append(dict(width=width,seed=seed,adjacent=near,status=st,states=ns,seconds=elapsed)); save(out/'results.json',result)
            if st=='NO_RUN' and (best is None or ns<best[0]): best=(ns,seed,rr,ww)
        if best is None or (status=='NO_RUN' and best[0]>=states):
            print(f'[SKIP] width={width} no improved NO_RUN candidate',flush=True); continue
        ns,seed,rr,ww=best
        candidate=widthlib.rewrite(text,a.id,rr,ww,width)
        assert binary.parse_statement(a.id,candidate)==binary.parse_statement(a.id,text)
        # Same original noSearch, not Certificate's per-state Lean proof.
        assert candidate[candidate.index('theorem noSearch'):]==text[text.index('theorem noSearch'):] or width!=512
        d=out/f'width-{width}'; d.mkdir(exist_ok=True)
        path=d/(a.id+'.candidate.lean'); path.write_text(candidate,encoding='utf-8')
        print(f'[CANDIDATE] width={width} states={ns} {path}',flush=True)
        rec=dict(width=width,seed=seed,states=ns,candidate=str(path)); result['checks'].append(rec); save(out/'results.json',result)
        if a.check:
            attempted+=1; verified=d/(a.id+'.verified.lean'); verified.unlink(missing_ok=True)
            rec.update(guard.check(repo,a.id,candidate,d,a.timeout,a.max_rss_gib,a.jobs,a.profile))
            if rec['lean_ok']:
                successes+=1; verified.write_text(candidate,encoding='utf-8'); print('[VERIFIED]',verified,flush=True)
            save(out/'results.json',result)
    print(f'[SUMMARY] candidates={len(result["checks"])} Lean={successes}/{attempted} (no submission)',flush=True)
    if not result['checks'] or (a.check and successes!=attempted): raise SystemExit(1)

if __name__=='__main__': main()
