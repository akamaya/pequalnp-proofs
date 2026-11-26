#!/usr/bin/env python3
"""Local positive graph theorem solver. No lease, submission, Git writes, or LLM calls."""
import argparse
import hashlib
import json
import re
import time
from pathlib import Path
import pnp_graph_support_v1 as support
import pnp_graph_binary_v3 as binary
import pnp_graph_binary_width_v1 as widthlib
import pnp_graph_binary_pairs_v1 as pair
import pnp_graph_certificate_v3 as guard

DEFAULT = Path.home() / 'dev/LeanDojo-v2/proof-logs/graph-solve-v1'

def get_statement(source):
    names = re.findall(r'^theorem\s+PEqualNP\.Outside\.(L_meta_\d+)\s*:', source, re.M)
    if len(names) != 1:
        raise ValueError('expected exactly one fully-qualified L_meta theorem')
    stem = names[0]
    decl, n, edges, rhs = binary.parse_statement(stem, source)
    return stem, decl, n, edges, rhs

def screen(n, edges, cap, widths, seeds, seconds, max_states):
    for w in widths:
        for seed in range(seeds):
            rows, near = pair.pairs(n, edges, w, seed)
            words = widthlib.words_for(rows, n)
            status, states, elapsed = widthlib.screen(words, w, cap, seconds, max_states)
            rec = dict(width=w, seed=seed, adjacent=near, status=status, states=states, seconds=round(elapsed, 4))
            print(f'[SCREEN] width={w} seed={seed} {status} states={states} wall={elapsed:.3f}s', flush=True)
            yield rec, rows, words

def choose(trials):
    # Prefer estimated kernel bit-work, then smaller width. Keep one best seed per width.
    best = {}
    def score(t):
        r = t[0]
        return r['width'] * r['states'], r['width'], r['seed']
    for t in trials:
        r = t[0]
        if r['status'] != 'NO_RUN': continue
        if r['width'] not in best or score(t) < score(best[r['width']]): best[r['width']] = t
    return sorted(best.values(), key=score)

def save(path, data):
    pair.save(path, data)

def self_test():
    stem='L_meta_123'; rhs='decide (∃ i < ([0, 1] : List ℕ).length / 2, (List.ofFn x).getD (([0, 1] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 1] : List ℕ).getD (2 * i + 1) 0) false = true)'
    decl=f"theorem PEqualNP.Outside.{stem} : ∀ (gates : List Nat), (∀ x : Fin 2 → Bool, true = {rhs}) → ∃ gates' : List Nat, gates'.length ≤ gates.length ∧ ∀ x : Fin 2 → Bool, true = {rhs}"
    assert get_statement(decl+' := by\n  sorry')[:4] == (stem, decl, 2, [(0,1)])
    for s in (decl.replace(': ∀', ': ¬ ∀',1)+' := by sorry', decl, decl+' := by sorry\n'+decl+' := by sorry'):
        try: get_statement(s)
        except ValueError: pass
        else: raise AssertionError('bad source accepted')
    e=[(0,4),(0,5),(1,5),(1,6),(2,6),(1,7),(2,7),(3,7)]
    g,o=support.synth(8,e); assert len(g)==10; support.verify(8,e,g,o)
    t=list(screen(8,e,8,[128,256,512],2,5,100000))
    b=choose(t); assert len(b)==3 and all(x[0]['status']=='NO_RUN' for x in b)
    assert next(x[0]['states'] for x in b if x[0]['width']==256)==22
    e=[(0,2),(0,3),(1,2),(1,3)]
    assert not choose(list(screen(4,e,3,[128],1,5,100000)))
    print('SOLVER SELF TEST OK (Python only)',flush=True)

def main():
    p=argparse.ArgumentParser(description=__doc__)
    src=p.add_mutually_exclusive_group(); src.add_argument('--source',type=Path); src.add_argument('--historical-id'); src.add_argument('--self-test',action='store_true')
    p.add_argument('--repo',type=Path,default=Path.home()/'dev/pequalnp-proofs'); p.add_argument('--out',type=Path,default=DEFAULT)
    p.add_argument('--widths',type=int,nargs='+',default=[128,256,512]); p.add_argument('--seeds',type=int,default=2)
    p.add_argument('--seconds',type=float,default=5); p.add_argument('--max-states',type=int,default=500000)
    p.add_argument('--timeout',type=float,default=180); p.add_argument('--max-rss-gib',type=float,default=20); p.add_argument('--jobs',type=int,default=4)
    p.add_argument('--check',action='store_true'); p.add_argument('--check-limit',type=int,default=2); p.add_argument('--profile',action='store_true')
    a=p.parse_args()
    if a.self_test: self_test(); return
    if not (a.source or a.historical_id): p.error('use --source or --historical-id')
    if min(a.seconds,a.max_states,a.seeds,a.timeout,a.max_rss_gib,a.jobs,a.check_limit)<=0 or any(w not in (64,128,256,512) for w in a.widths): p.error('invalid limits')
    repo=a.repo.resolve(); root=a.out.resolve()
    if root.is_relative_to(repo): p.error('output must be outside repository')
    ref=support.REV
    if a.historical_id:
        if not re.fullmatch(r'L_meta_\d+',a.historical_id): p.error('invalid historical ID')
        source=support.git_show(repo,ref,a.historical_id)
    else: source=a.source.read_text(encoding='utf-8')
    stem,decl,n,edges,rhs=get_statement(source)
    if a.historical_id and stem!=a.historical_id: raise ValueError('historical ID mismatch')
    # Fresh directory per run; never overwrite inputs or earlier verified files.
    out=root/stem/(time.strftime('%Y%m%d-%H%M%S')+'-'+str(time.time_ns()%1000000000).zfill(9)); out.mkdir(parents=True,exist_ok=False)
    (out/'input.lean').write_text(source,encoding='utf-8')
    report=dict(stem=stem,n=n,edges=edges,revision=ref,historical=bool(a.historical_id),source_sha256=hashlib.sha256(source.encode()).hexdigest(),trials=[],checks=[])
    rp=out/'results.json'; save(rp,report)
    gates,output=support.synth(n,edges); support.verify(n,edges,gates,output); m=len(gates)
    report['gates']=m; print(f'[WITNESS] {stem} n={n} mono={m} all {2**n} rows PASS',flush=True)
    choices=[]
    if m<=n:
        template=support.git_show(repo,ref,support.TEMPLATE)
        # Support renderer expects := by. Preserve exact original declaration, not its old proof.
        text=support.render(stem,decl+' := by\n  sorry\n',template,ref)
        if text is None: raise ValueError('support renderer declined eligible witness')
        choices.append(('support',text,{'method':'support'}))
    else:
        trials=list(screen(n,edges,m-2,dict.fromkeys(a.widths),a.seeds,a.seconds,a.max_states))
        report['trials']=[t[0] for t in trials]; save(rp,report)
        best=choose(trials)
        if best:
            template=support.git_show(repo,ref,binary.TEMPLATE)
            oldrows,oldwords=binary.make_rows(n,edges)
            base=binary.raise_limits(binary.render(stem,source,template,ref,gates,output,oldrows,oldwords),60000)
            for t,rows,words in best:
                w=t['width']; text=widthlib.rewrite(base,stem,rows,words,w)
                choices.append((f'width-{w}',text,dict(method='binary-pairs',**t)))
    if not choices:
        report['status']='NO_CERTIFICATE'; save(rp,report)
        print(f'[NO CERTIFICATE] {stem}: screening inconclusive for this proof method; not a refutation.\n[JSON] {rp}',flush=True); return 2
    for idx,(label,text,rec) in enumerate(choices):
        if binary.parse_statement(stem,text)[0]!=decl: raise ValueError('generated theorem statement changed')
        d=out/label; d.mkdir(); candidate=d/(stem+'.candidate.lean'); candidate.write_text(text,encoding='utf-8')
        rec['candidate']=str(candidate); report['checks'].append(rec); save(rp,report); print('[CANDIDATE]',candidate,flush=True)
        if not a.check or idx>=a.check_limit: continue
        rec.update(guard.check(repo,stem,text,d,a.timeout,a.max_rss_gib,a.jobs,a.profile)); save(rp,report)
        if rec['lean_ok']:
            verified=d/(stem+'.verified.lean'); verified.write_text(text,encoding='utf-8'); report.update(status='VERIFIED',verified=str(verified)); save(rp,report)
            print(f'[VERIFIED] {verified}\n[JSON] {rp}\nSOLVED LOCALLY (no submission)',flush=True); return 0
    report['status']='CHECK_FAILED' if a.check else 'CANDIDATES_ONLY'; save(rp,report)
    print(f'[SUMMARY] {report["status"]} (no submission)\n[JSON] {rp}',flush=True); return 1 if a.check else 0

if __name__=='__main__':
    raise SystemExit(main())
