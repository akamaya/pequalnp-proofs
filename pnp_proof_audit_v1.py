#!/usr/bin/env python3
"""Read-only inventory of graph-circuit proofs at a pinned Git revision."""
import argparse, collections, itertools, json, re, subprocess
from pathlib import Path

TARGETS = {
    'L-meta-10643': (7, [(0,2),(1,3),(0,4),(1,4),(2,4),(0,5),(1,5),(3,5),(0,6),(1,6),(2,6),(3,6),(4,6),(5,6)]),
    'L-meta-14961': (8, [(0,4),(1,4),(0,5),(1,5),(0,6),(1,6),(2,6),(3,6),(0,7),(2,7),(3,7),(4,7)]),
    'L-meta-15033': (8, [(0,4),(1,4),(0,5),(1,5),(2,5),(0,6),(3,6),(4,6),(0,7),(1,7),(2,7),(4,7)]),
}
FEATURES = {'live': r'\bdef\s+Live\b', 'forest': r'\b(?:structure|def)\s+Forest\b|\bforestSound\b', 'cofactor': r'cofactor', 'kernel_decide': r'decide\s+\+kernel', 'native_decide': r'\bnative_decide\b', 'bv_decide': r'\bbv_decide\b', 'mono_witness': r'\bmonoWitness\b', 'binary_lower': r'\bbinaryLower\b'}

def git(repo, *args, allow_empty=False):
    p = subprocess.run(['git','-C',str(repo),*args], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    if p.returncode and not (allow_empty and p.returncode == 1):
        raise RuntimeError(p.stderr.decode(errors='replace').strip())
    return p.stdout

def graph_signature(n, edges):
    e = {tuple(sorted(x)) for x in edges}
    d = [sum(i in p for p in e) for i in range(n)]
    return e, d, (n, len(e), tuple(sorted(d)))

def isomorphic(n, a, b):
    ea, da, sa = graph_signature(n,a); eb, db, sb = graph_signature(n,b)
    if sa != sb: return False
    groups = [[i for i in range(n) if da[i] == k] for k in sorted(set(da))]
    dest = [[i for i in range(n) if db[i] == k] for k in sorted(set(da))]
    for perms in itertools.product(*(itertools.permutations(g) for g in dest)):
        m = dict(zip(itertools.chain.from_iterable(groups), itertools.chain.from_iterable(perms)))
        if {tuple(sorted((m[i],m[j]))) for i,j in ea} == eb: return True
    return False

def inspect(path, source):
    stem = Path(path).stem
    m = re.search(r'^\s*theorem\s+PEqualNP\.Outside\.'+re.escape(stem)+r'\s*:\s*',source,re.M)
    if not m: return None
    statement = source[m.end():].split(':=',1)[0]
    polarity = 'negative' if statement.lstrip().startswith(('¬','Not ')) else 'positive' if statement.lstrip().startswith('∀') else 'other'
    # Only identify graphs from a literal edge-list followed by its length / 2.
    nm = re.search(r'Fin\s+(\d+)\s*→\s*Bool', statement)
    em = re.search(r'\(\[([\d,\s]+)\]\s*:\s*List\s+ℕ\)\.length\s*/\s*2', statement)
    n = int(nm.group(1)) if nm else None
    edges = None
    if n is not None and em:
        flat = [int(x) for x in re.findall(r'\d+',em.group(1))]
        if len(flat)%2 == 0 and all(x<n for x in flat) and all(i!=j for i,j in zip(flat[::2],flat[1::2])):
            edges = list(zip(flat[::2],flat[1::2]))
    return {'path':path,'lines':len(source.splitlines()),'polarity':polarity,'n':n,'edges':edges,'features':[k for k,v in FEATURES.items() if re.search(v,source,re.I)],'references':sorted(set(re.findall(r'\bL_meta_\d+\b', '\n'.join(source.splitlines()[:12])))-{stem})}

def main():
    p=argparse.ArgumentParser(); p.add_argument('--repo',type=Path,default=Path.home()/'dev/pequalnp-proofs'); p.add_argument('--ref',default='FETCH_HEAD'); p.add_argument('--output',type=Path,default=Path.home()/'dev/LeanDojo-v2/proof-logs/graph_proof_audit.json'); a=p.parse_args()
    rev=git(a.repo,'rev-parse','--verify',a.ref+'^{commit}').decode().strip()
    paths=git(a.repo,'grep','-l','-z','-F',"gates'.length ≤ gates.length",rev,'--','lean/PEqualNP/Outside/',allow_empty=True).decode().split('\0')
    paths=[x.split(':',1)[1] for x in paths if x and ':' in x]
    print('[REV]',rev,'[MATCHES]',len(paths),flush=True)
    records=[]; skipped=[]
    with subprocess.Popen(['git','-C',str(a.repo),'cat-file','--batch'],stdin=subprocess.PIPE,stdout=subprocess.PIPE) as proc:
        for i,path in enumerate(paths,1):
            proc.stdin.write((rev+':'+path+'\n').encode()); proc.stdin.flush()
            header=proc.stdout.readline().split()
            if len(header)!=3 or header[1]!=b'blob': raise RuntimeError(f'Unexpected cat-file header {header!r}')
            size=int(header[2]); data=proc.stdout.read(size)
            if len(data)!=size or proc.stdout.read(1)!=b'\n': raise RuntimeError('Incomplete git blob')
            r=inspect(path,data.decode('utf-8'))
            if r is not None: records.append(r)
            else: skipped.append(path)
            if i%250==0: print(f'[SCAN] {i}/{len(paths)}',flush=True)
        proc.stdin.close()
        if proc.wait(): raise RuntimeError('git cat-file failed')
    graphs=[r for r in records if r['edges'] is not None]
    print('[PARSED]',len(records),'[GRAPH]',len(graphs),'[SKIPPED]',len(skipped))
    for (n,pol),count in sorted(collections.Counter((r['n'],r['polarity']) for r in graphs).items()): print('[GROUP]',n,pol,count)
    for k,count in collections.Counter(k for r in graphs for k in r['features']).most_common(): print('[FEATURE]',k,count)
    for pol in ('positive','negative'):
        for r in sorted((r for r in graphs if r['polarity']==pol),key=lambda r:r['lines'])[:5]: print('[SHORTEST]',pol,r['lines'],r['path'],','.join(r['features']))
    refs=collections.Counter(k for r in graphs for k in r['references']); print('[COMMON SOURCES]',refs.most_common(10))
    matches={}
    for name,(n,e) in TARGETS.items():
        hits=[r for r in graphs if r['n']==n and isomorphic(n,e,r['edges'])]
        matches[name]=[{'path':r['path'],'polarity':r['polarity'],'lines':r['lines']} for r in hits]
        print('[ISOMORPHIC]',name,json.dumps(matches[name]))
    a.output.parent.mkdir(parents=True,exist_ok=True); a.output.write_text(json.dumps({'revision':rev,'records':records,'skipped':skipped,'isomorphic':matches},ensure_ascii=False,indent=2)+'\n',encoding='utf-8'); print('[JSON]',a.output)
if __name__=='__main__': main()
