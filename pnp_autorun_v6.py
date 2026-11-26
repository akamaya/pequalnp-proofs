#!/usr/bin/env python3
"""P=NP serial worker: one task or continuous loop; official lease, solver, check/submit.
WSL/Linux; existing solver scripts and official pnp_current.sh required.
"""
import argparse, datetime, fcntl, hashlib, json, os, re, shutil, signal, subprocess, sys, threading, time
from pathlib import Path

UP='open-goat/pequalnp-proofs'
HOME=Path.home()/'dev/LeanDojo-v2'
ID=re.compile(r'L-meta-\d+\Z')
OTHER_ID=re.compile(r'L-[a-z]+-\d+\Z')
REL=re.compile(r'lean/PEqualNP/Outside/[A-Za-z0-9_]+\.lean\Z')
KNOWN={'lean/ExtractData.lean'}
class Stop(Exception): pass

def say(*x): print(*x,flush=True)
def norm(s): return re.sub(r'\s+','',s)
def closed_race(rc,txt):
    return rc==3 and bool(re.search(r'^stopped: this step is no longer open \(pr_open\)\.',txt,re.M))

def release_confirmed(rc,txt,gid):
    # Official release uses curl without -f: exit zero alone is not enough.
    if rc:return False
    try:d=json.loads(txt)
    except (ValueError,TypeError):return False
    return isinstance(d,dict) and d.get('released')==gid and not d.get('error')

def is_skeleton(s): return bool(re.search(r':=\s*by\s+sorry\s*\Z',s)) and s.count('sorry')==1

def declaration(text,module):
    pat=r'^theorem\s+'+re.escape(module)+r'\s*:\s*(.*?)\s*:=\s*by\b'
    m=list(re.finditer(pat,text,re.M|re.S))
    if len(m)!=1: raise Stop('target theorem missing or duplicated')
    return m[0][1].strip()

def validate_statement(text,gap):
    actual=norm(declaration(text,gap['module'])); expected=norm(gap['statement'])
    if actual not in (expected,'('+expected+')'): raise Stop('STATEMENT MISMATCH against official lease')

def graph_input(text,module):
    # The existing graph parser expects a bare forall; the desk wraps its term.
    term=declaration(text,module)
    if term.startswith('(') and term.endswith(')') and term[1:-1].lstrip().startswith('∀'):
        return replace_statement(text,module,term[1:-1].strip())
    return text

def replace_statement(text,module,term):
    pattern=r'(^theorem\s+'+re.escape(module)+r'\s*:\s*)(.*?)(\s*:=\s*by\b)'
    result,n=re.subn(pattern,lambda m:m[1]+term+m[3],text,flags=re.M|re.S)
    if n!=1:raise Stop('cannot replace target declaration')
    return result

def clean_generated(text):
    # The graph solver used these global options for experiments. The desk forbids them.
    return re.sub(r'^set_option (?:maxRecDepth|exponentiation\.threshold) \d+[ \t]*\n','',text,flags=re.M)

def remote_is(url,owner):
    name=re.escape(owner)+r'/pequalnp-proofs(?:\.git)?/?'
    return bool(re.fullmatch(r'(?:https://github\.com/|git@github\.com:|ssh://git@github\.com/)'+name,url,re.I))

def positive_input(original,module,twin):
    """Only the exact table solver's positive syntax is supported; no arbitrary negation rewrite."""
    import pnp_table_solve_v2 as table
    term=declaration(original,module).strip()
    if term.startswith('(') and term.endswith(')'):term=term[1:-1].strip()
    if not term.startswith('¬'):raise ValueError('not a negative table statement')
    inner=term[1:].strip()
    if not (inner.startswith('(') and inner.endswith(')')):raise ValueError('unsupported negation syntax')
    inner=inner[1:-1].strip()
    target='PEqualNP.Outside.'+twin.replace('-','_')
    text='import Mathlib\nimport PEqualNP.Defs\n\ntheorem '+target+' : ('+inner+') := by\n  sorry\n'
    table.parse(text)  # requires exact supported positive type, six essential inputs and monotonicity
    return text

class Run:
    def __init__(self,a):
        self.a=a; self.repo=a.repo.resolve(); self.tools=a.tools.resolve(); self.script=self.tools/'pnp_current.sh'
        self.root=self.tools/'proof-logs/autorun-v6'; self.root.mkdir(parents=True,exist_ok=True)
        self.out=self.root/(datetime.datetime.now().strftime('%Y%m%d-%H%M%S')+'-'+str(time.time_ns()%10**9).zfill(9)); self.out.mkdir()
        self.id=None; self.gap=None; self.request_lock=threading.Lock(); self.last_request=0.0; self.twin_hint=None; self.heartbeat=None; self.hstop=threading.Event(); self.hfail=threading.Event(); self.lease_new=False; self.pr=None
        self.report={'status':'START','directory':str(self.out)}; self.save()
    def save(self,**kw):
        self.report.update(kw); p=self.out/'run.json'; tmp=p.with_suffix('.tmp'); tmp.write_text(json.dumps(self.report,indent=2,ensure_ascii=False)+'\n'); tmp.replace(p)
    def capture(self,cmd,ok=True,timeout=60):
        p=subprocess.run(cmd,cwd=self.repo,stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True,timeout=timeout)
        if ok and p.returncode: raise Stop(f'{cmd[0]} failed: {p.stderr.strip()[-1200:]}')
        return p
    def git(self,*args,ok=True):return self.capture(['git',*args],ok=ok)
    def gitout(self,*args):return self.git(*args).stdout.strip()
    def status(self):
        raw=self.git('status','--porcelain=v1','-z','--untracked-files=all','--no-renames').stdout
        return [(s[:2],s[3:]) for s in raw.split('\0') if s]
    def tracked(self,rel): return bool(self.gitout('ls-files','--',rel))
    def file(self,rel):
        p=self.repo/rel
        if p.is_symlink() or p.resolve()!=p or not p.is_file(): raise Stop(f'not a regular repo file: {rel}')
        return p
    def archive(self,rel):
        if self.tracked(rel):raise Stop(f'will not move tracked file: {rel}')
        src=self.file(rel); dst=self.out/'archived'/rel; dst.parent.mkdir(parents=True,exist_ok=True)
        if dst.exists():raise Stop(f'archive collision: {dst}')
        shutil.move(str(src),str(dst)); say('[ARCHIVE]',rel,'->',dst)
    def clean(self,target=None):
        unknown=[]; moves=[]
        for code,rel in self.status():
            if rel.startswith('.pnp/') and code=='??': continue
            if rel==target:
                if code=='??' or (self.a.resume and code=='A '):continue
                raise Stop(f'target unexpectedly modified/tracked: {code} {rel}')
            if code=='??' and (rel in KNOWN or self.a.archive_untracked): moves.append(rel)
            else: unknown.append((code,rel))
        if unknown:raise Stop('other changes; nothing moved. Review:\n'+'\n'.join(f'{c} {r}' for c,r in unknown)+'\nUse --archive-untracked only for untracked files you intend to move; tracked changes are never moved.')
        for rel in moves:self.archive(rel)
    def preflight(self):
        if not self.repo.is_dir() or self.gitout('rev-parse','--show-toplevel')!=str(self.repo):raise Stop('not repository root')
        if self.root.resolve().is_relative_to(self.repo):raise Stop('logs must be outside repository')
        for cmd in ('git','gh','lake','bash','curl'):
            if not shutil.which(cmd):raise Stop(f'missing command {cmd}')
        for f in ('pnp_current.sh','pnp_table_solve_v2.py','pnp_graph_solve_v1.py','pnp_graph_support_v1.py','pnp_graph_binary_v3.py','pnp_graph_binary_width_v1.py','pnp_graph_binary_pairs_v1.py','pnp_graph_certificate_v3.py'):
            if not (self.tools/f).is_file():raise Stop(f'missing {self.tools/f}')
        if os.environ.get('PNP_DESK'):raise Stop('PNP_DESK override is set; refusing live submission')
        self.owner=self.capture(['gh','api','user','--jq','.login']).stdout.strip()
        if not re.fullmatch(r'[A-Za-z0-9-]+',self.owner):raise Stop('invalid GitHub login')
        d=json.loads(self.capture(['gh','api',f'repos/{self.owner}/pequalnp-proofs']).stdout)
        if d.get('full_name','').lower()!=f'{self.owner}/pequalnp-proofs'.lower() or not d.get('fork') or d.get('parent',{}).get('full_name','').lower()!=UP.lower():raise Stop('GitHub repository is not the expected fork')
        origin=self.gitout('remote','get-url','origin'); push=self.gitout('remote','get-url','--push','--all','origin').splitlines()
        if not remote_is(origin,self.owner) or not push or not all(remote_is(x,self.owner) for x in push):
            if origin=='/mnt/c/dev/pequalnp-proofs' and push==[origin] and 'windows-local' not in self.gitout('remote').splitlines():
                self.git('remote','rename','origin','windows-local'); self.git('remote','add','origin',f'https://github.com/{self.owner}/pequalnp-proofs.git');say('[GIT] repaired origin; old remote saved as windows-local')
            else:raise Stop('unexpected origin/push URL; inspect git remote -v (no automatic change)')
        if not self.git('var','GIT_AUTHOR_IDENT',ok=False).returncode==0 or not self.git('var','GIT_COMMITTER_IDENT',ok=False).returncode==0:
            u=json.loads(self.capture(['gh','api','user']).stdout)
            for k,v in [('user.name',self.owner),('user.email',f'{u["id"]}+{self.owner}@users.noreply.github.com')]:
                if not self.git('config','--get',k,ok=False).stdout.strip():self.git('config','--local',k,v)
            self.git('var','GIT_AUTHOR_IDENT');self.git('var','GIT_COMMITTER_IDENT');say('[GIT] missing identity configured locally')
        branch=self.gitout('branch','--show-current')
        if branch!='main' and not OTHER_ID.fullmatch(branch):raise Stop(f'unexpected branch: {branch}')
        if self.a.resume and branch not in ('main',self.a.resume):raise Stop('resume requires main or its own task branch')
        if not self.a.resume:
            self.clean()
            if branch!='main':self.git('checkout','main');say('[GIT] switched to main; previous task branch retained')
        # Official main is fetched but never merged/rebased into the working tree.
        self.capture(['git','fetch','-q','https://github.com/'+UP+'.git','main'],timeout=180)
        self.upsha=self.gitout('rev-parse','FETCH_HEAD');
        if self.git('cat-file','-e',f'{self.upsha}:STOP',ok=False).returncode==0:raise Stop('official STOP notice on main')
        base=self.gitout('merge-base',self.upsha,'main')
        if self.gitout('diff','--name-status',base,'main'):raise Stop('local main contains changes not on upstream main; refusing to acquire or submit')
        say('[READY]',self.owner,'logs=',self.out)
    def run(self,cmd,label,timeout=None,mem=None,solver=False):
        """Log all output, show concise progress. Official children share a process group."""
        import pnp_graph_certificate_v3 as guard
        log=self.out/(label+'.log'); t=time.monotonic(); peak=0; why=''; next_report=30; read_at=0; pending=''
        def drain():
            nonlocal read_at,pending
            if not solver:return
            with log.open('r',encoding='utf-8',errors='replace') as reader:
                reader.seek(read_at);pending+=reader.read();read_at=reader.tell()
            lines=pending.split('\n');pending=lines.pop()
            for line in lines:
                if line.startswith(('[' ,'SOLVED','SELF TEST')):say(line)
        with log.open('wb') as f:
            p=subprocess.Popen(cmd,cwd=self.repo,stdout=f,stderr=subprocess.STDOUT,start_new_session=True)
            try:
                while p.poll() is None:
                    drain();elapsed=time.monotonic()-t; rss,_=guard.group_rss(p.pid);peak=max(peak,rss)
                    if self.hfail.is_set():why='LEASE heartbeat failed';break
                    if timeout and elapsed>=timeout:why='TIMEOUT';break
                    if mem and rss>mem*1024**3:why='RSS_LIMIT';break
                    if elapsed>=next_report:say('[WAIT]',label,f'{elapsed:.0f}s '+('solver wrapper (Lean RSS shown in RUN)' if solver else f'RSS={rss/1024**3:.2f} GiB'));next_report=elapsed+30
                    time.sleep(.25)
            except BaseException:
                why='INTERRUPTED';raise
            finally:
                if p.poll() is None or guard.group_rss(p.pid)[1]:
                    if solver and p.poll() is None:
                        # Solver's internal guard owns a separate Lean session. Let its finally block run.
                        try: os.kill(p.pid,signal.SIGINT);p.wait(timeout=15)
                        except (ProcessLookupError,subprocess.TimeoutExpired):pass
                    guard.terminate_group(p)
        drain();txt=log.read_text(encoding='utf-8',errors='replace')
        if solver:
            if p.returncode:say('[SOLVER FAILED] see full log:',log)
        elif label in ('next','submit','release','next-counterpart','release-negative','release-race'):say(txt.rstrip())
        else:
            useful=[l for l in txt.splitlines() if re.search(r'error:|REFUSED|stopped:|not built|not submitted|Build completed|it builds\.|^\[CHECK\]',l,re.I)]
            for l in useful[-25:]:say(l)
            if p.returncode and not useful:say(txt[-3000:])
        say('[END]',label,'rc=',p.returncode,'seconds=',round(time.monotonic()-t,2),'log=',log)
        if why:raise Stop(f'{label}: {why}; see {log}')
        return p.returncode,txt
    def pace(self):
        # Space wrapper-level official commands; never patch official internal calls.
        with self.request_lock:
            delay=5-(time.monotonic()-self.last_request)
            if delay>0:time.sleep(delay)
            self.last_request=time.monotonic()
    def official(self,*args,label=None,**kw):
        self.pace()
        return self.run(['bash',str(self.script),*args],label or args[0],**kw)
    def load_gap(self):
        d=json.loads((self.repo/'.pnp'/f'{self.id}.json').read_text());g=d['gap']
        if g.get('id')!=self.id or not REL.fullmatch(g.get('file','')) or g.get('module')!=g['file'][5:-5].replace('/','.') or not isinstance(g.get('statement'),str):raise Stop('unexpected official lease data')
        if not d.get('lease',{}).get('id'):raise Stop('missing lease')
        self.gap=g;return g
    def beat_once(self):
        self.pace()
        p=self.capture(['bash',str(self.script),'beat',self.id],ok=False,timeout=90)
        txt=(p.stdout+'\n'+p.stderr).strip();say('[BEAT]',txt[-1000:])
        if p.returncode or not re.search(r'lease until\s+\d',txt):raise Stop('lease renewal failed')
    def start_beat(self):
        self.beat_once()
        def worker():
            while not self.hstop.wait(240):
                try:self.beat_once()
                except Exception as e:say('[LEASE STOP]',e);self.hfail.set();return
        self.heartbeat=threading.Thread(target=worker,daemon=True);self.heartbeat.start()
    def stop_beat(self):
        self.hstop.set()
        if self.heartbeat:self.heartbeat.join()
    def acquire(self):
        if self.a.resume:self.id=self.a.resume
        else:
            rc,txt=self.official('next',*(() if getattr(self.a,'loop',False) else ('--another',)),'--level',self.a.level,'--kind','prove',timeout=180)
            if rc:raise Stop('official next failed')
            m=re.search(r'^STEP\s+(L-[a-z]+-\d+)\s+-',txt,re.M)
            if not m:
                d=json.loads((self.repo/'.pnp/.last.json').read_text())
                if not isinstance(d,dict) or 'gap' not in d or d['gap'] is not None or d.get('error'):
                    raise Stop('unexpected next response; inspect next.log and .pnp/.last.json')
                self.save(status='NO_TASK');say('[NO TASK]');return False
            self.id=m[1];self.lease_new=True
            hints=set(re.findall(r'positive statement (L-meta-\d+)',txt))
            if len(hints)==1:self.twin_hint=hints.pop()
        self.save(step=self.id,initial_step=self.id,status='LEASED');self.load_gap();return True
    def release_unsolved(self,reason):
        say('[UNSOLVED]',reason);self.save(status='UNSOLVED',reason=reason)
        self.stop_beat()
        if self.a.release_unsolved and (self.lease_new or self.a.resume==self.id) and not self.hfail.is_set():
            rel=self.gap['file']; path=self.file(rel); data=path.read_bytes()
            if self.tracked(rel) or not is_skeleton(data.decode('utf-8')):raise Stop('unsolved file not an untouched skeleton')
            rc,txt=self.official('release',self.id,'other',timeout=60)
            if not release_confirmed(rc,txt,self.id):raise Stop('release not confirmed; skeleton retained')
            if self.tracked(rel) or path.read_bytes()!=data:raise Stop('skeleton changed during release')
            self.archive(rel);self.save(released=True);say('[RELEASE CONFIRMED]')
        return 2
    def retire_race(self,where):
        """Preserve verified proof; stop requesting a task already in PR review."""
        self.stop_beat()
        rel=self.gap['file']; path=self.file(rel)
        data=path.read_bytes(); validate_statement(data.decode('utf-8'),self.gap)
        if is_skeleton(data.decode('utf-8')):raise Stop('race retirement requires a proof, not skeleton')
        backup=self.out/'race-proof.lean'; backup.write_bytes(data)
        self.save(status='RACE_LOST',proof=str(backup),race_stage=where)
        # A closed task may reject release. Preserve the proof and report either outcome.
        try:
            rc,txt=self.official('release',self.id,'other',label='release-race',timeout=60)
            released=release_confirmed(rc,txt,self.id)
        except Exception as e:
            say('[RELEASE WARNING]',e);released=False
        if path.read_bytes()!=data:raise Stop('proof changed during retirement; not moving')
        if not self.tracked(rel):self.archive(rel)
        else:say('[GIT] committed proof retained on task branch')
        self.save(status='RACE_LOST',released=released)
        say('[RACE LOST] proof saved:',backup,'; lease release:', 'OK' if released else 'unconfirmed')
        return 2

    def desk_state(self,gid,phase):
        """Read-only official desk state. Unknown/unreachable is never treated as open."""
        if not ID.fullmatch(gid):raise Stop('invalid counterpart ID for desk query')
        state='unknown'; detail=''; raw=''
        try:
            self.pace()
            p=self.capture(['curl','--proto','=https','-fsS','-m','10','-G','https://pequalnp.com/desk/step','--data-urlencode','gap='+gid],ok=False,timeout=15)
            raw=p.stdout
            if p.returncode:detail='curl exit '+str(p.returncode)
            else:
                d=json.loads(raw)
                if isinstance(d,dict) and isinstance(d.get('state'),str) and re.fullmatch(r'[a-z_]{1,40}',d['state']):
                    state=d['state']
                else:detail='missing or invalid state'
        except (OSError,ValueError,subprocess.TimeoutExpired) as e:detail=type(e).__name__
        (self.out/('desk-'+phase+'.json')).write_text(json.dumps({'gap':gid,'state':state,'detail':detail,'response':raw[:16000]},ensure_ascii=False,indent=2)+'\n')
        say('[DESK]',gid,'state='+state,'phase='+phase,detail)
        self.save(**{'desk_'+phase.replace('-','_'):state})
        return state

    def skip_counterpart(self,twin,state,phase,verified=False):
        # Busy does not prove the negative false. Release with other unless we have a checked proof.
        say('[SKIP COUNTERPART]',twin,'state='+state,'phase='+phase)
        self.stop_beat()
        if self.hfail.is_set():raise Stop('negative lease lost; not releasing')
        rel=self.gap['file'];path=self.file(rel)
        data=path.read_bytes();validate_statement(data.decode('utf-8'),self.gap)
        if self.tracked(rel) or not is_skeleton(data.decode('utf-8')):raise Stop('negative skeleton changed; not releasing')
        reason='statement_seems_false' if verified else 'other'
        self.save(status='COUNTERPART_SKIPPED',counterpart=twin,skip_state=state,skip_phase=phase)
        # Respect --release-unsolved; otherwise keep the negative lease and file for explicit resume.
        if not self.a.release_unsolved:
            say('[KEPT] negative lease/skeleton retained; use --release-unsolved to release automatically')
            return 2
        rc,txt=self.official('release',self.id,reason,label='release-negative',timeout=60)
        if not release_confirmed(rc,txt,self.id):raise Stop('negative release not confirmed; skeleton retained')
        if self.tracked(rel) or path.read_bytes()!=data:raise Stop('negative skeleton changed; not archiving')
        self.archive(rel);self.save(status='COUNTERPART_SKIPPED',released=True,release_reason=reason)
        return 2

    def attempt_counterpart(self,path,original):
        if self.a.no_counterpart:return self.release_unsolved('negative/unsupported statement')
        twin=self.a.counterpart or self.twin_hint
        if not twin or twin==self.id or not ID.fullmatch(twin):
            return self.release_unsolved('no confirmed positive counterpart ID; use --resume ID --counterpart ID')
        try: text=positive_input(original,self.gap['module'],twin)
        except ValueError:return self.release_unsolved('unsupported statement (positive/negative six-input table or positive graph only)')
        neg=self.id; rel=self.gap['file']; stem=twin.replace('-','_'); module='PEqualNP.Outside.'+stem
        if twin in getattr(self.a,'seen',set()):return self.skip_counterpart(twin,'already_attempted','before-solve')
        state=self.desk_state(twin,'before-solve')
        if state!='open':return self.skip_counterpart(twin,state,'before-solve')
        src=self.out/(stem+'.counterpart.input.lean');src.write_text(text)
        say('[COUNTERPART]',neg,'->',twin,'local proof before requesting positive task')
        self.save(counterpart=twin,negative=neg,status='COUNTERPART_SEARCH')
        rc,txt=self.run([sys.executable,'-u',str(self.tools/'pnp_table_solve_v2.py'),'--source',str(src),'--repo',str(self.repo),'--out',str(self.out/'counterpart-solver'),'--widths','128','256','512','--check','--timeout',str(self.a.timeout),'--max-rss-gib',str(self.a.max_rss_gib),'--jobs',str(self.a.jobs)],'solve-counterpart',solver=True)
        if rc:return self.release_unsolved(f'counterpart solver exit {rc}; no refutation certified')
        matches=re.findall(r'^\[VERIFIED\]\s+(.+)$',txt,re.M)
        if len(matches)!=1:raise Stop('counterpart solver did not identify exactly one verified artifact')
        verified=Path(matches[0]).resolve()
        if not verified.is_relative_to(self.out/'counterpart-solver') or verified.name!=stem+'.verified.lean':raise Stop('unexpected counterpart artifact path')
        raw=verified.read_text()
        if norm(declaration(raw,module))!=norm(declaration(text,module)):raise Stop('counterpart local statement mismatch')
        self.save(status='COUNTERPART_VERIFIED',counterpart_proof=str(verified));say('[COUNTERPART VERIFIED]',twin)
        state=self.desk_state(twin,'after-solve')
        if state!='open':return self.skip_counterpart(twin,state,'after-solve',verified=True)
        if self.hfail.is_set() or path.read_text()!=original or self.tracked(rel):raise Stop('negative lease/file changed; not releasing')
        self.stop_beat()
        if self.hfail.is_set():raise Stop('negative lease renewal failed')
        rc,txt=self.official('release',neg,'statement_seems_false',label='release-negative',timeout=60)
        if not release_confirmed(rc,txt,neg):raise Stop('negative release not confirmed; local positive proof retained')
        if path.read_text()!=original or self.tracked(rel):raise Stop('negative skeleton changed; not archiving')
        self.archive(rel)
        # No claim is requested until the exact positive theorem has passed Lean locally.
        rc,txt=self.official('next','--proof-of',twin,label='next-counterpart',timeout=180)
        if rc:raise Stop('positive task unavailable; verified counterpart retained')
        m=re.search(r'^STEP\s+(L-[a-z]+-\d+)\s+-',txt,re.M)
        if not m or m[1]!=twin:raise Stop('desk did not assign requested counterpart; no file installed')
        self.id=twin; self.lease_new=True; self.load_gap();self.save(step=twin,status='LEASED_COUNTERPART')
        self.heartbeat=None;self.hstop=threading.Event();self.hfail=threading.Event()
        return self.solve(prepared=raw)

    def solve(self,prepared=None):
        g=self.gap;rel=g['file'];path=self.file(rel);stem=path.stem
        if self.git('cat-file','-e',f'{self.upsha}:{rel}',ok=False).returncode==0 or self.git('cat-file','-e',f'main:{rel}',ok=False).returncode==0:raise Stop('file already on main; never edit a recorded proof')
        self.clean(rel);original=path.read_text();validate_statement(original,g)
        self.start_beat()
        if prepared is not None:
            if not is_skeleton(original) or self.tracked(rel):raise Stop('counterpart target is not an untouched new skeleton')
            validate_statement(prepared,g)
            candidate=replace_statement(clean_generated(prepared),g['module'],declaration(original,g['module']))
            must_check=candidate!=prepared
        elif not is_skeleton(original):
            if not self.a.resume:raise Stop('existing proof found; use --resume to recheck it without overwriting')
            candidate=original; must_check=True
        else:
            if not ID.fullmatch(self.id):return self.release_unsolved('unsupported task family')
            import pnp_table_solve_v2 as table
            import pnp_graph_solve_v1 as graph
            solver_source=path
            try:table.parse(original);method='table'
            except ValueError:
                try:
                    normalized=graph_input(original,g['module']);graph.get_statement(normalized);method='graph'
                    solver_source=self.out/(stem+'.input.lean');solver_source.write_text(normalized)
                except ValueError:return self.attempt_counterpart(path,original)
            solver=self.tools/('pnp_table_solve_v2.py' if method=='table' else 'pnp_graph_solve_v1.py')
            self.save(method=method);say('[SOLVER]',method)
            rc,txt=self.run([sys.executable,'-u',str(solver),'--source',str(solver_source),'--repo',str(self.repo),'--out',str(self.out/'solver'),'--widths','128','256','512','--check','--timeout',str(self.a.timeout),'--max-rss-gib',str(self.a.max_rss_gib),'--jobs',str(self.a.jobs)],'solve-'+method,solver=True)
            if rc:return self.release_unsolved(f'solver exit {rc}; not a refutation')
            matches=re.findall(r'^\[VERIFIED\]\s+(.+)$',txt,re.M)
            if len(matches)!=1:raise Stop('solver did not identify exactly one verified artifact')
            verified=Path(matches[0]).resolve()
            if not verified.is_relative_to(self.out/'solver') or verified.name!=stem+'.verified.lean':raise Stop('unexpected solver artifact path')
            raw=verified.read_text();validate_statement(raw,g);candidate=clean_generated(raw)
            if method=='graph':candidate=replace_statement(candidate,g['module'],declaration(original,g['module']))
            must_check=candidate!=raw
        validate_statement(candidate,g)
        if must_check:
            import pnp_graph_certificate_v3 as guard
            d=self.out/'recheck';d.mkdir(); r=guard.check(self.repo,stem,candidate,d,self.a.timeout,self.a.max_rss_gib,self.a.jobs)
            if not r['lean_ok']:raise Stop('submission-ready proof failed kernel/axiom recheck')
        if self.hfail.is_set():raise Stop('lease lost; not installing')
        if path.read_text()!=original:raise Stop('source changed during solve; not overwriting')
        if is_skeleton(original):
            if self.tracked(rel):raise Stop('skeleton became tracked')
            (self.out/'skeleton.lean').write_text(original);tmp=path.with_name(path.name+'.autorun-tmp');
            if tmp.exists():raise Stop('unexpected temporary file')
            tmp.write_text(candidate);tmp.replace(path);say('[INSTALLED]',rel)
        self.save(status='LOCAL_VERIFIED',proof=str(path));self.clean(rel)
        rc,txt=self.official('check',self.id,timeout=self.a.check_timeout,mem=self.a.max_rss_gib)
        if closed_race(rc,txt):return self.retire_race('check')
        if rc:raise Stop('official check failed; proof retained for --resume')
        validate_statement(path.read_text(),g);self.save(status='OFFICIAL_CHECKED',sha256=hashlib.sha256(path.read_bytes()).hexdigest());self.clean(rel)
        self.stop_beat()
        if self.hfail.is_set():raise Stop('lease renewal failed; not submitting')
        if not self.a.submit:say('[CHECKED] --submit not specified; no PR created');return 0
        rc,txt=self.official('submit',self.id,timeout=180)
        prs=re.findall(r'https://github\.com/open-goat/pequalnp-proofs/pull/\d+',txt)
        if prs:self.pr=prs[-1];self.save(status='PR_CREATED',pr=self.pr);say('[PR]',self.pr)
        if not prs and closed_race(rc,txt):return self.retire_race('submit')
        if rc:raise Stop('official submit failed (PR may already exist); inspect log before retry')
        if not prs:raise Stop('submit returned without PR URL; verify GitHub before retry')
        self.save(status='SUBMITTED',pr=self.pr);say('[SUBMITTED] awaiting server verdict; no points confirmed');return 0

def self_test():
    assert closed_race(3,'stopped: this step is no longer open (pr_open). A pull request')
    assert not closed_race(1,'stopped: this step is no longer open (pr_open).')
    assert not closed_race(3,'error: build failed')
    gap={'module':'PEqualNP.Outside.L_meta_1','statement':'∀ s : ℕ, s = s'};s='theorem PEqualNP.Outside.L_meta_1 : (∀ s : ℕ, s = s) := by\n  sorry\n'
    validate_statement(s,gap);assert declaration(graph_input(s,gap['module']),gap['module'])==gap['statement'];assert is_skeleton(s);assert not is_skeleton(s.replace('sorry','rfl'))
    try:validate_statement(s.replace('s = s','s = 0'),gap)
    except Stop:pass
    else:raise AssertionError('changed statement accepted')
    assert clean_generated('set_option maxRecDepth 60000\nset_option exponentiation.threshold 1024\nset_option maxRecDepth 60000 in\n')=='set_option maxRecDepth 60000 in\n'
    assert remote_is('https://github.com/akamaya/pequalnp-proofs.git','akamaya') and remote_is('git@github.com:akamaya/pequalnp-proofs.git','akamaya') and not remote_is('/mnt/c/dev/pequalnp-proofs','akamaya')
    import pnp_table_solve_v2 as table
    positive=table.PROP
    negative='theorem PEqualNP.Outside.L_meta_2 : (¬ ('+positive+')) := by\n  sorry\n'
    got=positive_input(negative,'PEqualNP.Outside.L_meta_2','L-meta-1')
    assert norm(declaration(got,'PEqualNP.Outside.L_meta_1'))==norm('('+positive+')')
    try:positive_input(negative.replace('Monotone2','Monotone3'),'PEqualNP.Outside.L_meta_2','L-meta-1')
    except ValueError:pass
    else:raise AssertionError('unsupported negation accepted')
    import tempfile
    from types import SimpleNamespace
    with tempfile.TemporaryDirectory() as td:
        home=Path(td);repo=home/'repo';repo.mkdir();tools=home/'tools';tools.mkdir()
        def git(*args):subprocess.run(['git',*args],cwd=repo,check=True,capture_output=True)
        git('init','-q');git('config','user.name','Test');git('config','user.email','test@example.invalid')
        (repo/'tracked.txt').write_text('keep');git('add','tracked.txt');git('commit','-qm','base')
        (repo/'lean').mkdir();(repo/'lean/ExtractData.lean').write_text('data')
        (repo/'unknown.txt').write_text('other')
        a=SimpleNamespace(repo=repo,tools=tools,archive_untracked=False,resume=None);r=Run(a)
        try:r.clean()
        except Stop:pass
        else:raise AssertionError('unknown untracked file did not block')
        assert (repo/'lean/ExtractData.lean').exists() and (repo/'unknown.txt').exists()
        a.archive_untracked=True;(repo/'tracked.txt').write_text('changed')
        try:r.clean()
        except Stop:pass
        else:raise AssertionError('tracked change did not block')
        assert (repo/'unknown.txt').exists();(repo/'tracked.txt').write_text('keep');r.clean()
        assert (r.out/'archived/lean/ExtractData.lean').read_text()=='data' and (r.out/'archived/unknown.txt').read_text()=='other'
        assert not r.status()
        (repo/'lean/ExtractData.lean').write_text('new');a.archive_untracked=False
        r2=Run(a);r2.clean();assert (r2.out/'archived/lean/ExtractData.lean').read_text()=='new'
        rel='lean/PEqualNP/Outside/L_meta_1.lean'; target=repo/rel;target.parent.mkdir(parents=True);target.write_text(s.replace('sorry','intro s; rfl'))
        r3=Run(a);r3.id='L-meta-1';r3.gap=dict(gap,file=rel);r3.official=lambda *args,**kw:(0,json.dumps({'released':args[1]}))
        assert r3.retire_race('check')==2 and not target.exists() and (r3.out/'race-proof.lean').exists() and r3.report['released']
        target.write_text(s.replace('sorry','intro s; rfl'));git('add',rel);git('commit','-qm','proof')
        r4=Run(a);r4.id='L-meta-1';r4.gap=dict(gap,file=rel);r4.official=lambda *args,**kw:(1,'closed')
        assert r4.retire_race('submit')==2 and target.exists() and not r4.report['released'] and (r4.out/'race-proof.lean').exists()
        r5=Run(a);r5.pace=lambda:None
        for body,rc,want in [('{"state":"open"}',0,'open'),('{"state":"leased"}',0,'leased'),('{"state":"pr_open"}',0,'pr_open'),('{"state":"proved"}',0,'proved'),('bad json',0,'unknown'),('{}',0,'unknown'),('{"state":"open"}',22,'unknown')]:
            r5.capture=lambda *args,**kw:SimpleNamespace(stdout=body,returncode=rc)
            assert r5.desk_state('L-meta-1','test')==want
        def timeout(*args,**kw):raise subprocess.TimeoutExpired('curl',15)
        r5.capture=timeout;assert r5.desk_state('L-meta-1','test')=='unknown'
        # Use fresh untracked skeleton in the mock repo.
        rel2='lean/PEqualNP/Outside/L_meta_2.lean'; target2=repo/rel2
        target2.write_text(negative);g2={'file':rel2,'module':'PEqualNP.Outside.L_meta_2','statement':'¬ ('+positive+')'}
        a.release_unsolved=False;r6=Run(a);r6.id='L-meta-2';r6.gap=g2
        r6.official=lambda *args,**kw: (_ for _ in ()).throw(AssertionError('unexpected release'))
        assert r6.skip_counterpart('L-meta-1','leased','before-solve')==2 and target2.exists()
        a.release_unsolved=True;r7=Run(a);r7.id='L-meta-2';r7.gap=g2;calls=[]
        r7.official=lambda *args,**kw:(calls.append(args) or (0,json.dumps({'released':args[1]})))
        assert r7.skip_counterpart('L-meta-1','pr_open','before-solve')==2 and not target2.exists()
        assert calls==[('release','L-meta-2','other')]
        target2.write_text(negative);r8=Run(a);r8.id='L-meta-2';r8.gap=g2;calls=[]
        r8.official=lambda *args,**kw:(calls.append(args) or (0,json.dumps({'released':args[1]})))
        assert r8.skip_counterpart('L-meta-1','leased','after-solve',verified=True)==2 and not target2.exists()
        assert calls==[('release','L-meta-2','statement_seems_false')]
        rc,txt=r.run([sys.executable,'-c','print("it builds.")'],'mock-check',timeout=5,mem=1)
        assert rc==0 and 'it builds.' in txt
        try:r.run([sys.executable,'-c','import time; time.sleep(10)'],'mock-timeout',timeout=.2,mem=1)
        except Stop as e:assert 'TIMEOUT' in str(e)
        else:raise AssertionError('timeout not caught')
    say('SELF TEST OK (offline; no GitHub, no Lean)')

def next_action(report,rc):
    status=report.get('status')
    if rc==0 and status=='SUBMITTED':return 'continue'
    if rc==2 and status=='NO_TASK':return 'idle'
    if rc==2 and status in ('UNSOLVED','RACE_LOST','COUNTERPART_SKIPPED') and report.get('released') is True:
        if report.get('skip_state')=='unknown':return 'stop'
        return 'continue'
    return 'stop'

def one(a):
    r=Run(a);rc=1
    try:
        r.preflight()
        if not r.acquire():rc=2
        elif r.id in getattr(a,'seen',set()):
            # Do not retry or blindly release a possibly stale lease. Preserve its file for inspection.
            raise Stop('duplicate step within this session; no solve or submit; inspect lease before restart')
        else:rc=r.solve()
    except KeyboardInterrupt:
        say('[STOP] interrupted; current files and lease metadata retained');r.save(status='PR_CREATED_NEEDS_REVIEW' if r.pr else 'INTERRUPTED');rc=130
    except Exception as e:
        say('[STOP]',str(e) or type(e).__name__);r.save(status='PR_CREATED_NEEDS_REVIEW' if r.pr else 'STOPPED',error=str(e));rc=1
    finally:
        r.stop_beat();say('[LOGS]',r.out)
    return r,rc

def loop(a):
    root=a.tools.resolve()/'proof-logs/autorun-v6';root.mkdir(parents=True,exist_ok=True)
    session=root/('session-'+datetime.datetime.now().strftime('%Y%m%d-%H%M%S')+'-'+str(time.time_ns()%10**9).zfill(9));session.mkdir()
    a.seen=set();started=time.monotonic();counts={};records=[];attempts=0;idle=0
    def summary():
        data={'attempts':attempts,'idle_polls':idle,'elapsed_seconds':round(time.monotonic()-started,2),'counts':counts,'runs':records}
        tmp=session/'summary.tmp';tmp.write_text(json.dumps(data,indent=2,ensure_ascii=False)+'\n');tmp.replace(session/'summary.json')
        say('[TOTAL]', 'attempts='+str(attempts), 'idle='+str(idle), 'elapsed='+str(round(data['elapsed_seconds']))+'s', json.dumps(counts,ensure_ascii=False), 'summary=',session/'summary.json')
    say('[LOOP] serial; Ctrl+C stops; no final verdict polling; logs=',session)
    try:
        while True:
            r,rc=one(a);report=dict(r.report);status=report.get('status','UNKNOWN');action=next_action(report,rc)
            for key in ('initial_step','step'):
                if report.get(key):a.seen.add(report[key])
            if report.get('counterpart') and status in ('SUBMITTED','RACE_LOST'):a.seen.add(report['counterpart'])
            if status=='NO_TASK':idle+=1
            else:attempts+=1
            counts[status]=counts.get(status,0)+1;records.append(dict(report,rc=rc));summary()
            if action=='stop':
                say('[LOOP STOP] result requires review:',status);return 130 if rc==130 else 1
            if a.max_tasks and attempts>=a.max_tasks:say('[LOOP END] max tasks reached');return 0
            if action=='idle' and a.stop_on_empty:say('[LOOP END] no task');return 0
            delay=a.idle_wait if action=='idle' else a.delay
            say('[NEXT IN]',delay,'seconds');time.sleep(delay)
    except KeyboardInterrupt:
        say('[LOOP STOP] interrupted between tasks');return 130
    finally:summary()

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--repo',type=Path,default=Path.home()/'dev/pequalnp-proofs');p.add_argument('--tools',type=Path,default=HOME);p.add_argument('--level',choices=['warmup','solid','hard','open'],default='solid');p.add_argument('--resume');p.add_argument('--counterpart',help='explicit positive twin ID, for a resumed negative lease');p.add_argument('--no-counterpart',action='store_true');p.add_argument('--submit',action='store_true');p.add_argument('--archive-untracked',action='store_true');p.add_argument('--release-unsolved',action='store_true');p.add_argument('--jobs',type=int,default=4);p.add_argument('--timeout',type=int,default=1800);p.add_argument('--check-timeout',type=int,default=1800);p.add_argument('--max-rss-gib',type=float,default=20);p.add_argument('--self-test',action='store_true')
    p.add_argument('--loop',action='store_true',help='serial tasks until stopped; requires --submit --release-unsolved');p.add_argument('--max-tasks',type=int,default=0,help='stop after this many nonempty attempts (0 unlimited)');p.add_argument('--delay',type=int,default=10,help='seconds between attempts (minimum 5)');p.add_argument('--idle-wait',type=int,default=180,help='seconds before retry when no task (minimum 120)');p.add_argument('--stop-on-empty',action='store_true');a=p.parse_args()
    if a.self_test:
        self_test();loop_test();return 0
    if a.resume and not OTHER_ID.fullmatch(a.resume):p.error('invalid resume ID')
    if a.counterpart and (not a.resume or not ID.fullmatch(a.counterpart) or a.no_counterpart):p.error('--counterpart requires --resume and a valid positive ID')
    if min(a.jobs,a.timeout,a.check_timeout,a.max_rss_gib)<=0:p.error('invalid resource limits')
    if a.max_tasks<0 or a.delay<5 or a.idle_wait<120:p.error('invalid loop limit or delay')
    if a.loop and (a.resume or not a.submit or not a.release_unsolved):p.error('--loop requires --submit --release-unsolved and no --resume')
    if not a.loop and (a.max_tasks or a.stop_on_empty):p.error('loop options require --loop')
    lock=a.tools.resolve()/'proof-logs/autorun-v1.lock';lock.parent.mkdir(parents=True,exist_ok=True)
    with lock.open('a') as f:
        try:fcntl.flock(f,fcntl.LOCK_EX|fcntl.LOCK_NB)
        except BlockingIOError:say('[STOP] another autorun is active');return 1
        if a.loop:return loop(a)
        return one(a)[1]

def loop_test():
    import tempfile
    from types import SimpleNamespace
    assert release_confirmed(0,'{"released":"L-meta-1"}','L-meta-1')
    assert not release_confirmed(0,'{"error":"expired"}','L-meta-1')
    assert not release_confirmed(0,'{"released":"L-meta-2"}','L-meta-1')
    assert next_action({'status':'SUBMITTED'},0)=='continue'
    for status in ('UNSOLVED','RACE_LOST','COUNTERPART_SKIPPED'):
        assert next_action({'status':status,'released':True},2)=='continue'
        assert next_action({'status':status,'released':False},2)=='stop'
    assert next_action({'status':'COUNTERPART_SKIPPED','released':True,'skip_state':'unknown'},2)=='stop'
    assert next_action({'status':'NO_TASK'},2)=='idle'
    assert next_action({'status':'PR_CREATED_NEEDS_REVIEW'},1)=='stop'
    # Exercise actual serial controller without network or waiting.
    global one
    real_one=one;real_sleep=time.sleep
    try:
        with tempfile.TemporaryDirectory() as td:
            a=SimpleNamespace(tools=Path(td),max_tasks=3,stop_on_empty=False,delay=10,idle_wait=180)
            states=iter([({'status':'NO_TASK'},2),({'status':'COUNTERPART_SKIPPED','released':True,'initial_step':'L-meta-1'},2),({'status':'SUBMITTED','step':'L-meta-2'},0),({'status':'RACE_LOST','released':True,'step':'L-meta-3'},2)])
            waits=[]
            def fake(a):
                report,rc=next(states);return SimpleNamespace(report=report),rc
            one=fake;time.sleep=lambda sec:waits.append(sec)
            assert loop(a)==0 and waits==[180,10,10] and a.seen=={'L-meta-1','L-meta-2','L-meta-3'}
            q=json.loads(next(Path(td).rglob('summary.json')).read_text());assert q['attempts']==3 and q['idle_polls']==1 and q['counts']['SUBMITTED']==1
            one=lambda a:(SimpleNamespace(report={'status':'RACE_LOST','released':False}),2)
            assert loop(a)==1
    finally:one=real_one;time.sleep=real_sleep
    say('LOOP SELF TEST OK (offline)')

if __name__=='__main__':raise SystemExit(main())
