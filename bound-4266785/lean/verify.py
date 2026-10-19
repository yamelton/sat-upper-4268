"""Build the source import closure, kernel-check the endpoint, and audit its axioms.

Only source/dependency/object hash-matched checkpoints are reused. Mathlib is
provided by the pinned package cache. --library-only builds the analytic base.
"""
from concurrent.futures import ThreadPoolExecutor,wait,FIRST_COMPLETED
from pathlib import Path
import hashlib,json,os,re,subprocess,sys,time
from run import PATHS,TOOLCHAIN
from audit_helpers import audit_command,parse_audit,ALLOWED_AXIOMS
ROOT=Path(__file__).resolve().parent
RESULTS=ROOT.parent/'results';RESULTS.mkdir(exist_ok=True)
ENV=dict(os.environ,LEAN_PATH=':'.join(str(p.resolve()) for p in PATHS))
CACHE=RESULTS/'build-cache.json';STATUS=RESULTS/'build-status.json'
records=json.loads(CACHE.read_text()) if CACHE.exists() else {}
start=time.monotonic()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def source(m):return ROOT/(m.replace('.','/')+'.lean')
def target(m):return ROOT/'build'/(m.replace('.','/')+'.olean')
def dependencies(m):
 return [x for x in re.findall(r'^import\s+(\S+)',source(m).read_text(),re.M) if x.startswith(('SatUpper','SatKUpper','SatFinal'))]
def closure(roots):
 graph={};pending=list(roots)
 while pending:
  m=pending.pop()
  if m in graph:continue
  graph[m]=dependencies(m);pending.extend(graph[m])
 return graph

def compile_one(m,fingerprint):
 p=target(m);p.parent.mkdir(parents=True,exist_ok=True)
 old=records.get(m,{})
 if old.get('fingerprint')==fingerprint and p.exists() and old.get('object_sha256')==sha(p):return dict(old,reused=True)
 t=time.monotonic();log=RESULTS/(m+'.log')
 with log.open('w') as stream:
  result=subprocess.run([str(TOOLCHAIN/'bin/lean'),'--profile','-o',str(p),str(source(m))],cwd=ROOT,env=ENV,stdout=stream,stderr=subprocess.STDOUT)
 output=log.read_text()
 if result.returncode or "declaration uses 'sorry'" in output:raise RuntimeError(m+' failed:\n'+output)
 return dict(fingerprint=fingerprint,source_sha256=sha(source(m)),object_sha256=sha(p),seconds=round(time.monotonic()-t,3))

def build(roots):
 graph=closure(roots);pending=set(graph);done={};active={};failed=[]
 pin=sha(ROOT/'lean-toolchain')+sha(ROOT/'lake-manifest.json')
 workers=int(os.environ.get('SAT_BUILD_WORKERS','1'))
 def save(status):
  CACHE.write_text(json.dumps(records,indent=2)+'\n')
  STATUS.write_text(json.dumps(dict(status=status,completed=len(done),total=len(graph),active=list(active.values()),failed=failed,elapsed_seconds=round(time.monotonic()-start,1)),indent=2)+'\n')
 with ThreadPoolExecutor(max_workers=workers) as pool:
  while pending or active:
   for m in sorted(pending):
    if len(active)>=workers:break
    if not all(d in done for d in graph[m]):continue
    fingerprint=hashlib.sha256((sha(source(m))+pin+''.join(done[d] for d in graph[m])).encode()).hexdigest()
    active[pool.submit(compile_one,m,fingerprint)]=m;pending.remove(m)
   save('building')
   if not active:raise RuntimeError('Dependency cycle')
   finished,_=wait(active,return_when=FIRST_COMPLETED)
   for task in finished:
    m=active.pop(task)
    try:r=task.result()
    except Exception:
     failed.append(m);save('failed');raise
    records[m]=r;done[m]=r['object_sha256'];print('REUSED' if r.get('reused') else 'CHECKED',m,r.get('seconds'),flush=True)
  save('built')
 return graph

def audit(graph):
 roots=['SatFinal.Numerics.upperBound_4266785','SatFinal.satisfiabilityProbability_tendsto_zero']
 # All new theorem declarations and all dependency theorems reachable from them
 # are covered by Lean's transitive axiom collector.
 for m in graph:
  if not m.startswith('SatFinal.'):continue
  s=source(m).read_text();ns=re.findall(r'^namespace\s+(\S+)\s*$',s,re.M)
  if len(ns)!=1:raise RuntimeError('Unexpected namespaces: '+m)
  roots.extend(ns[0]+'.'+n for n in re.findall(r'^theorem\s+(\w+)',s,re.M))
 roots=sorted(set(roots))
 p=ROOT/'AxiomAudit.lean'
 p.write_text('import SatFinal.Endpoint\nimport Lean.Util.CollectAxioms\n'+audit_command(roots)+
  'example : Filter.Tendsto (fun n : ℕ => SatKUpper.Model.satisfiabilityProbability 3 n (853357*n/200000)) Filter.atTop (nhds 0) := SatFinal.satisfiabilityProbability_tendsto_zero\n')
 r=subprocess.run([str(TOOLCHAIN/'bin/lean'),str(p)],cwd=ROOT,env=ENV,text=True,capture_output=True)
 output=r.stdout+r.stderr;(RESULTS/'axiom-audit.txt').write_text(output)
 if r.returncode or "declaration uses 'sorry'" in output:raise RuntimeError(output)
 names,axioms=parse_audit(output,roots)
 report=dict(build_passed=True,density='853357/200000',T=192,H=512,certificate_method='polynomial logarithm minorant with a square derivative identity',audited_theorems=names,axiom_union=sorted(axioms),allowed_axioms=sorted(ALLOWED_AXIOMS),
  source_sha256={str(source(m).relative_to(ROOT)):sha(source(m)) for m in graph},
  object_sha256={str(target(m).relative_to(ROOT)):sha(target(m)) for m in graph},
  toolchain=(ROOT/'lean-toolchain').read_text().strip(),manifest_sha256=sha(ROOT/'lake-manifest.json'),elapsed_seconds=time.monotonic()-start)
 (RESULTS/'lean-verification.json').write_text(json.dumps(report,indent=2)+'\n')
 STATUS.write_text(json.dumps(dict(status='passed',completed=len(graph),total=len(graph),active=[],failed=[]),indent=2)+'\n')
 print('Full endpoint kernel checked and axiom audited.',flush=True)

if __name__=='__main__':
 library='--library-only' in sys.argv
 graph=build(['SatFinal.Quadratic','SatKUpper.Numerics.TransformBlocks'] if library else ['SatFinal.Endpoint'])
 if not library:audit(graph)
