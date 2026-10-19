import os, subprocess, sys, shutil
from pathlib import Path
ROOT=Path(__file__).resolve().parent
PIN=(ROOT/'lean-toolchain').read_text().strip()
TOOLCHAIN=ROOT.parent/'.tools/elan/toolchains'/PIN.replace('/','--').replace(':','---')
if not (TOOLCHAIN/'bin/lean').is_file():
 if shutil.which('elan'):
  LEAN=Path(subprocess.check_output(['elan','which','lean'],cwd=ROOT,text=True).strip())
  TOOLCHAIN=LEAN.parent.parent
 else:
  raise RuntimeError('Install the pinned Lean toolchain with elan; see README.md')
PATHS=[ROOT/'build']+[p/'.lake/build/lib/lean' for p in (ROOT/'.lake/packages').iterdir() if p.is_dir()]+[TOOLCHAIN/'lib/lean']
def run(*args):
 return subprocess.run([str(TOOLCHAIN/'bin/lean'),*args],env=dict(os.environ,LEAN_PATH=':'.join(str(p.resolve()) for p in PATHS)),text=True,capture_output=True,cwd=ROOT)
if __name__=='__main__':
 r=run(*sys.argv[1:]);print(r.stdout,end='');print(r.stderr,end='',file=sys.stderr);raise SystemExit(r.returncode)
