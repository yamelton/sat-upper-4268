"""Reproduce exact rational certification and an independent C++/MPFR check.

--check-only reuses the existing rational certificate and reruns the native check.
"""
from pathlib import Path
from fractions import Fraction as F
import time,json,hashlib,subprocess,sys,os,shlex,shutil
import certify_quadratic as cert
from fast_exp_v2 import exp_bounds_taylor
ROOT=Path(__file__).resolve().parent
out=ROOT/'quadratic-certificate.json'
start=time.monotonic()
if '--check-only' in sys.argv:
 r=json.loads(out.read_text())
else:
 old=cert.lib.exp_bounds_taylor;checks=[]
 def fast(x,bits):return exp_bounds_taylor(x,bits,minimum_squarings=64)
 for bits in [80,256,1872,5200]:
  for x in [F(0),F(-1,3),F(-853357,200000),-F(853357,200000)*F((1<<10330)-731**4,1<<10330)]:
   a,b=old(x,bits),fast(x,bits)
   assert max(a[0],b[0])<=min(a[1],b[1])
   checks.append(dict(bits=bits,exponent_bits=x.numerator.bit_length(),overlap=True))
 cert.lib.exp_bounds_taylor=fast
 r=cert.exact(5120,512)
 r.update(algebra_checks=cert.audit_moments(),exponential_crosschecks=checks,
          exponential_method='Positive Taylor series, reciprocal, 64 squarings, outward integer rounding',
          status='Exact rational certificate; independent crosscheck pending; not Lean verified')
 out.write_text(json.dumps(r,indent=2))
assert r['certified_negative']
compiler=os.environ.get('CXX') or shutil.which('clang++') or shutil.which('g++')
if not compiler:raise RuntimeError('A C++ compiler is required for the independent MPFR check')
flags=['-lmpfr','-lgmp']
if shutil.which('pkg-config'):
 probe=subprocess.run(['pkg-config','--cflags','--libs','mpfr'],text=True,capture_output=True)
 if probe.returncode==0:flags=shlex.split(probe.stdout)
if Path('/opt/homebrew/include/mpfr.h').exists() and not any(x.startswith('-I') for x in flags):
 flags=['-I/opt/homebrew/include','-L/opt/homebrew/lib']+flags
command=[compiler,'-O3','-std=c++17',str(ROOT/'crosscheck.cpp'),*flags,'-o',str(ROOT/'crosscheck')]
subprocess.run(command,check=True)
result=subprocess.run([str(ROOT/'crosscheck')],check=True,text=True,capture_output=True)
d=json.loads(result.stdout);(ROOT/'mpfr-crosscheck.json').write_text(result.stdout)
assert d['T']==r['T'] and d['H']==r['H']
for lo,hi,key in [('S_lower','S_upper','S_T'),('C_lower','C_upper','C_partial'),('Psi_lower','Psi_upper','Psi_T_lower'),('Psi_lower','Psi_upper','Psi_T_upper')]:
 assert F(r[lo]['exact'])<=F(d[key])<=F(r[hi]['exact']),key
r.update(independent_mpfr_check=d,
 source_sha256={name:hashlib.sha256((ROOT/name).read_bytes()).hexdigest() for name in ['certify_compact.py','certify_quadratic.py','fast_exp_v2.py','crosscheck.cpp']},
 library_sha256=hashlib.sha256(Path(cert.lib.__file__).read_bytes()).hexdigest(),
 crosscheck_compile_command=command,
 status='Exact rational certificate and independent C++/MPFR crosscheck passed; not Lean verified')
out.write_text(json.dumps(r,indent=2))
print('Exact upper:',r['Psi_upper']['decimal_for_display'])
print('Independent C++/MPFR check passed:',d['bits'],'bits (about',d['decimal_digits'],'decimal digits).')
