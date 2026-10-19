"""Generate the compact untrusted witness and its kernel arithmetic checks.

The polynomial seed is data; its optimization is not part of the trusted proof.
"""
from fractions import Fraction as F
from pathlib import Path
import json,hashlib,time,sys
from certificate.lean_witness import floor,ceil,transform,taylor_bounds,array,integer
sys.path.insert(0,str(Path(__file__).resolve().parent/"certificate"))
from certificate.certify_polynomial import polynomial

ROOT=Path(__file__).resolve().parent
SRC=ROOT/'lean/SatFinal/PolynomialNumerics'
NS='SatFinal.PolynomialNumerics'

def seq(name,values,typ):
 entries=[]
 for v in values:
  if typ=='ℚ':entries.append(f'({integer(v.numerator)} : ℚ)/{integer(v.denominator)}')
  else:entries.append(integer(v))
 return f'def {name} : Array {typ} := ⟨[\n  '+',\n  '.join(entries)+'\n]⟩\n\n'

def generate():
 began=time.monotonic();SRC.mkdir(exist_ok=True)
 T,H=192,512; mb,eb,ab,ib,fb=1200,900,940,1100,80
 ms,es,args,internal,fs=[1<<b for b in [mb,eb,ab,ib,fb]]
 alpha=F(853357,200000);terms,squarings=48,32
 raw=[(ms,ms)];moments=[(ms,ms)]
 for h in range(1,514):
  ratio=F(3*h,3*h+4)
  raw.append((floor(raw[-1][0]*ratio),ceil(raw[-1][1]*ratio)))
  factor=F(35*(81*h*h+299*h+442),221*(3*h+7)*(3*h+10))
  moments.append((floor(raw[-1][0]*factor),ceil(raw[-1][1]*factor)))
 powers=[(floor(F(a*a,ms)),ceil(F(b*b,ms))) for a,b in moments[:T+1]]
 nu=transform(powers)
 arguments=[(floor(3*alpha/2*(F(a,ms)-1)*args),ceil(3*alpha/2*(F(b,ms)-1)*args)) for a,b in nu]
 compound=[]
 for a,b in arguments:
  xl,xu=F(a,args),F(b,args)
  l,u=taylor_bounds(xl,internal,terms,squarings)
  compound.append((floor(l*es),ceil((u+xu-xl)*es)))
 side=transform(compound)
 assert all(0<=a<=b<=es for a,b in side)
 P=polynomial(); assert len(P)==T+1
 site=[floor(p*F((a if p>=0 else b)**2,es*es)*fs) for p,(a,b) in zip(P,side)]
 correction=[0]+[ceil(F(moments[h][1]**3*fs,ms**3*h)) for h in range(1,H+1)]
 tail=F(315,221)**3*F(raw[H+1][1],ms)**3/(H+1)*(1+F(H+1+F(7,3),4))
 tailupper=ceil(tail*fs)
 total=-sum(site)+ceil(2*alpha*(sum(correction)+tailupper))
 assert F(total,fs)<F(-4,10**10)
 seed=json.loads((ROOT/'certificate/polynomial-seed.json').read_text())
 R=[F(int(v),int(seed['scale'])) for v in seed['coefficients']]
 header='import SatKUpper.BetaEnclosures\nimport SatKUpper.DifferenceEnclosures\nimport SatKUpper.TaylorExponential\n'
 header+='set_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace '+NS+'.Data\n'
 header+='def a : ℚ := 1\ndef b : ℚ := 4/3\ndef tau : ℚ := 0\ndef alpha : ℚ := 853357/200000\n'
 for key,value in [('T',T),('H',H),('momentScale',ms),('expScale',es),('argumentScale',args),('internalScale',internal),('finalScale',fs),('terms',terms),('squarings',squarings)]:
  header+=f'def {key} : ℕ := {integer(value)}\n'
 for name,rows in [('raw',raw),('moments',moments),('powers',powers),('nu',nu),('arguments',arguments),('compound',compound),('side',side)]:header+=array(name,rows)
 header+=seq('coefficients',P,'ℚ')+seq('squareCoefficients',R,'ℚ')
 header+=seq('siteTerms',site,'ℤ')+array('correctionTerms',correction,False)
 header+=f'def tailUpper : ℕ := {integer(tailupper)}\ndef totalUpper : ℤ := {integer(total)}\n'
 header+='end '+NS+'.Data\n'
 (SRC/'Data.lean').write_text(header)
 defs=(ROOT/'templates/polynomial-definitions.lean').read_text()
 (SRC/'Definitions.lean').write_text(defs)
 imports=[];proof='namespace '+NS+'.Checks\n'
 for family,prop,count,step in [('Raw','rawStep',513,64),('Moment','momentStep',514,64),('Power','powerStep',193,64),('Argument','argumentStep',193,64),('Exp','expStep',193,8),('Site','siteStep',193,64),('Correction','correctionStep',512,64)]:
  starts=list(range(0,count,step))
  for i,s in enumerate(starts):
   n=min(step,count-s);module=family+str(i);imports.append('import '+NS+'.'+module+'\n')
   text='import '+NS+'.Definitions\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace '+NS+'.Checks\n'
   text+=f'theorem {family.lower()}_block_{i} : ∀ j : Fin {n}, {prop} ({s}+j.val) := by decide +kernel\nend '+NS+'.Checks\n'
   (SRC/(module+'.lean')).write_text(text)
  proof+=f'theorem {family.lower()}_steps : ∀ j : Fin {count}, {prop} j := by\n  intro j\n  have hj := j.isLt\n  match h : j.val/{step} with\n'
  for i,s in enumerate(starts):
   proof+=f'  | {i} =>\n    have hb := {family.lower()}_block_{i} ⟨j.val-{s}, by omega⟩\n    simpa only [show {s}+(j.val-{s}) = j.val by omega] using hb\n'
  proof+=f'  | n+{len(starts)} => omega\n'
 proof+='end '+NS+'.Checks\n'
 (SRC/'Checks.lean').write_text(''.join(imports)+proof)
 transforms='import '+NS+'.Data\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace '+NS+'.Checks\nopen Data SatKUpper.DifferenceEnclosures\n'
 for name,input in [('nu','powers'),('side','compound')]:transforms+=f'theorem {name}_table : table 193 {input}.toList = {name}.toList := by decide +kernel\n'
 (SRC/'Transforms.lean').write_text(transforms+'end '+NS+'.Checks\n')
 for i,start in enumerate(range(0,194,16)):
  count=min(16,194-start)
  text=f'''import SatFinal.PolynomialNumerics.Data
import SatFinal.PolynomialCoefficients
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace SatFinal.PolynomialNumerics.Checks
open Data SatFinal.PolynomialCoefficients
theorem coefficient_block_{i} : ∀ h : Fin {count},
    coefficients.getD ({start}+h.val+1) 0*({start}+h.val+1 : ℚ) = rhsCoeff squareCoefficients ({start}+h.val) := by decide +kernel
end SatFinal.PolynomialNumerics.Checks
'''
  (SRC/f'Coefficient{i}.lean').write_text(text)
 report=dict(status='Untrusted witness; complete Lean verification pending',T=T,H=H,moment_bits=mb,exp_bits=eb,upper=str(F(total,fs)),upper_decimal=float(F(total,fs)),elapsed_seconds=time.monotonic()-began,data_bytes=len(header.encode()),data_sha256=hashlib.sha256(header.encode()).hexdigest(),generator_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
 (ROOT/'results/polynomial-lean-witness.json').write_text(json.dumps(report,indent=2)+'\n');print(report)

if __name__=='__main__':generate()
