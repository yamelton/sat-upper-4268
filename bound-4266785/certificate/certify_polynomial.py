"""Exact rational certificate for the degree-192 site logarithm minorant.

The untrusted seed specifies R. Set P(0)=0 and P'=2R-(1-X)R².
Then (-log(1-x)-P(x))'=(1-(1-x)R(x))²/(1-x)>=0 on [0,1).
All numerical operations below use rational or outward-rounded integer arithmetic.
This script is not a substitute for Lean kernel verification.
"""
from pathlib import Path
from fractions import Fraction as F
import json,time,hashlib
from decimal import Decimal, localcontext
import arithmetic as lib
from fast_exp_v2 import exp_bounds_taylor
ROOT=Path(__file__).resolve().parent
ALPHA=F(853357,200000)

def polynomial():
 seed=json.loads((ROOT/'polynomial-seed.json').read_text())
 R=[F(int(v),int(seed['scale'])) for v in seed['coefficients']]
 sq=[F(0)]*(2*len(R)-1)
 for i,a in enumerate(R):
  for j,b in enumerate(R):sq[i+j]+=a*b
 dp=[F(0)]*(2*len(R))
 for i,a in enumerate(R):dp[i]+=2*a
 for i,a in enumerate(sq):dp[i]-=a;dp[i+1]+=a
 return [F(0)]+[a/(i+1) for i,a in enumerate(dp)]

def crosscheck(P):
 # Independent Decimal evaluation: closed moments, direct binomial sums,
 # Decimal.exp (not the rational Taylor enclosure), and a separate tail.
 import math
 with localcontext() as ctx:
  ctx.prec=420
  D=Decimal;alpha=D(853357)/200000;T=len(P)-1;H=512
  raw=D(1);moments=[D(1)]
  for h in range(1,max(T,H+1)+1):
   raw*=D(3*h)/(3*h+10)
   moments.append(raw*(81*h*h+299*h+442)/442)
  nu=[sum((-1)**h*D(math.comb(j,h))*moments[h]**2 for h in range(j+1)) for j in range(T+1)]
  compound=[(3*alpha/2*(v-1)).exp() for v in nu]
  side=[sum((-1)**j*D(math.comb(h,j))*compound[j] for j in range(h+1)) for h in range(T+1)]
  site=sum(D(p.numerator)/D(p.denominator)*v*v for p,v in zip(P,side))
  raw=D(1)
  for h in range(1,H+2):raw*=D(3*h)/(3*h+4)
  tail=(D(315)/221)**3*raw**3/(H+1)*(1+(D(7)/3+H+1)/4)
  correction=2*alpha*(sum(moments[h]**3/h for h in range(1,H+1))+tail)
  return dict(digits=ctx.prec,site=str(site),correction=str(correction),upper=str(correction-site))

def exact():
 start=time.monotonic();P=polynomial();T=len(P)-1;H=512
 mb,eb,fb=1200,900,80
 ms,es,fs=1<<mb,1<<eb,1<<fb
 rawlo=rawhi=ms;lo=[ms];hi=[ms]
 for h in range(1,max(T,H+1)+1):
  rawlo=rawlo*(3*h)//(3*h+4);rawhi=lib.ceil_div(rawhi*(3*h),3*h+4)
  factor=F(35*(81*h*h+299*h+442),221*(3*h+7)*(3*h+10))
  lo.append(rawlo*factor.numerator//factor.denominator)
  hi.append(lib.ceil_div(rawhi*factor.numerator,factor.denominator))
 tail=F(315,221)**3*lib.correction_tail(3,F(1),F(4,3),F(rawhi,ms),H+1)
 powers=[lib.scaled_power_bounds(a,b,2,ms) for a,b in zip(lo[:T+1],hi[:T+1])]
 nl,nu=lib.complement_bounds([a for a,b in powers],[b for a,b in powers],ms)
 compound=[]
 for a,b in zip(nl,nu):
  xl=3*ALPHA/2*(F(a,ms)-1);xu=3*ALPHA/2*(F(b,ms)-1)
  ml,_=exp_bounds_taylor(xl,eb);_,mu=exp_bounds_taylor(xu,eb)
  compound.append((ml,mu))
 sl,su=lib.complement_bounds([a for a,b in compound],[b for a,b in compound],es)
 assert all(0<=a<=b<=es for a,b in zip(sl,su))
 L=U=F(0)
 for p,a,b in zip(P,sl,su):
  lower,upper=F(a*a,es*es),F(b*b,es*es)
  if p<0:lower,upper=upper,lower
  L+=p*lower;U+=p*upper
 corr=2*ALPHA*(sum(F(hi[h],ms)**3/h for h in range(1,H+1))+tail)
 upper=F(lib.ceil_div((corr-L).numerator*fs,(corr-L).denominator),fs)
 assert upper<F(-4,10**10)
 def roundq(x,up):return str(F(lib.ceil_div(x.numerator*fs,x.denominator) if up else x.numerator*fs//x.denominator,fs))
 check=crosscheck(P)
 assert L<=F(check['site'])<=U
 assert F(check['upper'])<=upper
 report=dict(independent_decimal_check=check,status='Exact rational numerical certificate passed; Lean verification pending',alpha=str(ALPHA),T=T,H=H,moment_bits=mb,exp_bits=eb,final_bits=fb,
  site_polynomial_lower=roundq(L,False),site_polynomial_upper=roundq(U,True),correction_upper=roundq(corr,True),
  criterion_upper=str(upper),criterion_upper_decimal=float(upper),elapsed_seconds=time.monotonic()-start,
  source_sha256={f:hashlib.sha256((ROOT/f).read_bytes()).hexdigest() for f in ['certify_polynomial.py','polynomial-seed.json','arithmetic.py','fast_exp_v2.py']})
 (ROOT/'polynomial-certificate.json').write_text(json.dumps(report,indent=2)+'\n')
 print(json.dumps(report,indent=2))
 return report

if __name__=='__main__':exact()
