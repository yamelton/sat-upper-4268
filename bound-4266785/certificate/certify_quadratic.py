"""Exact enclosure for rho=140/1989*(1-r)^(1/3)*(24-34*r+37*r^2).

No atoms. Positive Bernstein decomposition: [24,7,27].
Independent moment representations:
 m_h = (1)_h/(7/3)_h * (24-34*(h+1)/(h+7/3)
       +37*(h+1)*(h+2)/((h+7/3)*(h+10/3))) / (663/35)
     = (1)_h/(13/3)_h * (81*h*h+299*h+442)/442.
Rational enclosure uses the first; Decimal crosscheck uses the second.
Tail domination: rho / Beta(1,4/3) density <= 315/221.
"""
from pathlib import Path
from fractions import Fraction as F
from decimal import Decimal as D,localcontext
import sys,math,json,time,hashlib,argparse
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT))
import arithmetic as lib

ALPHA=F(853357,200000)

def exact(T=5120,H=512):
 start=time.monotonic();guard=80
 moment_bits=2*T+guard+math.ceil(math.log2(H+2));exp_bits=T+guard
 scale=1<<moment_bits;exp_scale=1<<exp_bits;out_scale=1<<guard
 raw_lo=raw_hi=scale;lower=[scale];upper=[scale]
 for h in range(1,max(T,H+1)+1):
  ratio=F(3*h,3*h+4)
  raw_lo=raw_lo*ratio.numerator//ratio.denominator
  raw_hi=lib.ceil_div(raw_hi*ratio.numerator,ratio.denominator)
  factor=(24-34*F(3*h+3,3*h+7)+37*F(9*(h+1)*(h+2),(3*h+7)*(3*h+10)))/F(663,35)
  assert factor>0
  lower.append(raw_lo*factor.numerator//factor.denominator)
  upper.append(lib.ceil_div(raw_hi*factor.numerator,factor.denominator))
  if h==H+1:raw_tail_upper=F(raw_hi,scale)
 tail=lib.correction_tail(3,F(1),F(4,3),raw_tail_upper,H+1)*F(315,221)**3
 print('Moments enclosed',T,flush=True)
 powers=[lib.scaled_power_bounds(lo,hi,2,scale) for lo,hi in zip(lower[:T+1],upper[:T+1])]
 nu_lo,nu_hi=lib.complement_bounds([x for x,y in powers],[y for x,y in powers],scale)
 print('First binomial transform enclosed',flush=True)
 compound_lo=[];compound_hi=[]
 for j,(lo,hi) in enumerate(zip(nu_lo,nu_hi)):
  xl=3*ALPHA/2*(F(lo,scale)-1);xu=3*ALPHA/2*(F(hi,scale)-1)
  ml,_=lib.exp_bounds_taylor(xl,exp_bits);_,mu=lib.exp_bounds_taylor(xu,exp_bits)
  compound_lo.append(max(0,ml));compound_hi.append(min(exp_scale,mu))
  if j%1024==0:print('Exponentials',j,'elapsed',round(time.monotonic()-start,1),flush=True)
 mu_lo,mu_hi=lib.complement_bounds(compound_lo,compound_hi,exp_scale)
 # Outward round each site term at 80 bits; total error <= T*2^-80.
 # This avoids repeatedly reducing very large rational partial sums.
 site_lo=site_hi=0
 for h in range(1,T+1):
  denominator=exp_scale**2*h
  site_lo-=lib.ceil_div(mu_hi[h]**2*out_scale,denominator)
  site_hi-=mu_lo[h]**2*out_scale//denominator
 site_lo,site_hi=F(site_lo,out_scale),F(site_hi,out_scale)
 corr_lo=corr_hi=0
 for h in range(1,H+1):
  lo,hi=lib.scaled_power_bounds(lower[h],upper[h],3,scale)
  corr_lo+=lo//h;corr_hi+=lib.ceil_div(hi,h)
 corr_lo=2*ALPHA*F(corr_lo,scale)
 corr_hi=2*ALPHA*(F(corr_hi,scale)+tail)
 def rounded(x,up):
  n=x.numerator*out_scale;d=x.denominator
  return F(lib.ceil_div(n,d) if up else n//d,out_scale)
 corr_lo=rounded(corr_lo,False);corr_hi=rounded(corr_hi,True)
 r=dict(alpha=str(ALPHA),T=T,H=H,moment_bits=moment_bits,exp_bits=exp_bits,final_bits=guard,
        density='140/1989 * (1-r)^(1/3) * (24-34*r+37*r^2)',zero_atom='0',
        a='1',b='4/3',bernstein_coefficients=['24','7','27'],normalization_integral='1989/140',
        S_lower=lib.rational(site_lo),S_upper=lib.rational(site_hi),
        C_lower=lib.rational(corr_lo),C_upper=lib.rational(corr_hi),
        correction_tail_upper=lib.rational(2*ALPHA*tail),
        Psi_lower=lib.rational(site_lo+corr_lo),Psi_upper=lib.rational(site_hi+corr_hi),
        certified_negative=site_hi+corr_hi<0,exact_seconds=time.monotonic()-start,
        status='Exact rational enclosure; not Lean verified')
 return r

def numerical(T,H):
 digits=math.ceil(T*math.log10(4))+100
 with localcontext() as ctx:
  ctx.prec=digits;a=D(853357)/200000
  raw=D(1);moments=[D(1)]
  for h in range(1,max(T,H+1)+1):
   raw*=D(3*h)/(3*h+10)
   moments.append(raw*(81*h*h+299*h+442)/442)
  nu=lib.complement_moments([v*v for v in moments[:T+1]])
  assert all(0<=v<=1 for v in nu)
  mu=lib.complement_moments([(3*a/2*(v-1)).exp() for v in nu])
  assert all(0<=v<=1 for v in mu)
  site=-sum(v*v/h for h,v in enumerate(mu[1:],1))
  correction=2*a*sum(moments[h]**3/h for h in range(1,H+1))
  # A separate base-beta recurrence for the explicit dominating tail.
  raw=D(1)
  for h in range(1,H+2):raw*=D(3*h)/(3*h+4)
  tail=2*a*raw**3/(H+1)*(1+(D(7)/3+H+1)/4)*(D(315)/221)**3
  return dict(digits=digits,S_T=str(site),C_partial=str(correction),
              Psi_T_lower=str(site+correction),Psi_T_upper=str(site+correction+tail))

def audit_moments():
 raw1=raw2=F(1)
 for h in range(80):
  if h:
   raw1*=F(3*h,3*h+4);raw2*=F(3*h,3*h+10)
  m1=raw1*(24-34*F(3*h+3,3*h+7)+37*F(9*(h+1)*(h+2),(3*h+7)*(3*h+10)))/F(663,35)
  m2=raw2*F(81*h*h+299*h+442,442)
  assert m1==m2
 # Integral = 24 B(1,10/3)+14 B(2,7/3)+27 B(3,4/3).
 assert 24*F(3,10)+14*F(9,70)+27*F(27,140)==F(1989,140)
 return dict(moment_identities_checked=80,normalization_exact=True,positive_bernstein_coefficients=True,
             domination_constant='315/221')

def main():
 p=argparse.ArgumentParser();p.add_argument('--T',type=int,default=5120);p.add_argument('--H',type=int,default=512)
 args=p.parse_args();checks=audit_moments();r=exact(args.T,args.H)
 out=ROOT/f'quadratic-certificate-T{args.T}.json';out.write_text(json.dumps(r,indent=2))
 print('Exact upper',r['Psi_upper']['decimal_for_display'],'negative',r['certified_negative'],flush=True)
 assert r['certified_negative']
 check=numerical(args.T,args.H)
 for lo,hi,key in [('S_lower','S_upper','S_T'),('C_lower','C_upper','C_partial'),('Psi_lower','Psi_upper','Psi_T_lower'),('Psi_lower','Psi_upper','Psi_T_upper')]:
  assert F(r[lo]['exact'])<=F(check[key])<=F(r[hi]['exact']),key
 r.update(independent_decimal_check=check,algebra_checks=checks,
          source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
          library_sha256=hashlib.sha256(Path(lib.__file__).read_bytes()).hexdigest())
 out.write_text(json.dumps(r,indent=2));print('Independent Decimal crosscheck passed:',check['digits'],'digits',flush=True)
if __name__=='__main__':main()
