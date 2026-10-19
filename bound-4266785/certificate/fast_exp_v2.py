"""Same exact exponential enclosure, with factored integer division.

For D=odd*2^shift, floor(N/D)=floor(N/odd)>>shift.
The corresponding nested-ceiling identity is also exact. Extra scaling reduces Taylor degree; dyadic squarings use exact bit shifts.
The same positive-series remainder bound applies because y <= 1/2.
"""
from fractions import Fraction as F
import math

def ceil_div(n,d):return -(-n//d)

def exp_bounds_taylor(x,final_bits,guard_bits=64,minimum_squarings=32):
 x=F(x)
 if x>0 or final_bits<1:raise ValueError('Invalid exponent or precision')
 if x==0:return (1<<final_bits,)*2
 y=-x;squarings=0
 while y>F(1,2) or squarings<minimum_squarings:y/=2;squarings+=1
 bits=final_bits+2*squarings+guard_bits+math.ceil(math.log2(final_bits+2))
 scale=1<<bits
 shift=(y.denominator & -y.denominator).bit_length()-1
 odd=y.denominator>>shift;mask=(1<<shift)-1
 def down(n,k):return (n//(odd*k))>>shift
 def up(n,k):return (ceil_div(n,odd*k)+mask)>>shift
 term_lo=term_hi=sum_lo=sum_hi=scale;index=0
 while True:
  index+=1
  term_lo=down(term_lo*y.numerator,index)
  term_hi=up(term_hi*y.numerator,index)
  sum_lo+=term_lo;sum_hi+=term_hi
  if term_hi<=1:
   sum_hi+=2*up(term_hi*y.numerator,index+1);break
 lo,hi=scale**2//sum_hi,ceil_div(scale**2,sum_lo)
 for _ in range(squarings):lo,hi=(lo*lo)>>bits,(hi*hi+scale-1)>>bits
 divisor=1<<(bits-final_bits)
 return lo>>(bits-final_bits),(hi+divisor-1)>>(bits-final_bits)
