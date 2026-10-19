// Independent MPFR evaluation. Numerical crosscheck, not an interval proof.
#include <mpfr.h>
#include <vector>
#include <cstdio>
#include <cstdlib>
#include <cassert>
#include <chrono>
constexpr mpfr_prec_t BITS=11000;
constexpr mpfr_rnd_t RN=MPFR_RNDN;
struct Real {
  mpfr_t v;
  Real(){mpfr_init2(v,BITS);mpfr_set_zero(v,0);}
  Real(const Real& x){mpfr_init2(v,BITS);mpfr_set(v,x.v,RN);}
  Real& operator=(const Real& x){mpfr_set(v,x.v,RN);return *this;}
  ~Real(){mpfr_clear(v);}
};
std::vector<Real> complement(std::vector<Real> row){
  const size_t n=row.size();std::vector<Real> out(n);out[0]=row[0];
  for(size_t h=1;h<n;++h){
    for(size_t j=0;j<n-h;++j)mpfr_sub(row[j].v,row[j].v,row[j+1].v,RN);
    out[h]=row[0];
    assert(mpfr_cmp_ui(out[h].v,0)>=0 && mpfr_cmp_ui(out[h].v,1)<=0);
  }
  return out;
}
void field(const char* key,const Real& x,bool comma=true){
  char* s=nullptr;mpfr_asprintf(&s,"%.110Rg",x.v);
  printf("  \"%s\": \"%s\"%s\n",key,s,comma?",":"");mpfr_free_str(s);
}
int main(){
  constexpr unsigned T=5120,H=512,N=H+1;
  auto start=std::chrono::steady_clock::now();
  Real alpha,raw,tmp,site,correction,tail,low,upper;
  mpfr_set_ui(alpha.v,853357,RN);mpfr_div_ui(alpha.v,alpha.v,200000,RN);
  std::vector<Real> moments(T+1),powers(T+1);
  mpfr_set_ui(raw.v,1,RN);mpfr_set_ui(moments[0].v,1,RN);
  for(unsigned h=1;h<=T;++h){
    mpfr_mul_ui(raw.v,raw.v,3*h,RN);mpfr_div_ui(raw.v,raw.v,3*h+10,RN);
    unsigned long P=81UL*h*h+299UL*h+442;
    mpfr_mul_ui(moments[h].v,raw.v,P,RN);mpfr_div_ui(moments[h].v,moments[h].v,442,RN);
  }
  for(unsigned h=0;h<=T;++h)mpfr_sqr(powers[h].v,moments[h].v,RN);
  auto nu=complement(powers);std::vector<Real> compound(T+1);
  fprintf(stderr,"MPFR first transform complete\n");
  for(unsigned h=0;h<=T;++h){
    mpfr_sub_ui(tmp.v,nu[h].v,1,RN);mpfr_mul(tmp.v,tmp.v,alpha.v,RN);
    mpfr_mul_ui(tmp.v,tmp.v,3,RN);mpfr_div_ui(tmp.v,tmp.v,2,RN);
    mpfr_exp(compound[h].v,tmp.v,RN);
  }
  auto mu=complement(compound);
  fprintf(stderr,"MPFR second transform complete\n");
  for(unsigned h=1;h<=T;++h){
    mpfr_sqr(tmp.v,mu[h].v,RN);mpfr_div_ui(tmp.v,tmp.v,h,RN);mpfr_sub(site.v,site.v,tmp.v,RN);
  }
  for(unsigned h=1;h<=H;++h){
    mpfr_pow_ui(tmp.v,moments[h].v,3,RN);mpfr_div_ui(tmp.v,tmp.v,h,RN);
    mpfr_add(correction.v,correction.v,tmp.v,RN);
  }
  mpfr_mul(correction.v,correction.v,alpha.v,RN);mpfr_mul_ui(correction.v,correction.v,2,RN);
  mpfr_set_ui(raw.v,1,RN);
  for(unsigned h=1;h<=N;++h){mpfr_mul_ui(raw.v,raw.v,3*h,RN);mpfr_div_ui(raw.v,raw.v,3*h+4,RN);}
  // Tail = 2 alpha * raw_N^3/N * (1+(N+7/3)/4) * (315/221)^3.
  mpfr_mul_ui(raw.v,raw.v,315,RN);mpfr_div_ui(raw.v,raw.v,221,RN);
  mpfr_pow_ui(tail.v,raw.v,3,RN);mpfr_div_ui(tail.v,tail.v,N,RN);
  mpfr_mul_ui(tail.v,tail.v,3*N+19,RN);mpfr_div_ui(tail.v,tail.v,12,RN);
  mpfr_mul(tail.v,tail.v,alpha.v,RN);mpfr_mul_ui(tail.v,tail.v,2,RN);
  mpfr_add(low.v,site.v,correction.v,RN);mpfr_add(upper.v,low.v,tail.v,RN);
  double seconds=std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();
  printf("{\n  \"method\": \"Independent C++/MPFR calculation with the alternative moment formula\",\n");
  printf("  \"mpfr_version\": \"%s\",\n  \"bits\": %ld,\n  \"decimal_digits\": 3311,\n  \"T\": %u,\n  \"H\": %u,\n  \"seconds\": %.6f,\n",mpfr_get_version(),long(BITS),T,H,seconds);
  field("S_T",site);field("C_partial",correction);field("correction_tail_upper",tail);
  field("Psi_T_lower",low);field("Psi_T_upper",upper,false);printf("}\n");
}
