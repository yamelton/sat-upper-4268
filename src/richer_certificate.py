"""Exact interval certificate for a finite mixture of asymmetric cavity surveys.

This certifies the finite interpolation expression Psi_K; its implication
for random 3-SAT additionally needs the mathematical interpolation argument. All transcendental bounds use integer arithmetic.

The survey pairs are a convenient parametrization of a finite law of warning
rates: choose either a or b with equal probability, then draw a Bernoulli
warning at that rate. All cavity states are binary; there is no neutral state.
The vertex identity E[((1-A)(1-B))^k] = [E(1-A)^k]^2 avoids a
multidimensional sum. The proof chooses its softening parameter sufficiently
large after certifying Psi_K < 0, so no numerical temperature is needed.
"""

import argparse
from fractions import Fraction as F
import json
from pathlib import Path

try:
    from .certificate import log_bounds
except ImportError:
    from certificate import log_bounds


def ceildiv(n, d):
    assert d > 0
    return -((-n)//d)


def exp_grid_bounds(x, scale, terms):
    """Return integer lo,hi with lo/scale <= exp(x) <= hi/scale.

    Nonnegative input is enclosed on the grid first. Every Taylor multiply
    and divide rounds outward. The first omitted term is bounded above,
    and all remaining term ratios are <= x_upper/(terms+2).
    """
    x = F(x)
    if x < 0:
        lower, upper = exp_grid_bounds(-x, scale, terms)
        assert lower > 0
        return scale*scale//upper, ceildiv(scale*scale, lower)
    xlower = x.numerator*scale//x.denominator
    xupper = ceildiv(x.numerator*scale, x.denominator)
    assert xupper < scale*(terms+2)
    termlower = termupper = scale
    lower = upper = scale
    for j in range(1,terms+1):
        termlower = termlower*xlower//(scale*j)
        termupper = ceildiv(termupper*xupper, scale*j)
        lower += termlower
        upper += termupper
    omitted = ceildiv(termupper*xupper, scale*(terms+1))
    remainder = ceildiv(omitted*scale*(terms+2),
                        scale*(terms+2)-xupper)
    return lower, upper+remainder


def certificate(alpha=F(107,25), a=F(139,1000), b=F(719,1000),
                cutoff=128, surveys=None):
    alpha, a, b = F(alpha), F(a), F(b)
    assert alpha > 0
    assert cutoff >= 1
    if surveys is None:
        surveys = [(a,b,F(1))]
    surveys = [(F(u),F(v),F(p)) for u,v,p in surveys]
    assert sum(p for _,_,p in surveys) == 1
    atom_weights = {}
    for u,v,p in surveys:
        assert 0 <= u < 1 and 0 <= v < 1 and u+v <= 1 and p > 0
        for r in (u,v):
            atom_weights[r] = atom_weights.get(r,F(0)) + p/2
    atoms = list(atom_weights.items())
    # 1/3 > log10(2): guard digits absorb 2**cutoff amplification by
    # finite differences, while keeping exact intermediate integers small.
    digits = cutoff//3 + 65
    scale = 10**digits
    terms = 3*digits+64
    rate = 3*alpha/2
    mark_weights = {}
    for r,p in atoms:
        for s,q in atoms:
            mark = 1-r*s
            mark_weights[mark] = mark_weights.get(mark,F(0)) + p*q
    marks = list(mark_weights.items())
    powers = [F(1) for _ in marks]
    lower, upper = [], []
    for j in range(cutoff+1):
        mean = sum(weight*power for (_,weight),power in zip(marks,powers))
        lo,hi = exp_grid_bounds(rate*(mean-1), scale, terms)
        lower.append(lo)
        upper.append(hi)
        powers = [power*mark for power,(mark,_) in zip(powers,marks)]

    # μ_k = sum_j (-1)^j choose(k,j) E A^j. Interval forward differences
    # have integer-grid endpoints, so this step introduces no rounding.
    vertex_upper = F(0)
    max_moment_interval_width = 0
    for k in range(1,cutoff+1):
        newlower = [lower[j]-upper[j+1] for j in range(len(lower)-1)]
        newupper = [upper[j]-lower[j+1] for j in range(len(upper)-1)]
        lower,upper = newlower,newupper
        assert lower[0] <= upper[0] and upper[0] >= 0 and lower[0] <= scale
        # The true μ_k is nonnegative. A lower bound on its square yields
        # an upper bound on its negative contribution. Omitted k also
        # contribute nonpositively, so no tail estimate is required.
        moment_lower = max(0,lower[0])
        vertex_upper -= F(moment_lower*moment_lower, scale*scale*k)
        max_moment_interval_width = max(max_moment_interval_width,
                                        upper[0]-lower[0])

    edge_weights = {}
    for r,p in atoms:
        for s,q in atoms:
            for t,v in atoms:
                c = r*s*t
                edge_weights[c] = edge_weights.get(c,F(0)) + p*q*v
    edge_masses = list(edge_weights.items())
    edge_upper = -2*alpha*sum(weight*log_bounds(1-c)[0]
                             for c,weight in edge_masses)
    psi_upper = vertex_upper + edge_upper
    return dict(alpha=alpha,
                trial_field_law="Bernoulli warning with rate r",
                surveys=[dict(a=u,b=v,probability=p)
                         for u,v,p in surveys],
                bad_mass_law=[dict(r=r,probability=p) for r,p in atoms],
                cutoff=cutoff,
                digits=digits,exp_terms=terms,
                vertex_upper=vertex_upper,edge_upper=edge_upper,
                psi_upper=psi_upper,
                max_moment_interval_width=F(max_moment_interval_width,scale),
                certified_negative=psi_upper < 0)


def serialized(value):
    if isinstance(value,F):
        return dict(exact=str(value),decimal_for_display=float(value))
    if isinstance(value,dict):
        return {key:serialized(item) for key,item in value.items()}
    if isinstance(value,list):
        return [serialized(item) for item in value]
    return value


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--alpha',type=F,default=F(107,25))
    parser.add_argument('--a',type=F,default=F(139,1000))
    parser.add_argument('--b',type=F,default=F(719,1000))
    parser.add_argument('--cutoff',type=int,default=128)
    parser.add_argument('--surveys',nargs='+',
                        help='Triples a,b,probability; overrides --a and --b')
    parser.add_argument('--output')
    args = parser.parse_args()
    surveys = ([tuple(map(F,item.split(','))) for item in args.surveys]
               if args.surveys else None)
    result = certificate(args.alpha,args.a,args.b,args.cutoff,
                         surveys=surveys)
    output = json.dumps(serialized(result),indent=2)+'\n'
    if args.output:
        Path(args.output).write_text(output)
    print(output,end='')
    if not result['certified_negative']:
        raise SystemExit('The selected parameters did not certify negativity.')
