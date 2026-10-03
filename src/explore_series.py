"""High precision exploration of a one-dimensional vertex series.

This is NOT an interval certificate. The identity is
E log(A+B-AB) = -sum_{k>=1} [E(1-A)^k]^2/k,
with E A^j = exp((3 alpha/2)*(E(1-R1*R2)^j - 1)).
Increasing K requires roughly K*log10(2) guard digits for binomial
cancellation; finite differences calculate all moments in O(K^2).
"""

import argparse
import json
import math
from pathlib import Path

import mpmath as mp


def series(alpha, support, weights, cutoff=512, checkpoints=None):
    mp.mp.dps = math.ceil(cutoff*math.log10(2)) + 60
    alpha = mp.mpf(str(alpha))
    support = [mp.mpf(str(x)) for x in support]
    weights = [mp.mpf(str(x)) for x in weights]
    assert abs(sum(weights)-1) < mp.mpf('1e-40')
    marks = [(1-r*s, p*q) for r,p in zip(support,weights)
             for s,q in zip(support,weights)]
    edge = -2*alpha*sum(p*q*v*mp.log(1-r*s*t)
                       for r,p in zip(support,weights)
                       for s,q in zip(support,weights)
                       for t,v in zip(support,weights))
    increments = [mp.exp(3*alpha/2*(sum(p*a**j for a,p in marks)-1))
                  for j in range(cutoff+1)]
    vertex = mp.mpf(0)
    rows = []
    checkpoints = checkpoints or {16,32,64,128,256,512,1024,2048,4096,cutoff}
    previous = mp.mpf(1)
    for k in range(1,cutoff+1):
        increments = [increments[j]-increments[j+1]
                      for j in range(len(increments)-1)]
        moment = increments[0]
        assert 0 <= moment <= previous
        previous = moment
        vertex -= moment**2/k
        if k in checkpoints:
            rows.append(dict(k=k, moment=str(mp.nstr(moment,25)),
                             vertex=str(mp.nstr(vertex,25)),
                             edge=str(mp.nstr(edge,25)),
                             upper_estimate=str(mp.nstr(vertex+edge,25))))
    return rows


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--alpha',default='4.341011805')
    parser.add_argument('--support',nargs='+',default=['.42379'])
    parser.add_argument('--weights',nargs='+',default=['1'])
    parser.add_argument('--cutoff',type=int,default=512)
    parser.add_argument('--output')
    args = parser.parse_args()
    rows = series(args.alpha,args.support,args.weights,args.cutoff)
    result = dict(alpha=args.alpha,support=args.support,weights=args.weights,
                  precision=mp.mp.dps,cutoff=args.cutoff,rows=rows)
    print(json.dumps(result,indent=2),flush=True)
    if args.output:
        Path(args.output).write_text(json.dumps(result,indent=2)+'\n')
