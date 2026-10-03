"""Optimize small admissible survey mixtures with high-precision finite series.

Numerical optimization is exploratory. The finite series is an upper bound
analytically, but this script uses floating-point mpmath rather than intervals.
"""

import argparse
import json
from pathlib import Path

import mpmath as mp
import numpy as np
from scipy.optimize import minimize

from explore_series import series


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--alpha',default='4.268')
    parser.add_argument('--atoms',type=int,default=4)
    parser.add_argument('--cutoff',type=int,default=256)
    parser.add_argument('--output',default='results/richer_optimized.json')
    args = parser.parse_args()
    initial = json.loads(Path(f'results/richer_quantile_{args.atoms}.json').read_text())
    support = np.array(initial['support'])
    weights = [str(mp.mpf(1)/args.atoms)]*args.atoms
    calls = 0
    def objective(support):
        nonlocal calls
        calls += 1
        if np.max(support + support[::-1]) > 1:
            return 1 + float(np.max(support + support[::-1]) - 1)
        value = float(series(args.alpha,support,weights,args.cutoff)[-1]['upper_estimate'])
        if calls % 30 == 0:
            print(json.dumps(dict(calls=calls,value=value,support=support.tolist())),flush=True)
        return value
    opt = minimize(objective,support,method='L-BFGS-B',
                   bounds=[(max(.00001,x-.1),min(.999,x+.1)) for x in support],
                   options=dict(maxiter=150,ftol=1e-14,gtol=1e-8,maxls=30))
    rounded = [round(x,6) for x in opt.x]
    rows = series(args.alpha,rounded,weights,max(512,args.cutoff))
    result = dict(alpha=args.alpha,atoms=args.atoms,support=rounded,weights=weights,
                  pairs=list(zip(rounded[:args.atoms//2],rounded[:args.atoms//2-1:-1])),
                  optimization_cutoff=args.cutoff,optimization_value=opt.fun,
                  success=bool(opt.success),message=opt.message,validation=rows,
                  status='high precision numerical exploration, not interval certificate')
    Path(args.output).write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result),flush=True)


if __name__ == '__main__':
    main()
