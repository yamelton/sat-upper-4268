"""Exploratory finite-m hard/soft 3-atom trial; not a rigorous certificate.

At beta=infinity, cavity probabilities are 0, 1/2, 1 with masses
q/2, 1-q, q/2. A site message has weights 0, 1/2, 3/4, 1.
For m>0, zeros contribute zero to moments. The m=0 endpoint below
means the limit m down to zero: the probability of a positive weight.
"""

import argparse
import json
from pathlib import Path

import numpy as np
from scipy.optimize import minimize_scalar, root_scalar
from scipy.special import gammaln
from scipy.stats import poisson

from src.factorized import functional as energetic


class EntropicTrial:
    def __init__(self, cutoff=36):
        self.cutoff = cutoff
        self.degrees = np.arange(cutoff + 1)
        states = [(b, c) for b in range(cutoff + 1)
                  for c in range(cutoff + 1 - b)]
        self.b, self.c = np.array(states).T
        d = self.degrees[:, None]
        self.r = d - self.b - self.c
        self.valid = self.r >= 0
        self.log_multinomial = (gammaln(d+1) - gammaln(self.b+1)
                               - gammaln(self.c+1)
                               - gammaln(np.maximum(self.r, 0)+1))
        log_weight = -self.b*np.log(2) + self.c*np.log(.75)
        self.log_sum = np.logaddexp(log_weight[:, None], log_weight[None, :])

    def moments(self, q, m):
        p0 = q*q/4
        phalf = q*(1-q)
        pthree = (1-q)**2
        pone = q-q*q/4
        probs = np.exp(self.log_multinomial + self.b*np.log(phalf)
                       + self.c*np.log(pthree)
                       + np.maximum(self.r, 0)*np.log(pone))
        probs[~self.valid] = 0
        kernel = np.exp(m*self.log_sum)
        both_positive = probs @ kernel @ probs.T
        zero = 1 - (1-p0)**self.degrees
        one_positive = (pone+phalf*.5**m+pthree*.75**m)**self.degrees
        vertex = both_positive + zero[:, None]*one_positive[None, :]
        vertex += one_positive[:, None]*zero[None, :]
        # Enumerate the 27 cavity triples independently of vertex messages.
        cavity = [(0., q/2), (.5, 1-q), (1., q/2)]
        edge = sum(pa*pb*pc*(1-a*b*c)**m
                   for a, pa in cavity for b, pb in cavity for c, pc in cavity
                   if a*b*c < 1)
        return vertex, edge

    def functional(self, alpha, q, m):
        vertex, edge = self.moments(q, m)
        p = poisson.pmf(self.degrees, 3*alpha/2)
        return float(p @ np.log(vertex) @ p - 2*alpha*np.log(edge))


def scan_y():
    rows = []
    for y in [.1, .25, .5, 1., 2., 3., 4., 6., 8., 12., 20., 40.]:
        def optimum(alpha):
            return minimize_scalar(lambda q: energetic(alpha, q, y),
                                   bounds=(.5, .99), method='bounded')
        alpha = root_scalar(lambda a: optimum(a).fun,
                            bracket=(4.3, 5.3), xtol=1e-11).root
        opt = optimum(alpha)
        rows.append(dict(y=y, alpha=alpha, q=float(opt.x), value=float(opt.fun)))
    return rows


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--alpha', type=float, default=4.341011805)
    parser.add_argument('--cutoff', type=int, default=36)
    parser.add_argument('--output')
    args = parser.parse_args()
    trial = EntropicTrial(args.cutoff)
    rows = []
    for m in [0., .0001, .001, .01, .05, .1, .2, .4, .6, .8, 1.]:
        opt = minimize_scalar(lambda q: trial.functional(args.alpha, q, m),
                              bounds=(.5, .99), method='bounded')
        row = dict(alpha=args.alpha, m=m, q=float(opt.x), value=float(opt.fun))
        rows.append(row)
        print(json.dumps(row), flush=True)
    result = dict(cutoff=args.cutoff, entropic=rows, energetic=scan_y())
    if args.output:
        Path(args.output).write_text(json.dumps(result, indent=2) + '\n')
