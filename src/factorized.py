"""Exploratory energetic 1RSB trial; numerical outputs are not certificates."""

import argparse
import json
import numpy as np
from scipy.optimize import differential_evolution
from scipy.stats import binom, poisson


def functional(alpha, q, y, cutoff=55, k=3):
    """Return y times the candidate upper bound on negative ground energy.

    Outer signed degrees are independent Poisson(k*alpha/2). Inside each
    degree, each clause warns independently with probability (q/2)**(k-1).
    The zero-temperature inner star factor is exp(-y*min(B_plus,B_minus)).
    """
    d = np.arange(cutoff + 1)
    w = (q / 2) ** (k - 1)
    b = binom.pmf(d[None, :], d[:, None], w)
    kernel = np.exp(-y * np.minimum(d[:, None], d[None, :]))
    star = b @ kernel @ b.T
    p = poisson.pmf(d, k * alpha / 2)
    vertex = p @ np.log(star) @ p
    edge = -(k - 1) * alpha * np.log1p(-(q / 2) ** k * (-np.expm1(-y)))
    return float(vertex + edge)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--alpha', type=float, nargs='+', default=[4.3, 4.4, 4.4898, 4.6])
    args = parser.parse_args()
    for alpha in args.alpha:
        opt = differential_evolution(lambda x: functional(alpha, *x),
                                     [(0.01, 1), (0.01, 30)], seed=11,
                                     tol=1e-9, popsize=10)
        print(json.dumps(dict(alpha=alpha, q=float(opt.x[0]), y=float(opt.x[1]),
                              value=float(opt.fun), success=opt.success)), flush=True)
