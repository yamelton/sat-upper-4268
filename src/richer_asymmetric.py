"""Exploratory two-atom hard-survey law with quasi-Monte Carlo vertex sum.

Every inner survey has masses a,b at +beta,-beta and 1-a-b at zero.
Independent fair signs make the hard-bad probability R uniform on {a,b}.
Thus warning probabilities are a*a,a*b,b*b with probabilities 1/4,1/2,1/4.
QMC is used only to choose promising rational parameters, not as a proof.
"""

import argparse
import json
from pathlib import Path

import numpy as np
from scipy.optimize import differential_evolution
from scipy.stats import poisson, qmc

from richer_population import log_star


class Trial:
    def __init__(self, alpha, power=18, seed=1729):
        self.alpha = alpha
        samples = qmc.Sobol(6, scramble=True, seed=seed).random_base2(power)
        means = np.array([.375, .75, .375] * 2) * alpha
        self.counts = poisson.ppf(samples, means).astype(np.int16)

    def evaluate(self, a, b):
        jumps = -np.log1p(-np.array([a*a, a*b, b*b]))
        s = np.sum(self.counts[:, :3] * jumps, axis=1)
        t = np.sum(self.counts[:, 3:] * jumps, axis=1)
        vertex = log_star(s, t).mean()
        edge = -self.alpha / 4 * (
            np.log1p(-a**3) + 3*np.log1p(-a*a*b)
            + 3*np.log1p(-a*b*b) + np.log1p(-b**3))
        return float(vertex + edge)

    def objective(self, x):
        mass, asymmetry = x
        return self.evaluate(mass*(1-asymmetry)/2,
                             mass*(1+asymmetry)/2)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--alpha', type=float, default=4.3)
    parser.add_argument('--power', type=int, default=17)
    parser.add_argument('--output', default='results/richer_asymmetric.json')
    args = parser.parse_args()
    trial = Trial(args.alpha, args.power)
    opt = differential_evolution(trial.objective, [(0.2,.9999),(0,.99)],
                                 seed=191, popsize=8, tol=1e-7)
    mass, asymmetry = opt.x
    a, b = mass*(1-asymmetry)/2, mass*(1+asymmetry)/2
    validations = [Trial(args.alpha, 20, seed).evaluate(a,b)
                   for seed in (23, 39, 57, 83)]
    result = dict(alpha=args.alpha, a=a,b=b, q=mass, asymmetry=asymmetry,
                  optimization_value=opt.fun, validation_values=validations,
                  status='exploratory QMC, not certified')
    Path(args.output).write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result), flush=True)


if __name__ == '__main__':
    main()
