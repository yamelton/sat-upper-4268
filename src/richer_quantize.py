"""Compress an exploratory paired population into an admissible rational law."""

import argparse
import json
from pathlib import Path

import numpy as np


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--input',default='results/richer_population.npz')
    parser.add_argument('--atoms',type=int,nargs='+',default=[4,8,12,16])
    parser.add_argument('--digits',type=int,default=5)
    args = parser.parse_args()
    population = np.load(args.input)['pairs'].reshape(-1)
    for atoms in args.atoms:
        if atoms % 2:
            raise ValueError('Use an even number of marginal atoms')
        support = np.round(np.quantile(population,(np.arange(atoms)+.5)/atoms),args.digits)
        # Opposite quantiles provide explicit inner laws. Admissibility is
        # checked after decimal rounding, rather than assumed from sampling.
        pairs = np.stack((support[:atoms//2],support[:atoms//2-1:-1]),axis=1)
        denominator = 10**args.digits
        numerators = np.rint(pairs*denominator).astype(np.int64)
        if np.any(numerators < 0) or np.any(numerators.sum(axis=1) > denominator):
            raise ArithmeticError('Quantile compression did not preserve admissibility')
        result = dict(atoms=atoms,weight=f'1/{atoms}',support=support.tolist(),
                      pairs=pairs.tolist(),source=args.input,
                      status='exploratory trial parameters; no bound certified by this file')
        target = Path(f'results/richer_quantile_{atoms}.json')
        target.write_text(json.dumps(result,indent=2)+'\n')
        print(str(target),flush=True)


if __name__ == '__main__':
    main()
