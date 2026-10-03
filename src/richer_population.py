"""Exploratory admissible random survey trial laws; no numerical certification.

At energetic parameter y=infinity, let an inner field law have hard masses
(p_plus, p_minus), with p_plus+p_minus <= 1, and remaining mass at zero.
A random literal sign picks R from those two masses. For independent copies,
W=R1*R2, S=sum_{j<=Pois(3 alpha/2)} -log(1-W_j), and T an independent copy.
The variational functional is
 E log(exp(-S)+exp(-T)-exp(-S-T)) - 2 alpha E log(1-R1*R2*R3).
Only the marginal law of R enters; paired populations preserve admissibility.

The population iteration below is merely a useful way to choose a trial law.
Its convergence/fixed point is not required by the interpolation inequality.
Monte Carlo estimates and standard errors are exploratory, not certificates.
"""

import argparse
import json
from pathlib import Path

import numpy as np


def poisson_logs(rng, population, alpha, n):
    """Draw compound-Poisson log-products using independent incoming fields."""
    counts = rng.poisson(1.5 * alpha, n)
    total = int(counts.sum())
    left = population[rng.integers(len(population), size=total)]
    right = population[rng.integers(len(population), size=total)]
    contributions = -np.log1p(-left * right)
    return np.bincount(np.repeat(np.arange(n), counts), weights=contributions,
                       minlength=n)


def log_star(s, t):
    low = np.minimum(s, t)
    high = np.maximum(s, t)
    return -low + np.log1p(np.exp(-(high - low)) - np.exp(-high))


def iterate(alpha, pairs=100_000, iterations=100, seed=2718):
    rng = np.random.default_rng(seed)
    population = np.full(2 * pairs, 0.424)
    history = []
    for iteration in range(iterations):
        s = poisson_logs(rng, population, alpha, pairs)
        t = poisson_logs(rng, population, alpha, pairs)
        logg = log_star(s, t)
        plus = np.exp(-s - logg) * (-np.expm1(-t))
        minus = np.exp(-t - logg) * (-np.expm1(-s))
        if not np.all(plus + minus <= 1 + 2e-14):
            raise ArithmeticError("Invalid trial survey")
        population = np.concatenate((plus, minus))
        if iteration % 10 == 0 or iteration == iterations - 1:
            row = dict(iteration=iteration + 1, mean=float(population.mean()),
                       std=float(population.std()),
                       zero_fraction=float((population == 0).mean()))
            history.append(row)
            print(json.dumps(row), flush=True)
    return np.stack((plus, minus), axis=1), history


def estimate(alpha, pairs, samples=1_000_000, batch=100_000, seed=314159):
    population = np.asarray(pairs).reshape(-1)
    rng = np.random.default_rng(seed)
    v_sum = v_sq = e_sum = e_sq = 0.0
    used = 0
    while used < samples:
        n = min(batch, samples - used)
        s = poisson_logs(rng, population, alpha, n)
        t = poisson_logs(rng, population, alpha, n)
        v = log_star(s, t)
        r = population[rng.integers(len(population), size=(3, n))]
        e = -2 * alpha * np.log1p(-r.prod(axis=0))
        v_sum += v.sum()
        v_sq += np.dot(v, v)
        e_sum += e.sum()
        e_sq += np.dot(e, e)
        used += n
    vertex, edge = v_sum / samples, e_sum / samples
    se = np.sqrt(max(0, v_sq / samples - vertex**2) / samples
                 + max(0, e_sq / samples - edge**2) / samples)
    return dict(alpha=alpha, samples=samples, seed=seed, vertex=vertex,
                edge=edge, functional=vertex + edge, standard_error=se,
                status="exploratory Monte Carlo, not certified")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--alpha', type=float, default=4.28)
    parser.add_argument('--pairs', type=int, default=100_000)
    parser.add_argument('--iterations', type=int, default=100)
    parser.add_argument('--samples', type=int, default=2_000_000)
    parser.add_argument('--seed', type=int, default=2718)
    parser.add_argument('--output', default='results/richer_population')
    args = parser.parse_args()
    pairs, history = iterate(args.alpha, args.pairs, args.iterations, args.seed)
    prefix = Path(args.output)
    prefix.parent.mkdir(parents=True, exist_ok=True)
    np.savez_compressed(str(prefix) + '.npz', pairs=pairs)
    result = dict(trial_alpha=args.alpha, pair_count=args.pairs,
                  iterations=args.iterations, population_seed=args.seed,
                  history=history,
                  estimate=estimate(args.alpha, pairs, samples=args.samples))
    Path(str(prefix) + '.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result['estimate']), flush=True)


if __name__ == '__main__':
    main()
