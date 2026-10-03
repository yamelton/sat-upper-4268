"""Exact rational enclosure of the proposed 3-SAT interpolation witness.

Standard library only. Floating point is used solely to print the result.
The mathematical link to random 3-SAT is proved in notes/proof.md.
"""

from fractions import Fraction as F
from math import factorial
import argparse
import json

SCALE = 10 ** 30


def down(x):
    return F(x.numerator * SCALE // x.denominator, SCALE)


def up(x):
    return -down(-x)


def log_unit(x, terms=36):
    """Enclose log(x) for rational x in [1,2] by the atanh series."""
    assert 1 <= x <= 2
    z = (x - 1) / (x + 1)
    z2 = z * z
    power = z
    total = F(0)
    for j in range(terms):
        total += power / (2 * j + 1)
        power *= z2
    lower = 2 * total
    remainder = 2 * power / ((2 * terms + 1) * (1 - z2))
    return down(lower), up(lower + remainder)


LOG2 = log_unit(F(2))


def log_bounds(x):
    """Enclose log of any positive rational using powers-of-two reduction."""
    assert x > 0
    k = 0
    while x < 1:
        x *= 2
        k -= 1
    while x > 2:
        x /= 2
        k += 1
    lo, hi = log_unit(x)
    if k >= 0:
        return down(lo + k * LOG2[0]), up(hi + k * LOG2[1])
    return down(lo + k * LOG2[1]), up(hi + k * LOG2[0])


def exp_bounds(x, terms=120):
    """Taylor enclosure with a geometric remainder, all arithmetic exact."""
    x = F(x)
    if x < 0:
        lo, hi = exp_bounds(-x, terms)
        return down(1 / hi), up(1 / lo)
    assert x < terms + 2
    total = term = F(1)
    for j in range(1, terms + 1):
        term *= x / j
        total += term
    next_term = term * x / (terms + 1)
    remainder = next_term / (1 - x / (terms + 2))
    return down(total), up(total + remainder)


def certificate(alpha=F(2171, 500), q=F(106, 125), cutoff=32,
                beta=10 ** 8, y=20):
    """Return an exact upper bound for m times the free-entropy bound.

    Every omitted vertex summand is nonpositive. Thus dropping all signed
    degrees beyond cutoff is an upper bound, without any tail estimate.
    """
    alpha, q = F(alpha), F(q)
    assert 0 < q < 1 and alpha > 0 and 0 < y < beta
    assert cutoff >= 0
    rate = 3 * alpha / 2
    w = q * q / 4
    a = 1 - w
    c = q ** 3 / 8
    degree_weights = [rate ** i / factorial(i) for i in range(cutoff + 1)]
    powers = [a ** i for i in range(cutoff + 1)]
    # The weights below exclude exp(-2*rate), included once at the end.
    log_sum_upper = F(0)
    for i in range(cutoff + 1):
        for j in range(i, cutoff + 1):
            g = powers[i] + powers[j] - powers[i] * powers[j]
            log_upper = log_bounds(g)[1]
            assert log_upper <= 0
            multiplicity = 1 if i == j else 2
            log_sum_upper += up(multiplicity * degree_weights[i]
                                * degree_weights[j] * log_upper)
    exp_lower = exp_bounds(-2 * rate)[0]
    vertex_upper = up(exp_lower * log_sum_upper)
    edge_upper = up(-2 * alpha * log_bounds(1 - c)[0])
    psi_upper = vertex_upper + edge_upper
    m = F(y, beta)
    # Analytic error bound from finite beta and finite y, see the proof.
    # Use beta >= y so exp(-beta) <= exp(-y), avoiding huge rationals.
    conflict_error = exp_bounds(-y + 3 * alpha * w / a)[1]
    entropy_error = up(m * (1 + 2 * alpha) * LOG2[1])
    message_error = up(6 * alpha * m * exp_bounds(-y)[1])
    final_upper = psi_upper + conflict_error + entropy_error + message_error
    return dict(alpha=alpha, q=q, cutoff=cutoff, beta=beta, y=y, m=m,
                vertex_upper=vertex_upper, edge_upper=edge_upper,
                psi_upper=psi_upper, conflict_error=conflict_error,
                entropy_error=entropy_error, message_error=message_error,
                scaled_free_entropy_upper=final_upper,
                free_entropy_upper=up(final_upper / m),
                certified_negative=final_upper < 0)


def serialized(result):
    return {k: ({'exact': str(v), 'decimal_for_display': float(v)}
                if isinstance(v, F) else v) for k, v in result.items()}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--alpha', type=F, default=F(2171, 500))
    parser.add_argument('--q', type=F, default=F(106, 125))
    parser.add_argument('--cutoff', type=int, default=32)
    parser.add_argument('--beta', type=int, default=10 ** 8)
    parser.add_argument('--y', type=int, default=20)
    parser.add_argument('--output')
    args = parser.parse_args()
    result = certificate(args.alpha, args.q, args.cutoff, args.beta, args.y)
    output = json.dumps(serialized(result), indent=2) + '\n'
    if args.output:
        from pathlib import Path
        Path(args.output).write_text(output)
    print(output, end='')
    if not result['certified_negative']:
        raise SystemExit('The witness did not certify a negative value.')
