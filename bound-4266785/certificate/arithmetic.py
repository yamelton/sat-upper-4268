"""Exact arithmetic used by the independent 4.266785 certificate.

The arithmetic functions are retained verbatim from the beta-law certificate
library; exploratory search code and unrelated candidate results are omitted.
"""
from fractions import Fraction as F
from decimal import Decimal, localcontext
import math

def complement_moments(moments):
    """Binomial transform; high precision or exact arithmetic is essential."""
    work = list(moments)
    transformed = [work[0]]
    while len(work) > 1:
        work = [x-y for x, y in zip(work, work[1:])]
        transformed.append(work[0])
    return transformed


def correction_tail(k, a, b, moment, index):
    """Upper bound on sum_{h>=index} m_h^k/h for a beta(a,b) law.

    m_h <= m_index ((a+b+index)/(a+b+h))^b for h>=index.
    Bound 1/h by (a+b+index)/(index*(a+b+h)), then bound
    the decreasing sum by its first term plus its integral.
    The resulting bound only uses rational operations.
    """
    return moment**k/index*(1+(a+b+index)/(k*b))


def ceil_div(numerator, denominator):
    return -(-numerator//denominator)


def exp_bounds_taylor(x, final_bits, guard_bits=64):
    """Exact dyadic enclosure of exp(x), x<=0, using a positive series.

    Write -x=2^s*y with 0<=y<=1/2. Enclose exp(y) by its positive
    Taylor sum through N and a tail at most twice term N+1. Take the
    reciprocal and square s times, rounding outwards at every step.
    The precision budget affects tightness, never enclosure validity.
    """
    x = F(x)
    if x > 0 or final_bits < 1:
        raise ValueError('Expected nonpositive exponent and positive precision')
    if x == 0:
        return (1 << final_bits,)*2
    y, squarings = -x, 0
    while y > F(1, 2):
        y /= 2
        squarings += 1
    bits = final_bits+2*squarings+guard_bits+math.ceil(math.log2(final_bits+2))
    scale = 1 << bits
    term_lo = term_hi = sum_lo = sum_hi = scale
    index = 0
    while True:
        index += 1
        denominator = y.denominator*index
        term_lo = term_lo*y.numerator//denominator
        term_hi = ceil_div(term_hi*y.numerator, denominator)
        sum_lo += term_lo
        sum_hi += term_hi
        if term_hi <= 1:
            next_hi = ceil_div(term_hi*y.numerator, y.denominator*(index+1))
            sum_hi += 2*next_hi
            break
    lo, hi = scale**2//sum_hi, ceil_div(scale**2, sum_lo)
    for _ in range(squarings):
        lo, hi = lo**2//scale, ceil_div(hi**2, scale)
    divisor = 1 << (bits-final_bits)
    return lo//divisor, ceil_div(hi, divisor)


def scaled_power_bounds(lower, upper, power, scale):
    denominator = scale**(power-1)
    return lower**power//denominator, ceil_div(upper**power, denominator)


def complement_bounds(lower, upper, scale):
    """Exact interval binomial transform, intersected with [0,1]."""
    transformed_lower, transformed_upper = [], []
    while lower:
        lo, hi = max(0, lower[0]), min(scale, upper[0])
        if not 0 <= lo <= hi <= scale:
            raise ArithmeticError('Invalid Hausdorff moment enclosure')
        transformed_lower.append(lo)
        transformed_upper.append(hi)
        lower, upper = ([x-y for x, y in zip(lower, upper[1:])],
                        [x-y for x, y in zip(upper, lower[1:])])
    return transformed_lower, transformed_upper


def rational(x):
    with localcontext() as ctx:
        ctx.prec = 45
        display = str(Decimal(x.numerator) / Decimal(x.denominator))
    return {"exact": str(x), "decimal_for_display": display}
