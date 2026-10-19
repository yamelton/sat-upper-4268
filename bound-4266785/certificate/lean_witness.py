"""Untrusted witness generation helpers; every result requires kernel checks."""
from fractions import Fraction as F

def floor(x):
    return x.numerator // x.denominator

def ceil(x):
    return -((-x.numerator) // x.denominator)

def transform(rows):
    rows = list(rows)
    result = []
    while rows:
        result.append(rows[0])
        rows = [(a[0]-b[1], a[1]-b[0]) for a, b in zip(rows, rows[1:])]
    return result

def taylor_bounds(x, scale, terms, squarings):
    """Exact implementation of SatKUpper.TaylorExponential.bounds."""
    y = -x / (1 << squarings)
    assert 0 <= y <= 1
    tl = tu = sl = su = scale
    for n in range(1, terms+1):
        tl = floor(tl*y/n)
        tu = ceil(tu*y/n)
        sl += tl
        su += tu
    upper = su + 2*ceil(tu*y/(terms+1))
    lo, hi = F(scale, upper), F(scale, sl)
    for _ in range(squarings):
        lo = F(floor(lo*lo*scale), scale)
        hi = F(ceil(hi*hi*scale), scale)
    return lo, hi

def integer(n):
    return ('-' if n < 0 else '') + hex(abs(n))

def array(name, rows, pairs=True):
    typ = 'ℤ × ℤ' if pairs else 'ℕ'
    entries = ['(' + integer(a) + ', ' + integer(b) + ')' for a, b in rows] if pairs else [integer(a) for a in rows]
    chunks = [entries[i:i+128] for i in range(0, len(entries), 128)]
    result = ''
    names = []
    for i, chunk in enumerate(chunks):
        part = name+'Part'+str(i)
        names.append(part)
        result += 'def '+part+' : Array ('+typ+') := ⟨[\n  '+',\n  '.join(chunk)+'\n]⟩\n\n'
    # Array.append repeatedly pushes into its left argument during kernel
    # reduction. Assemble the underlying lists instead, in linear time.
    result += 'def '+name+' : Array ('+typ+') := ⟨'+' ++ '.join(n+'.toList' for n in names)+'⟩\n\n'
    return result
