"""Independent checks of the combinatorics, finite-temperature bounds and arithmetic."""
import itertools
import json
import math
from fractions import Fraction as F
from pathlib import Path
import unittest
import mpmath as mp
import numpy as np

from src.certificate import exp_bounds, log_bounds
from src.factorized import functional


class WitnessChecks(unittest.TestCase):
    def test_interpolation_derivative_on_arbitrary_joint_measures(self):
        # Enumerate the *unexpanded* derivative for a joint Gibbs measure on
        # two spins and two state labels. Fields at repeated state labels are
        # shared. This probes the sign and randomness placement independently
        # of the cubic identity used in the written proof.
        rng = np.random.default_rng(1729)
        spins = np.array(list(itertools.product((-1, 1), repeat=2)))
        for beta, q in ((.7, .4), (2., .848), (5., .9)):
            joint = rng.random((4, 2))
            joint /= joint.sum()
            spin_mass, state_mass = joint.sum(axis=1), joint.sum(axis=0)
            lam = -math.expm1(-beta)
            cavity = [((1+math.tanh(x))/2, p)
                      for x, p in [(-beta, q/2), (0., 1-q), (beta, q/2)]]
            arrays = [(np.array([x[0] for x in pair]), math.prod(x[1] for x in pair))
                      for pair in itertools.product(cavity, repeat=2)]
            clause = 0.
            for variables in itertools.product(range(2), repeat=3):
                for signs in itertools.product((-1, 1), repeat=3):
                    bad = np.all(spins[:, variables] == signs, axis=1)
                    clause += math.log1p(-lam * (spin_mass @ bad))/64
            site = 0.
            for variable, sign in itertools.product(range(2), (-1, 1)):
                bad = spins[:, variable] == sign
                for (p1, w1), (p2, w2) in itertools.product(arrays, repeat=2):
                    forbidden = (joint[bad, :].sum(axis=0) @ (p1*p2))
                    site += w1*w2*math.log1p(-lam*forbidden)/4
            edge = 0.
            for (p1, w1), (p2, w2), (p3, w3) in itertools.product(arrays, repeat=3):
                edge += w1*w2*w3*math.log1p(-lam*(state_mass @ (p1*p2*p3)))
            self.assertLessEqual(clause-3*site+2*edge, 1e-12)

    def test_warning_union_by_enumeration(self):
        q = F(106, 125)
        w = q * q / 4
        for i, j in itertools.product(range(4), repeat=2):
            probability = F(0)
            for active in itertools.product((0, 1), repeat=i+j):
                if not any(active[:i]) or not any(active[i:]):
                    count = sum(active)
                    probability += w ** count * (1-w) ** (i+j-count)
            self.assertEqual(probability, (1-w)**i + (1-w)**j - (1-w)**(i+j))

    def test_local_finite_temperature_bounds(self):
        # Enumerate actual cavity-field assignments, not warning-count formulas.
        for beta, q, m in itertools.product((1., 3., 7.), (.2, .848), (.2, .7)):
            states = [(x, p) for x, p in [(-beta, q/2), (0., 1-q), (beta, q/2)]]
            cavity = [((1+math.tanh(x))/2, p) for x, p in states]
            edge_moment = 0.
            for choices in itertools.product(cavity, repeat=3):
                value = 1 + math.expm1(-beta) * math.prod(x[0] for x in choices)
                edge_moment += math.prod(x[1] for x in choices) * value**m
            self.assertGreaterEqual(edge_moment + 1e-14, (1-q**3/8)*2**(-m))
            messages = [(1 + math.expm1(-beta)*p1*p2, w1*w2)
                        for p1, w1 in cavity for p2, w2 in cavity]
            for i, j in ((0, 0), (1, 0), (1, 1), (2, 1), (0, 3)):
                actual = 0.
                for choices in itertools.product(messages, repeat=i+j):
                    z = math.prod(x[0] for x in choices[:i]) + math.prod(x[0] for x in choices[i:])
                    actual += math.prod(x[1] for x in choices) * z**m
                a = 1-q*q/4
                g = a**i + a**j - a**(i+j)
                upper = (math.log(g) + math.exp(-m*beta)/g + m*math.log(2)
                         + m*(i+j)*math.log1p(2*math.exp(-beta)))
                self.assertLessEqual(math.log(actual), upper + 1e-12)

    def test_rational_enclosures_against_high_precision(self):
        mp.mp.dps = 90
        for x in [F(1, 1000000), F(7, 13), F(1), F(2), F(13, 3), F(1001)]:
            lo, hi = log_bounds(x)
            reference = mp.log(mp.mpf(x.numerator)/x.denominator)
            self.assertLessEqual(mp.mpf(lo.numerator)/lo.denominator, reference)
            self.assertGreaterEqual(mp.mpf(hi.numerator)/hi.denominator, reference)
        for x in [F(-20), F(-6513, 500), F(-1, 3), F(0), F(1, 3), F(20)]:
            lo, hi = exp_bounds(x)
            reference = mp.exp(mp.mpf(x.numerator)/x.denominator)
            self.assertLessEqual(mp.mpf(lo.numerator)/lo.denominator, reference)
            self.assertGreaterEqual(mp.mpf(hi.numerator)/hi.denominator, reference)

    def test_saved_certificate_against_independent_sum(self):
        mp.mp.dps = 75
        for density in ('4.342', '4.341012'):
            with self.subTest(density=density):
                data = json.loads(Path(f'results/certificate_{density}.json').read_text())
                def value(key):
                    r = F(data[key]['exact'])
                    return mp.mpf(r.numerator)/r.denominator
                alpha, q, m = map(value, ['alpha', 'q', 'm'])
                y = mp.mpf(data['y'])
                w = q*q/4
                a = 1-w
                rate = 3*alpha/2
                p = [mp.exp(-rate)*rate**i/mp.factorial(i) for i in range(61)]
                vertex = mp.fsum(p[i]*p[j]*mp.log(a**i+a**j-a**(i+j))
                                 for i in range(61) for j in range(61))
                psi = vertex-2*alpha*mp.log(1-q**3/8)
                actual = (psi + mp.exp(-y+3*alpha*w/a) + m*(1+2*alpha)*mp.log(2)
                          + 6*alpha*m*mp.exp(-y))
                self.assertLess(actual, value('scaled_free_entropy_upper'))
                self.assertLess(value('scaled_free_entropy_upper'), 0)
                # The discrepancy should be the dropped (negative) Poisson tail.
                self.assertLess(value('scaled_free_entropy_upper')-actual, mp.mpf('1e-11'))

    def test_binomial_computation_matches_zero_conflict_limit(self):
        alpha, q = 4.342, .848
        mp.mp.dps = 40
        a = 1-mp.mpf(str(q))**2/4
        rate = mp.mpf(str(alpha))*3/2
        p = [mp.exp(-rate)*rate**i/mp.factorial(i) for i in range(56)]
        direct = mp.fsum(p[i]*p[j]*mp.log(a**i+a**j-a**(i+j))
                         for i in range(56) for j in range(56))
        direct -= 2*mp.mpf(str(alpha))*mp.log(1-mp.mpf(str(q))**3/8)
        self.assertAlmostEqual(functional(alpha, q, 40), float(direct), places=12)


if __name__ == '__main__':
    unittest.main()
