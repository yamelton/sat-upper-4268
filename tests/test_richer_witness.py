"""Independent checks of the richer-law certificate and local estimates."""

import itertools
import json
import math
from fractions import Fraction as F
from pathlib import Path
import unittest

import mpmath as mp

from src.richer_certificate import certificate, exp_grid_bounds


class RicherWitnessChecks(unittest.TestCase):
    def test_grid_exponentials_against_high_precision(self):
        with mp.workdps(250):
            scale = 10**150
            for x in (F(-40), F(-3201, 500), F(-1, 10**16), F(0),
                      F(1, 10**16), F(3201, 500), F(40), F(100)):
                with self.subTest(x=x):
                    lo, hi = exp_grid_bounds(x, scale, 514)
                    reference = mp.exp(mp.mpf(x.numerator)/x.denominator)
                    self.assertLessEqual(mp.mpf(lo)/scale, reference)
                    self.assertGreaterEqual(mp.mpf(hi)/scale, reference)

    def test_saved_witness_against_direct_binomial_sums(self):
        # The verifier uses interval forward differences. This check instead
        # evaluates the alternating binomial formula directly at 250 digits.
        data = json.loads(Path('results/certificate_4.268.json').read_text())
        self.assertEqual(F(data['alpha']['exact']), F(1067, 250))
        self.assertEqual(data['cutoff'], 128)
        self.assertEqual(
            {F(atom['r']['exact']): F(atom['probability']['exact'])
             for atom in data['bad_mass_law']},
            {F(1, 20): F(1, 4), F(2, 5): F(1, 2), F(17, 20): F(1, 4)})
        with mp.workdps(250):
            def value(item):
                rational = F(item['exact'])
                return mp.mpf(rational.numerator)/rational.denominator

            alpha = value(data['alpha'])
            atoms = [(value(atom['r']), value(atom['probability']))
                     for atom in data['bad_mass_law']]
            moments = []
            for j in range(data['cutoff']+1):
                nu = mp.fsum(p*q*(1-r*s)**j
                             for r,p in atoms for s,q in atoms)
                moments.append(mp.exp(3*alpha/2*(nu-1)))
            vertex = mp.mpf(0)
            for k in range(1, data['cutoff']+1):
                mu = mp.fsum((-1)**j * math.comb(k,j) * moments[j]
                             for j in range(k+1))
                self.assertGreaterEqual(mu, 0)
                vertex -= mu**2/k
            edge = -2*alpha*mp.fsum(
                p*q*v*mp.log(1-r*s*t)
                for r,p in atoms for s,q in atoms for t,v in atoms)
            reference = vertex+edge
            certified = value(data['psi_upper'])
            self.assertLess(vertex, value(data['vertex_upper']))
            self.assertLess(reference, certified)
            self.assertLess(certified-reference, mp.mpf('1e-27'))
            self.assertLess(certified, -mp.mpf('0.00001'))

    def test_heterogeneous_local_estimate_by_field_enumeration(self):
        # Enumerate actual fields with different asymmetric laws at different
        # cavity positions, instead of using the moment-series functional.
        laws = ((.05, .85), (.4, .4))
        for beta in (.7, 3.):
            m = .4
            t = math.exp(-beta)
            for signs in itertools.product((-1, 1), repeat=4):
                messages, warning_rates = [], []
                for offset in (0, 2):
                    cavity, bad_masses = [], []
                    for pos, (a,b) in enumerate(laws):
                        sign = signs[offset+pos]
                        r = a if sign == 1 else b
                        cavity.append([(0., 1-r), (1., r)])
                        bad_masses.append(a if sign == 1 else b)
                    messages.append([(1-(1-t)*p1*p2, w1*w2)
                                     for (p1,w1),(p2,w2) in itertools.product(*cavity)])
                    warning_rates.append(math.prod(bad_masses))
                actual = sum(weight1*weight2*(factor1+factor2)**m
                             for (factor1,weight1),(factor2,weight2)
                             in itertools.product(*messages))
                a0, b0 = (1-w for w in warning_rates)
                g = a0+b0-a0*b0
                upper = (m*math.log(2)
                         +math.log(g+(1-g)*math.exp(-m*beta)))
                self.assertLessEqual(math.log(actual), upper+1e-13)

    def test_inadmissible_survey_is_rejected(self):
        with self.assertRaises(AssertionError):
            certificate(cutoff=2, surveys=[(F(3,5), F(3,5), F(1))])


if __name__ == '__main__':
    unittest.main()
