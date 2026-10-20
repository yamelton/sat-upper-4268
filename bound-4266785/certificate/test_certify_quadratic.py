"""Regression check for exact certificates larger than Python's digit limit."""
from pathlib import Path
import subprocess
import sys
import unittest


class CertificateSerializationTest(unittest.TestCase):
    @unittest.skipUnless(hasattr(sys, 'set_int_max_str_digits'), 'Python 3.11+ limit')
    def test_large_rational_roundtrip_with_default_limit(self):
        result = subprocess.run(
            [sys.executable, '-X', 'int_max_str_digits=4300', '-c', '''
import sys
assert sys.get_int_max_str_digits() == 4300
import certify_quadratic as cert
from fractions import Fraction
import json
value = Fraction((1 << 31000) - 1, 1 << 30999)
record = json.loads(json.dumps(cert.lib.rational(value)))
assert len(record['exact'].split('/')[0]) > 4300
assert Fraction(record['exact']) == value
'''],
            cwd=Path(__file__).resolve().parent,
            capture_output=True,
            text=True,
        )
        self.assertEqual(result.returncode, 0, result.stderr)


if __name__ == '__main__':
    unittest.main()
