"""Exercise the audit gate with isolated Lean fixtures, never imported by SatUpper."""
import unittest

from verify import ROOT, audit_command, parse_audit, run


class AuditGateTests(unittest.TestCase):
    def lean_audit(self, declarations, names):
        path = ROOT / '.lake' / 'AuditGateFixture.lean'
        path.write_text('import Lean\nimport Lean.Util.CollectAxioms\n\n' +
                        declarations + '\n' + audit_command(names))
        return run('env', 'lean', str(path))

    def test_accepts_kernel_theorem(self):
        names = ['AuditFixture.clean']
        output = self.lean_audit(
            'theorem AuditFixture.clean : True := True.intro', names)
        roots, axioms = parse_audit(output, names)
        self.assertEqual(roots, names)
        self.assertEqual(axioms, set())

    def test_rejects_transitive_extra_axiom(self):
        names = ['AuditFixture.clean', 'AuditFixture.contaminated']
        output = self.lean_audit('''
axiom AuditFixture.forbidden : True
def AuditFixture.intermediary : True := AuditFixture.forbidden
theorem AuditFixture.clean : True := True.intro
theorem AuditFixture.contaminated : True := AuditFixture.intermediary
''', names)
        self.assertIn('AUDIT_AXIOM AuditFixture.forbidden', output)
        with self.assertRaisesRegex(SystemExit, 'Unexpected axioms'):
            parse_audit(output, names)

    def test_rejects_missing_theorem(self):
        with self.assertRaisesRegex(SystemExit, 'Missing kernel theorem'):
            self.lean_audit('', ['AuditFixture.missing'])

    def test_rejects_incomplete_output(self):
        with self.assertRaisesRegex(SystemExit, 'incomplete'):
            parse_audit('AUDIT_ROOT AuditFixture.clean\n', ['AuditFixture.clean'])

    def test_rejects_non_theorem_root(self):
        with self.assertRaisesRegex(SystemExit, 'Missing kernel theorem'):
            self.lean_audit('def AuditFixture.notTheorem : Nat := 0',
                            ['AuditFixture.notTheorem'])


if __name__ == '__main__':
    unittest.main()
