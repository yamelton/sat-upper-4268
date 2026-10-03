#!/usr/bin/env python3
"""Run the proof audit and independent checks; record exact tested inputs."""
import argparse
import hashlib
import json
from pathlib import Path
import platform
import subprocess
import sys
from datetime import datetime, timezone
from fractions import Fraction

ROOT = Path(__file__).resolve().parents[1]
RESULTS = ROOT / 'results'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def audited_inputs():
    return sorted((ROOT / 'lean/SatUpper').rglob('*.lean')) + [
        ROOT / 'lean' / name for name in
        ('SatUpper.lean', 'lakefile.toml', 'lake-manifest.json', 'lean-toolchain')]


def check_audit():
    report = json.loads((RESULTS / 'lean_verification.json').read_text())
    assert report['build_passed'] and report['full_threshold_theorem_verified']
    assert not report['open_obligations']
    assert set(report['axiom_union']) <= {'propext', 'Classical.choice', 'Quot.sound'}
    current = {str(p.relative_to(ROOT / 'lean')): sha(p) for p in audited_inputs()}
    assert current == report['source_sha256'], 'Lean audit is stale; rerun without --skip-lean'
    return report


def run(log, *args):
    print('Running:', ' '.join(args), flush=True)
    with (RESULTS / log).open('w') as out:
        result = subprocess.run(args, cwd=ROOT, stdout=out, stderr=subprocess.STDOUT)
    if result.returncode:
        print((RESULTS / log).read_text(), file=sys.stderr)
        raise SystemExit(result.returncode)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--skip-lean', action='store_true',
                        help='Reuse only an audit whose recorded source hashes still match')
    args = parser.parse_args()
    RESULTS.mkdir(exist_ok=True)
    # An interrupted or failed check must not leave a previous success report.
    (RESULTS / 'release-checks.json').unlink(missing_ok=True)
    if not args.skip_lean:
        run('build-and-audit.log', sys.executable, 'lean/verify.py')
    audit = check_audit()
    run('audit-gate-tests.log', sys.executable, 'lean/test_verify.py')
    run('python-tests.log', sys.executable, '-m', 'unittest', 'discover', '-s', 'tests', '-v')
    run('certificate-recomputed.log', sys.executable, 'src/richer_certificate.py',
        '--alpha', '4.268', '--cutoff', '128', '--surveys', '.05,.85,.5', '.4,.4,.5',
        '--output', 'results/certificate-recomputed.json')
    saved = json.loads((RESULTS / 'certificate_4.268.json').read_text())
    recomputed = json.loads((RESULTS / 'certificate-recomputed.json').read_text())
    assert recomputed == saved, 'Independent certificate differs from the published fixture'
    assert Fraction(recomputed['psi_upper']['exact']) <= -Fraction(1, 100000)
    paths = audited_inputs() + sorted((ROOT / 'src').glob('*.py'))
    paths += sorted((ROOT / 'tests').glob('*.py'))
    paths += [ROOT / 'requirements.txt', ROOT / 'lean/verify.py', ROOT / 'lean/test_verify.py',
              ROOT / 'lean/run.sh', ROOT / 'scripts/check.py']
    paths += sorted(RESULTS.glob('certificate_*.json'))
    report = dict(passed=True, checked_at=datetime.now(timezone.utc).isoformat(),
                  python=platform.python_version(), platform=platform.system(),
                  lean_audit_reused=args.skip_lean,
                  audited_theorems=audit['audited_theorem_count'],
                  source_sha256={str(p.relative_to(ROOT)): sha(p) for p in paths})
    (RESULTS / 'release-checks.json').write_text(json.dumps(report, indent=2) + '\n')
    print('All proof, audit-gate, numerical, and exact-certificate checks passed.')


if __name__ == '__main__':
    main()
