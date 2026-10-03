#!/usr/bin/env python3
"""Package checked software and arXiv sources using explicit inclusion lists."""
import hashlib
import json
from pathlib import Path
import shutil
import zipfile

ROOT = Path(__file__).resolve().parents[1]
DIST = ROOT / 'dist'


def check_report(name):
    report = json.loads((ROOT / 'results' / name).read_text())
    assert report['passed'], f'{name} did not pass'
    for path, expected in report['source_sha256'].items():
        assert hashlib.sha256((ROOT / path).read_bytes()).hexdigest() == expected, f'Stale check: {path}'
    return report


def archive(name, paths):
    with zipfile.ZipFile(DIST / name, 'w', compression=zipfile.ZIP_DEFLATED) as out:
        for source, target in sorted(paths, key=lambda pair: pair[1]):
            out.write(source, target)


def main():
    check_report('release-checks.json')
    paper = check_report('paper-checks.json')
    pdf = ROOT / 'build/paper/main.pdf'
    assert hashlib.sha256(pdf.read_bytes()).hexdigest() == paper['pdf_sha256']
    DIST.mkdir(exist_ok=True)
    software = [ROOT / p for p in ['README.md', 'LICENSE', 'NOTICE', 'CITATION.cff',
        'requirements.txt', '.zenodo.json', 'scripts/check.py', 'lean/run.sh',
        'lean/verify.py', 'lean/test_verify.py', 'lean/lakefile.toml',
        'lean/lake-manifest.json', 'lean/lean-toolchain', 'lean/SatUpper.lean',
        'publication/source-manifest.json', 'publication/AUDIT.md',
        'results/lean_verification.json', 'results/release-checks.json',
        'results/build-and-audit.log', 'results/audit-gate-tests.log', 'results/python-tests.log']]
    software += sorted((ROOT / 'lean/SatUpper').rglob('*.lean'))
    software += sorted((ROOT / 'src').glob('*.py')) + sorted((ROOT / 'tests').glob('*.py'))
    software += sorted((ROOT / 'results').glob('certificate_*.json'))
    archive('sat-upper-4268-software-v1.0.0.zip',
            [(p, str(p.relative_to(ROOT))) for p in software])
    tex = sorted((ROOT / 'paper').glob('*.tex')) + sorted((ROOT / 'paper').glob('*.bib'))
    archive('sat-upper-4268-arxiv.zip', [(p, p.name) for p in tex] +
            [(ROOT / 'build/paper/main.bbl', 'main.bbl')])
    shutil.copy2(pdf, DIST / 'sat-upper-4268.pdf')
    artifacts = sorted(p for p in DIST.iterdir() if p.suffix in {'.zip', '.pdf'})
    (DIST / 'SHA256SUMS').write_text(''.join(
        hashlib.sha256(p.read_bytes()).hexdigest() + '  ' + p.name + '\n' for p in artifacts))
    print('Prepared software archive, arXiv source archive, PDF, and SHA256SUMS in dist/.')


if __name__ == '__main__':
    main()
