#!/usr/bin/env python3
"""Build the paper with PDFLaTeX/BibTeX and reject unresolved references."""
import hashlib
import json
from pathlib import Path
import shutil
import subprocess

ROOT = Path(__file__).resolve().parents[1]
BUILD = ROOT / 'build/paper'


def main():
    BUILD.mkdir(parents=True, exist_ok=True)
    sources = sorted((ROOT / 'paper').glob('*.tex')) + sorted((ROOT / 'paper').glob('*.bib'))
    for path in sources:
        shutil.copy2(path, BUILD / path.name)
    commands = [
        ['pdflatex', '-interaction=nonstopmode', '-halt-on-error', 'main.tex'],
        ['bibtex', 'main'],
        ['pdflatex', '-interaction=nonstopmode', '-halt-on-error', 'main.tex'],
        ['pdflatex', '-interaction=nonstopmode', '-halt-on-error', 'main.tex'],
    ]
    (ROOT / 'results/paper-checks.json').unlink(missing_ok=True)
    with (ROOT / 'results/paper-build.log').open('w') as log:
        for command in commands:
            result = subprocess.run(command, cwd=BUILD, stdout=log, stderr=subprocess.STDOUT)
            if result.returncode:
                raise SystemExit('Paper build failed; see results/paper-build.log')
    log = (BUILD / 'main.log').read_text()
    for marker in ['undefined references', 'undefined citations', 'Rerun to get', 'Overfull \\hbox', 'Overfull \\vbox']:
        if marker in log:
            raise SystemExit(f'Paper needs attention: {marker}; see build/paper/main.log')
    report = {'passed': True, 'source_sha256': {
        str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in sources},
        'pdf_sha256': hashlib.sha256((BUILD / 'main.pdf').read_bytes()).hexdigest()}
    (ROOT / 'results/paper-checks.json').write_text(json.dumps(report, indent=2) + '\n')
    print('Paper built: build/paper/main.pdf')


if __name__ == '__main__':
    main()
