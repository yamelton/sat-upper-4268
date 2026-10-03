"""Build and audit every project theorem and the unconditional target endpoint.

This script is an audit driver, not a mathematical proof checker. Lean checks
the proofs. The driver rejects failed builds and any theorem dependency other
than the three standard logical axioms listed below.
"""

import json
import hashlib
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parent
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}


def run(*args):
    result = subprocess.run(['sh', 'run.sh', *args], cwd=ROOT,
                            text=True, capture_output=True)
    output = result.stdout + result.stderr
    if result.returncode:
        raise SystemExit(output)
    if "declaration uses 'sorry'" in output:
        raise SystemExit('Rejected proof placeholder:\n' + output)
    return output


def audit_command(names):
    """Lean's own collector, sharing its visited state across all roots."""
    quoted_names = ',\n    '.join('`' + name for name in names)
    return ('open Lean Elab Command in\nrun_cmd do\n' +
        '  let roots : Array Name := #[\n    ' + quoted_names + ']\n' +
        '  let env ← getEnv\n' +
        '  for name in roots do\n' +
        '    match env.checked.get.find? name with\n' +
        '    | some (.thmInfo _) => pure ()\n' +
        '    | _ => throwError "Missing kernel theorem: {name}"\n' +
        '  let (_, state) := ((roots.forM CollectAxioms.collect).run env).run {}\n' +
        '  for name in roots do\n' +
        '    liftIO <| IO.println s!"AUDIT_ROOT {name}"\n' +
        '  for name in state.axioms do\n' +
        '    liftIO <| IO.println s!"AUDIT_AXIOM {name}"\n' +
        '  liftIO <| IO.println s!"AXIOM_AUDIT_COMPLETE {roots.size}"\n\n')


def parse_audit(output, names):
    checked = re.findall(r'^AUDIT_ROOT (\S+)$', output, re.M)
    axioms = set(re.findall(r'^AUDIT_AXIOM (\S+)$', output, re.M))
    if axioms - ALLOWED_AXIOMS:
        raise SystemExit(f'Unexpected axioms in theorem dependency union: {axioms}')
    if (len(checked) != len(names) or set(checked) != set(names) or
            f'AXIOM_AUDIT_COMPLETE {len(names)}' not in output.splitlines()):
        raise SystemExit('Axiom audit incomplete:\n' + output)
    return checked, axioms


def main():
    print(run('build'), end='', flush=True)
    names = []
    sources = sorted((ROOT / 'SatUpper').rglob('*.lean'))
    for source in sources:
        text = source.read_text()
        namespaces = re.findall(r'^namespace\s+(\S+)\s*$', text, re.M)
        if len(namespaces) != 1:
            raise SystemExit(f'Update the audit parser for {source.name}: namespace layout changed')
        names.extend(namespaces[0] + '.' + name
                     for name in re.findall(r'^theorem\s+(\w+)', text, re.M))
    if len(set(names)) != len(names) or not names:
        raise SystemExit('Invalid theorem inventory')
    audit = ROOT / '.lake' / 'AxiomAudit.lean'
    audit.write_text('import SatUpper\nimport Lean.Util.CollectAxioms\n\n' +
        audit_command(names) +
        '#check @SatUpper.Formalization.linearVarianceControl\n' +
        '#check @SatUpper.Formalization.numericalEnclosure\n' +
        '#check @SatUpper.Formalization.upperBound_of_comparison\n' +
        '#check @SatUpper.GroundBound.scaled_mean_le\n' +
        'example : SatUpper.Formalization.AsymptoticComparison :=\n' +
        '  SatUpper.ModelTransfer.asymptoticComparison\n' +
        'example : SatUpper.CandidateUpperBound := SatUpper.upperBound_4268\n' +
        'example : Filter.Tendsto (fun n : ℕ =>\n' +
        '    SatUpper.satisfiabilityProbability n (1067*n/250))\n' +
        '    Filter.atTop (nhds 0) :=\n' +
        '  SatUpper.satisfiabilityProbability_4268_tendsto_zero\n' +
        '#print axioms SatUpper.upperBound_4268\n' +
        'run_cmd Lean.logInfo "ENDPOINT_CHECK_COMPLETE"\n')
    print(f'Auditing {len(names)} theorem dependencies (shared traversal)...', flush=True)
    output = run('env', 'lean', str(audit))
    (ROOT / '.lake' / 'axiom-audit.txt').write_text(output)
    checked, axioms = parse_audit(output, names)
    endpoints = [
        'SatUpper.ModelTransfer.asymptoticComparison',
        'SatUpper.upperBound_4268',
        'SatUpper.satisfiabilityProbability_4268_tendsto_zero',
    ]
    if not set(endpoints).issubset(checked) or 'ENDPOINT_CHECK_COMPLETE' not in output.splitlines():
        raise SystemExit('Unconditional endpoint check incomplete:\n' + output)
    manifest = json.loads((ROOT / 'lake-manifest.json').read_text())
    mathlib = next(p for p in manifest['packages'] if p['name'] == 'mathlib')
    report = {
        'lean_toolchain': (ROOT / 'lean-toolchain').read_text().strip(),
        'mathlib_revision': mathlib['rev'],
        'build_passed': True,
        'audited_theorem_count': len(checked),
        'allowed_axioms': sorted(ALLOWED_AXIOMS),
        'audit_report_version': 5,
        'proof_module_count': len(sources),
        'proof_source_lines': sum(len(source.read_text().splitlines()) for source in sources),
        'proof_sources': [str(source.relative_to(ROOT)) for source in sources],
        'source_sha256': {
            str(source.relative_to(ROOT)): hashlib.sha256(source.read_bytes()).hexdigest()
            for source in sources + [ROOT / 'SatUpper.lean', ROOT / 'lakefile.toml',
                                     ROOT / 'lake-manifest.json', ROOT / 'lean-toolchain']
        },
        'audit_method': 'Lean.CollectAxioms.collect with shared visited state across all theorem roots',
        'audited_theorems': sorted(checked),
        'axiom_union': sorted(axioms),
        'full_threshold_theorem_verified': True,
        'kernel_checked_endpoints': endpoints,
        'discharged_obligations': {
            'SatUpper.Formalization.LinearVarianceControl': 'SatUpper.Formalization.linearVarianceControl',
            'SatUpper.Formalization.NumericalEnclosure': 'SatUpper.Formalization.numericalEnclosure',
            'SatUpper.Formalization.AsymptoticComparison': 'SatUpper.ModelTransfer.asymptoticComparison',
        },
        'open_obligations': [],
        'scope': 'Unconditional limit: satisfiability probability tends to zero for floor(1067*n/250) iid uniform ordered legal signed 3-clauses on n variables. Variables within each clause are distinct; repeated clauses are allowed.',
    }
    destination = ROOT.parent / 'results' / 'lean_verification.json'
    destination.write_text(json.dumps(report, indent=2) + '\n')
    print(f'{len(checked)} theorem dependencies audited: only standard logical axioms.')
    print('The unconditional 4.268 threshold upper-bound theorem and its exact endpoint are verified.')
    print('Report: results/lean_verification.json')


if __name__ == '__main__':
    main()
