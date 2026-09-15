#!/usr/bin/env bash
# Run after `lake update` and `lake exe cache get`.
set -euo pipefail
cd "$(dirname "$0")"
python3 tools/generate_data.py --check
lake build
mkdir -p checks
lake env lean Audit.lean | tee checks/lean_axioms.txt
python3 - <<'PY'
import re
from pathlib import Path
text = Path('checks/lean_axioms.txt').read_text()
blocks = re.findall(r'depends on axioms:\s*\[([^\]]*)\]', text)
if len(blocks) != 1:
    raise SystemExit('Expected the certificate axiom report; inspect Audit.lean output.')
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
for block in blocks:
    used = {name.strip() for name in block.split(',') if name.strip()}
    if used - allowed:
        raise SystemExit(f'Unexpected axiom dependencies: {sorted(used - allowed)}')
print('PASS: only the standard propext/Classical.choice/Quot.sound axioms appear.')
Path('checks/lean_build_passed.txt').write_text(
    'PASS: lake build; Audit.lean; standard-axiom check.\n')
PY
