#!/usr/bin/env bash
# Every planner-owned file is as the manifest records it, and the manifest is what a
# planner changes when one of them moves. Regeneration is manual by design: the diff is the record.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$root"
python3 - <<'PY'
import hashlib, pathlib, sys
manifest = pathlib.Path('toolchain/spec-manifest.sha1').read_text().splitlines()
want = dict(l.split('  ', 1)[::-1] for l in manifest if l.strip())
roots = ['lean/Spec', 'lean/Contracts', 'vectors', 'ledger']
have = {}
for r in roots:
    for f in sorted(pathlib.Path(r).rglob('*')):
        if f.is_file() and f.suffix in ('.lean', '.ndjson', '.json', '.md'):
            have[str(f)] = hashlib.sha1(f.read_bytes()).hexdigest()
changed = [p for p in want if p in have and have[p] != want[p]]
added   = [p for p in have if p not in want]
gone    = [p for p in want if p not in have]
for p in changed: print(f'problem: {p} differs from the manifest — a planner-owned file moved')
for p in added:   print(f'problem: {p} is not in the manifest — new planner-owned file')
for p in gone:    print(f'problem: {p} is in the manifest but absent from the tree')
if changed or added or gone:
    print(f'check FAILED: {len(changed)} changed, {len(added)} added, {len(gone)} gone')
    sys.exit(1)
print(f'planner-owned files: {len(have)} as recorded')
PY
echo "s0_spec_manifest: PASS"
