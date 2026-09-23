#!/usr/bin/env bash
# Every planner-owned file is as the manifest records it, and the manifest is what a
# planner changes when one of them moves. Regeneration is manual by design: the diff is the record — and the manifest is rebuilt from the
# *committed* state, never from the working tree, because a tree with a slice mid-edit would
# otherwise bless that slice's unreviewed bytes as the record.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$root"
python3 - <<'PY'
import hashlib, pathlib, sys
manifest = pathlib.Path('toolchain/spec-manifest.sha1').read_text().splitlines()
want = dict(l.split('  ', 1)[::-1] for l in manifest if l.strip())
# Every tree AGENTS.md names planner-owned, plus the one file of toolchain/ that is a
# contract rather than a pin record. `lean/Proofs`, `lean/Generated` and `scripts/` are
# deliberately absent: they are coder-owned, and their integrity is the trust gate's and the
# generator-fidelity gate's business rather than this manifest's. Adding `tests/contracts`
# closes a real hole: a contract script is the thing that says what the evidence means, and
# until today nothing compared its bytes to anything, which is how one was edited by a coder
# in flight and noticed only by a reviewer reading the diff.
roots = ['lean/Spec', 'lean/Contracts', 'vectors', 'ledger', 'tests/contracts']
have = {p: hashlib.sha1(pathlib.Path(p).read_bytes()).hexdigest()
        for p in ['toolchain/sources.toml']}
for r in roots:
    for f in sorted(pathlib.Path(r).rglob('*')):
        if f.is_file() and f.suffix in ('.lean', '.ndjson', '.json', '.md', '.sh', '.feature'):
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
