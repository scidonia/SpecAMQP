#!/usr/bin/env bash
# Every clause and picture a vector cites resolves in the id space, artifacts' own names included.
#
# The dispositions were checked for this and the corpus was not, which is where 163 stale
# references hid for a whole session: a vector citing `section:link-handles` names a document
# whose real clause is `links/doc:link-handles.1`, and nothing said so. The check normalises the
# artifact prefix the way the id space does, so a citation is compared on its fragment.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$root"
python3 - <<'PY'
import importlib.util, json, pathlib, sys, tempfile
spec = importlib.util.spec_from_file_location('cl', 'scripts/clause-ledger.py')
cl = importlib.util.module_from_spec(spec); spec.loader.exec_module(cl)
with tempfile.TemporaryDirectory() as td:
    g = cl.generate(pathlib.Path('spec/oasis'), pathlib.Path(td))
def refs(bucket):
    """Ids as the ledger writes them: each entry carries `ref`, prefixed with its artifact."""
    out = set()
    for c in (bucket.values() if isinstance(bucket, dict) else bucket or []):
        if isinstance(c, str): out.add(c)
        elif isinstance(c, dict):
            for k in ('ref', 'id', 'name'):
                if isinstance(c.get(k), str): out.add(c[k])
    return out
known = refs(g['clauses']) | refs(g.get('pictures') or [])
def norm(c): return c.split('#', 1)[-1]
ids = {norm(c) for c in known}
bad = []
for f in sorted(pathlib.Path('vectors').rglob('*.ndjson')):
    for i, line in enumerate(f.read_text().splitlines(), 1):
        v = json.loads(line)
        for c in v.get('clauses') or []:
            if norm(c) not in ids:
                bad.append(f"{f}:{i} {(v.get('vector') or {}).get('name') if isinstance(v.get('vector'), dict) else v.get('id') or v.get('name') or v.get('vector')} cites {c}")
if bad:
    for b in bad[:40]: print('problem: ' + b)
    print(f"check FAILED: {len(bad)} citations name nothing in the artifact; {len(ids)} ids known")
    sys.exit(1)
print(f"vector citations: all resolve against {len(ids)} clause and picture ids")
PY
echo "s0_vector_citations: PASS"
