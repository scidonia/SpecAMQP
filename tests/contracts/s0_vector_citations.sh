#!/usr/bin/env bash
# Every clause and picture a vector cites resolves in the id space, artifacts' own names included.
#
# The dispositions were checked for this and the corpus was not, which is where 163 stale
# references hid for a whole session: a vector citing `section:link-handles` names a document
# whose real clause is `links/doc:link-handles.1`, and nothing said so. The check normalises the
# artifact prefix the way the id space does, so a citation is compared on its fragment.
#
# The second clause covers the handwritten modules, where the same class of stale reference was
# checked by nothing at all: `lean/Contracts` and `lean/Spec` cite clauses in their documentation,
# and a citation that names nothing is a reader's dead end. It admits *section-level* references
# and counts them separately, because some citations are deliberately to a whole section — the
# frame layout is transcribed from the framing doc rather than from a sentence of it — and a rule
# demanding a clause id for those would force a false precision. A reference to a section that
# does not exist still fails: the cited text must be extended by a registered id past a `.` or `/`
# boundary, so `section:link-handles` remains a failure against `links/doc:link-handles.1`.
#
# One thing neither clause can see, stated so its silence is not read as coverage: a citation that
# *resolves* but names the wrong clause. `lean/Contracts/SessionWindows.lean` carried four of
# those — the right document, the wrong sentence — and they were found by a reader comparing each
# against the artifact, not by this gate. Precision of attribution is a review property here.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$root"
python3 - <<'PYVEC'
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
PYVEC
python3 - <<'PYLEAN'
import importlib.util, pathlib, re, sys, tempfile
spec = importlib.util.spec_from_file_location('cl', 'scripts/clause-ledger.py')
cl = importlib.util.module_from_spec(spec); spec.loader.exec_module(cl)
with tempfile.TemporaryDirectory() as td:
    g = cl.generate(pathlib.Path('spec/oasis'), pathlib.Path(td))
def refs(bucket):
    out = set()
    for c in (bucket.values() if isinstance(bucket, dict) else bucket or []):
        if isinstance(c, str): out.add(c)
        elif isinstance(c, dict):
            for k in ('ref', 'id', 'name'):
                if isinstance(c.get(k), str): out.add(c[k])
    return out
ids = {c.split('#', 1)[-1] for c in refs(g['clauses']) | refs(g.get('pictures') or [])}

def resolves(cand):
    """Exact id, or a section some registered id extends past a `.` or `/` boundary."""
    if not cand:
        return False
    if cand in ids:
        return True
    return any(i.startswith(cand + '.') or i.startswith(cand + '/') for i in ids)

CITE = re.compile(r'amqp-core-[a-z0-9-]+-v1\.0-os\.xml#([A-Za-z0-9:._/+-]+)')
bad, total, sections = [], 0, 0
for root in (pathlib.Path('lean/Contracts'), pathlib.Path('lean/Spec')):
    for f in sorted(root.rglob('*.lean')):
        text = f.read_text(encoding='utf-8')
        for m in CITE.finditer(text):
            raw = m.group(1)
            total += 1
            # An id may be followed by sentence punctuation the pattern cannot exclude, since
            # ids themselves contain dots and slashes. Trim while the suffix is punctuation.
            cand = raw
            while cand and cand not in ids and cand[-1] in '.-:/':
                cand = cand[:-1]
            if resolves(cand):
                if cand not in ids:
                    sections += 1
            else:
                line = text[:m.start()].count('\n') + 1
                bad.append(f"{f}:{line} cites {raw}")
if bad:
    for b in bad[:30]: print('problem: ' + b)
    print(f"check FAILED: {len(bad)} of {total} citations in the handwritten modules name nothing")
    sys.exit(1)
print(f"handwritten citations: all {total} resolve ({sections} of them to a whole section)")
PYLEAN
echo "s0_vector_citations: PASS"
