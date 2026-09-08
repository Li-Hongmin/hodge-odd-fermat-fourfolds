#!/usr/bin/env python3
"""Print every project theorem's axioms, then check the entire saved transcript."""
import re
import sys
from pathlib import Path


def theorem_names():
    names = []
    for path in sorted(Path("Certificates").glob("*.lean")):
        source = path.read_text()
        namespace = re.search(r"^namespace ([\w.]+)$", source, re.M).group(1)
        names.extend(f"{namespace}.{name}" for name in
                     re.findall(r"^theorem (\w+)", source, re.M))
    assert names and len(names) == len(set(names))
    return names


names = theorem_names()
if sys.argv[1:] == ["--generate"]:
    Path("PrintAxioms.lean").write_text("import Certificates\n\n" + "\n".join(
        f"#print axioms {name}" for name in names) + "\n")
else:
    transcript = Path(sys.argv[1]).read_text()
    assert not re.search(r"sorryAx|Lean\.ofReduceBool|\berror:", transcript), transcript
    records = re.findall(
        r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|(does not depend on any axioms))",
        transcript,
    )
    assert len(records) == len(names), (len(records), len(names))
    assert {name for name, _, _ in records} == set(names), "Missing or unexpected theorem output"
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    for name, dependencies, _ in records:
        found = set(filter(None, re.split(r"[,\s]+", dependencies.strip())))
        assert found <= allowed, (name, found)
    print(f"AXIOMS: PASS; complete output for all {len(names)} declared project theorems; standard axioms only")
