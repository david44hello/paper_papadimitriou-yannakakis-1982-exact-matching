"""Check the axioms of every paper claim declaration and expose their explicit literature hypotheses."""
from pathlib import Path
import argparse
import csv
import json
import re
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[1]
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
AXIOMS = re.compile(r"^'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", re.M)
INPUTS = re.compile(r"CHECK_INPUTS\|([^|\n]+)\|([^|\n]*)\|END")
LABELS = {
    "KI04_Cor_7_4": "[KI04] Corollary 7.4",
    "A26_MainTheorem": "[A26] Theorem 1.1 (UNREFEREED)",
    "O26_Thm_1_1": "[O26] Theorem 1.1 (UNREFEREED)",
}


def read_claims():
    with (ROOT / "CLAIM_MAP.tsv").open() as source:
        return list(csv.DictReader(source, delimiter="\t"))


def row_decls(row):
    val = row["lean_decl"].strip()
    if not val or val == "NONE":
        return []
    return val.split()


def check_axioms(names, allow_sorry=False):
    probe = [
        "import ExactMatching",
        "import Lean",
        "set_option pp.universes false",
        (ROOT / "scripts/audit_inputs.lean.inc").read_text(),
    ]
    for name in names:
        probe.extend([f"#check {name}", f"#print axioms {name}", f"run_cmd ExactMatchingAudit.report ``{name}"])
    with tempfile.TemporaryDirectory() as scratch:
        source = Path(scratch) / "ClaimTypes.lean"
        source.write_text("\n".join(probe) + "\n")
        result = subprocess.run(
            ["lake", "env", "lean", "-j1", str(source)],
            cwd=ROOT,
            check=True,
            stdout=subprocess.PIPE,
            text=True,
        )
    print(result.stdout, end="")
    entries = AXIOMS.findall(result.stdout)
    if [name for name, _ in entries] != names:
        raise ValueError("Lean did not report exactly the requested declarations in order")
    axioms = {name: sorted(s.strip() for s in items.split(",") if s.strip()) for name, items in entries}
    permitted = STANDARD | ({"sorryAx"} if allow_sorry else set())
    for name, deps in axioms.items():
        if set(deps) - permitted:
            raise ValueError(f"{name} uses additional axioms: {deps}")
    checked = INPUTS.findall(result.stdout)
    if [name for name, _ in checked] != names:
        raise ValueError("Lean did not report the literature inputs for every declaration")
    inputs = {
        name: sorted(v.removeprefix("ExactMatching.") for v in values.split(",") if v)
        for name, values in checked
    }
    return axioms, inputs


def report(claims):
    lines = [
        "# Paper claim audit",
        "",
        "Every formalized declaration below depends strictly on Lean's three standard axioms "
        "(`propext`, `Classical.choice`, `Quot.sound`), with zero custom `axiom` declarations. "
        "Cited external results (`KI04_Cor_7_4`, `A26_MainTheorem`, `O26_Thm_1_1`) enter solely as "
        "explicit hypotheses of the theorems that use them, verified mechanically below.",
        "",
        "| Claim ID | Paper ref | Plain name | Status | Lean declaration | Cited hypotheses |",
        "|---|---|---|---|---|---|",
    ]
    for row in claims:
        decls = row_decls(row)
        targets = ", ".join(f"`{name}`" for name in decls) if decls else "—"
        lines.append(
            f"| `{row['claim_id']}` | {row['paper_ref']} | {row['plain_name']} | "
            f"{row['status']} | {targets} | {row['cited_hypotheses']} |"
        )
    return "\n".join(lines) + "\n"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true", help="write the checked audit files")
    parser.add_argument("--allow-sorry", action="store_true", help="allow sorryAx during work-in-progress")
    options = parser.parse_args()
    claims = read_claims()
    if not claims or len({row["claim_id"] for row in claims}) != len(claims):
        raise ValueError("The paper map must have a distinct claim_id for each row")
    names = sorted({name for row in claims for name in row_decls(row)})
    if not names:
        raise ValueError("Empty Lean target list")
    axioms, inputs = check_axioms(names, allow_sorry=options.allow_sorry)
    if not options.allow_sorry:
        for row in claims:
            decls = row_decls(row)
            if row["status"].startswith("PROVED") != bool(decls):
                if row["status"] != "CITED":
                    raise ValueError(f"Inconsistent target list for {row['claim_id']}")
            if row["status"].startswith("PROVED"):
                actual = {LABELS.get(code, code) for name in decls for code in inputs[name]}
                expected = (
                    {s.strip() for s in row["status"].removeprefix("PROVED GIVEN ").split(",")}
                    if row["status"].startswith("PROVED GIVEN ")
                    else set()
                )
                if actual != expected:
                    raise ValueError(f"{row['claim_id']}: literature inputs {actual} differ from {expected}")
    products = {
        "CLAIMS.json": json.dumps({"paper": claims, "axioms": axioms, "inputs": inputs}, indent=2, ensure_ascii=False)
        + "\n",
        "AUDIT.md": report(claims),
    }
    for filename, content in products.items():
        path = ROOT / filename
        if options.write:
            path.write_text(content)
        elif path.read_text() != content:
            raise ValueError(f"{filename} differs from the checked result")
    print(f"Checked {len(names)} Lean declarations against the three permitted standard axioms.")


if __name__ == "__main__":
    main()
