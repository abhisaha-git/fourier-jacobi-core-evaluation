"""Read-only supplementary audit of the fifty retained source transcriptions.

This is not a Lean proof certificate. Ordinary Lean reproduction does not
require Python or SymPy. --source additionally checks the preserved full TeX.
"""
from pathlib import Path
import argparse
import hashlib
import json
import sympy as sp


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    data_path = root / "data/region-expressions.json"
    audit = json.loads((root / "data/source-row-restorations.json").read_text(encoding="utf-8-sig"))
    data = json.loads(data_path.read_text(encoding="utf-8-sig"))
    assert hashlib.sha256(data_path.read_bytes()).hexdigest() == audit["data_sha256"]
    assert len(audit["rows"]) == len(data) == 50
    symbols = dict(zip("S t d U V P N E F G".split(), sp.symbols("S t d U V P N E F G")))
    S, t = symbols["S"], symbols["t"]
    source = None
    if args.source:
        assert hashlib.sha256(args.source.read_bytes()).hexdigest() == audit["source_sha256"]
        source = args.source.read_text(encoding="utf-8-sig")
    for i, (row, stored) in enumerate(zip(audit["rows"], data)):
        assert row["index"] == i
        assert row["central"] == stored["central"] and row["row"] == stored["row"]
        assert row["expression"] == stored["expression"]
        raw = sp.sympify(row["raw_transcription"], locals=symbols)
        restoration = -t**-2 if row["central"] == 1 else S**-1
        expected = sp.sympify(stored["expression"], locals=symbols)
        difference = sp.cancel((raw * restoration).subs(S, 1-t**2) - expected)
        assert difference == 0, (i, row["label"], difference)
        if source is not None:
            assert source.count("\\label{" + row["label"] + "}") == 1
            assert row["raw_source_tex"] in source
    print(f"SymPy {sp.__version__}: 50/50 restored transcriptions match exact stored fractions.")
    if source is not None:
        print("Full TeX SHA256, all fifty unique labels and literal snippets match.")
    print("Supplementary source comparison only; the Lean HasSum and Haar proofs are independent.")


if __name__ == "__main__":
    main()
