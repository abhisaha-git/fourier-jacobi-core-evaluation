"""Reproduce the fifty-row documentation map; no proof certificate is generated."""
import json
from pathlib import Path

root = Path(__file__).resolve().parents[1]
audit = json.loads((root / "data/source-row-restorations.json").read_text(encoding="utf-8"))
lines = [
    "# Source-to-Lean map for all fifty rows, version 1", "",
    "Every index below is the zero-based `Algebra.regionTerms` index. "
    "All declaration names have prefix `FourierJacobi`. The precise original "
    "inequalities and depth predicates are in the named row modules; "
    "all reindexing maps have both inverse laws proved.", "",
    "Write S=1−t², P=1−δVt, N=1−Vt/δ, E=1−V²t², F=1−Ut², G=1−Ut⁴. "
    "The raw column omits the common Aᵢ/C_q. To obtain each actual contribution, "
    "the source's E₀ rows are divided by S, its E₁ rows multiplied by −q=−1/t², "
    "and its E₂ rows divided by S. The stored fraction already contains this "
    "restoration. Damping replaces U,V by TU,TV in the unsummed monomial and "
    "then in its proved row fraction; it is never applied to the simplified E_q.", "",
    "| Stored index | Source label (complete TeX line) | Raw source fraction | "
    "Restoration | Infinite HasSum proof | Provenance |",
    "|---:|---|---|---|---|---|",
]
for row in audit["rows"]:
    idx, case, central = row["index"], row["row"], row["central"]
    if central == 0:
        decl = f"Analysis.hasSum_i0_case{case}_regionTerm"
        status = "inherited v2" if idx in [0, 1, 5, 6] else "new I0Complete"
    elif central == 1:
        decl = f"Analysis.hasSum_i1_source_case{case}"
        status = "new I1SourceRows"
    else:
        decl = f"Analysis.hasSum_i2_rowTerm (ν={idx - 25})"
        status = "new I2Ambient"
    lines.append(f"| {idx} | `{row['label']}` ({row['source_line']}) | "
                 f"`{row['raw_transcription']}` | `{row['restoration']}` | `{decl}` | {status} |")
lines += ["", "## Partitions, inverse maps, and assembly", "",
    "- I0: `Analysis.i0Region_partition`; the four inherited maps in "
    "`Analysis/ValuationSeries.lean` and the new `i0UpperRowEquiv`, "
    "`i0MiddleRowEquiv`, `i0LowerRowEquiv` in `Analysis/I0Complete.lean`. "
    "The upper map includes both parity classes. `hasSum_i0_master` inserts "
    "the actual r=0 depth rule into the four-coordinate family.",
    "- I1: `Analysis/I1Partition.lean` proves unique membership in seventeen "
    "cells. `Analysis/I1Complete.lean` contains every cell Equiv, both inverse "
    "laws, Cartan substitution, geometric HasSum, and norm proof. The two "
    "parity pairs are combined in `I1SourceRows.lean`; `hasSum_i1_master` "
    "assembles the fifteen source rows with their true collision weights.",
    "- I2: `Analysis.i2_rows_partition` proves unique membership in twenty-five "
    "spatial/depth rows. `I2Domains.lean` contains their exact Equiv maps and "
    "both inverse laws; `I2Complete.lean` their infinite spatial sums; "
    "`I2Assembly.lean` the true depth sums; `I2Ambient.lean` transport to the "
    "original full lattice. The generic row theorem reaches the exact stored "
    "entry through `i2RegionTerm_eq_regionTerms`, with `i2Offset ν=25+ν`. "
    "`hasSum_i2_master` performs the final disjoint assembly.",
    "- `Analysis.summable_norm_weightedLatticeTerm` proves norm summability "
    "of the full eight-Weyl/three-central/integer-depth family. "
    "`hasSum_weightedLatticeTerm` justifies its grouping, and "
    "`latticeCore_eq_dampedRational` identifies its sum with all fifty rows.", "",
    "## Source audit and proof status", "",
    "`data/source-row-restorations.json` retains every literal final TeX "
    "right side, independent transcription, restoration, and exact symbolic "
    "difference. All fifty differences are zero. This SymPy check is "
    "supplementary source-matching evidence, not a Lean proof certificate. "
    "The declarations above prove the infinite identities; the final full "
    "build and axiom audit certify the delivered sources.", "",
    f"Complete TeX SHA256: `{audit['source_sha256']}`.",
    f"Inherited stored-data SHA256: `{audit['data_sha256']}`.", "",
    "## Endpoints", "",
    "The row sums require strict geometric norm bounds. Their full natural "
    "range is 0≤T≤1, t≤|δ|≤1, Tt<|δ|. At δ=εt, only 0<T<1 is used "
    "for ordinary summation. The signed whole-product Abel theorem is "
    "`Analysis.infinite_lattice_special_abel`, on the generic unitary locus "
    "with α,β≠ε. Its ε=1 branch is a direct zero-product limit. Negative "
    "special α=−1 or β=−1 and Weyl walls are not covered by continuation; "
    "no ordinary endpoint summability is inferred from a nonzero denominator.", "",
    "The detailed human row proofs and exact monomial tables are in the I0, "
    "I1, and I2 appendices under `docs/appendices/`. The separate proved "
    "`Analysis.paperExplicitHaarCore_eq_latticeCore` completes the actual "
    "explicit-kernel Haar bridge, and `Analysis.explicit_haar_special_abel` "
    "transfers the whole signed limit. The independently defined source "
    "spherical-coefficient identification remains unproved.", "",
]
dest = root / "docs/source-map.md"
dest.parent.mkdir(exist_ok=True)
dest.write_text("\n".join(lines), encoding="utf-8")
print(f"Wrote {dest}: {len(audit['rows'])} rows")
