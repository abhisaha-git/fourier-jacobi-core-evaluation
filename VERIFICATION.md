# Verification of the delivered core-evaluation publication

This is the historical verification record for the original mathematical
library and PDF statement. The current Palomar preparation record, including
the additional Challenge/Solution files and current source hashes, is
[verification/palomar-v1/README.md](verification/palomar-v1/README.md).
The dated records below are retained unchanged as historical evidence; their
old whole-repository hashes are not a claim about subsequently edited metadata.

Verified locally on 11 September 2026 with the pinned project-local environment.
The strongest checked scope is Stage B: actual explicit-kernel Haar evaluation,
ordinary integrability, principal Abel convergence and the whole signed special
Abel limit. Stage A is complete as part of its dependency chain. The source
spherical-coefficient identification is not claimed.

## Current checks and outputs

| Check | Result | Current output |
|---|---|---|
| Reproduced preserved v2 full build | Passed, 3,108 jobs | `verification/baseline-v2-build.txt` |
| Reproduced preserved v2 axiom audit | Passed, 1,546 declarations | `verification/baseline-v2-axioms.txt` |
| New publication full Lake build with `--wfail` | Passed, 3,164 jobs, exit 0 | `verification/build.txt` |
| New exhaustive audit with `warningAsError=true` | Passed, 4,609 declarations across 69 modules, exit 0 | `verification/axioms.txt` |
| New-module types and transitive axioms | 3,053 declarations in all 39 new modules audited | Same exhaustive audit output |
| Original sources and snapshots | All 5 source documents, 46 v1 hashes and 66 v2 hashes match | `verification/preservation-recheck.json` |
| Dependency revisions and tracked sources | All 9 match their manifest revisions, no tracked changes | `verification/dependencies.json` |
| Independent source restoration audit | 50/50 exact symbolic differences zero; source hash, labels and literal snippets match | `verification/row-restorations.txt` |

The counts are **declaration counts**, not theorem counts. The new audit covers
all 30 inherited source modules and all 39 new modules, including private
helpers identified by their originating module. This is more exhaustive for
older private helpers than the saved v2 namespace-based audit; inherited
mathematical results are not counted as new progress.

`Audit.lean` verifies that the entire enumerated project module inventory is
imported and rejects unexpected project modules, missing main declarations,
unsafe or partial declarations, and any transitive axiom outside
`propext`, `Classical.choice`, and `Quot.sound`. It prints the complete types
and axioms of every new declaration, followed by the main interfaces together.
The full source scan found no `sorry`, `admit`, new `axiom`, `native_decide`,
`unsafe` or `partial` in the mathematical modules.

The first audit execution diagnosed an unsupported pretty-print option; it
was corrected from `pp.width` to the pinned Lean option `format.width`, then
the entire audit was rerun successfully. The final output linked above is
from that successful run. The initial diagnostic is kept only in workspace
build state. No mathematical assumption was changed to repair the audit.
The full build contains one informational `ring_nf` tactic suggestion in
`ExplicitKernel.lean`; the enclosing proof and full build passed, with no
warning or error. Hosted GitHub CI has **not** been run.

## Commands and checked source location

From the original workspace root, in each fresh command session:

```powershell
. ./build/fourier-jacobi-core-lean/direct-env.ps1
lake -d build/fourier-jacobi-core-lean build --wfail
lake -d build/fourier-jacobi-core-lean env lean -DwarningAsError=true publications/fourier-jacobi-core-evaluation/Audit.lean
```

The build used `srcDir = '../../publications/fourier-jacobi-core-evaluation'`.
It did not point to v2. The root module explicitly imports all 69 delivered
source modules. The exact external Lake configuration and process-local
environment scripts are retained in `verification/workspace-lakefile.toml`,
`workspace-direct-env.ps1.txt`, and `workspace-base-env.ps1.txt`.
`verification/check-summary.json` records the commands, outcomes and pins.

Lean: `leanprover/lean4:v4.33.1`.
Mathlib: `0df444a360eaa60ab8c11dca51a86af692955474`.
The unchanged full dependency manifest is `lake-manifest.json`.
The actual `lean --version` output is in `verification/lean-version.txt`.

All Lean compilation ran inside the sandbox. No Lean compilation escalation, installation,
upgrade, global configuration change or dependency-source edit was necessary.
The environment keeps Elan, Lake/mathlib caches, XDG state, temporary files
and build products under the workspace. The checked output directories,
package roots and their relevant ancestors have no junction/symlink redirects.
Build products and downloaded packages are outside this publication. Shared
workspace module caches were used through Lake's source-aware dependency graph.

## Source identity and mathematical hypothesis review

`verification/checked-lean-sha256.json` records all 69 module sources, the root
module, Audit.lean, toolchain file, Lake configuration and manifest.
`verification/source-sha256.json` records the complete delivered source/data/
script/document set, excluding the verification records themselves to avoid
self-referential hashes. `scripts/verify-source-record.ps1` verifies that set.
`verification/record-sha256.json` ties the build, audit, pins, source manifests,
commands and preservation evidence together. No proof source was changed after
its successful final check. The audit-script formatting fix was verified by
the successful final audit.

The main actual-Haar hypotheses are a field with valuation relation and its
nonarchimedean local-field topology, the Borel structure, actual residue
cardinality q>2, a uniformizer of canonical valuation one, and exactly the
stated scalar parameter conditions. Sigma-finiteness, measurability, finite
cell measures, AE exhaustiveness, cell values, norm summability, integrability
and the integral-to-series identity are proved. None is assumed in the final
evaluation or limit theorem. The actual core is defined from matrix minima
and normalized Haar measures, independently of the series and E_q.

For the principal theorem, t<|δ|≤1 and generic unitary α,β are required.
For the literal special quotient additionally α,β≠ε, ε=±1. The ε=1 proof
is the direct zero-product limit; no ordinary undamped endpoint sum/integral
is asserted. The independent review reports are included in `docs/appendices/`.
Axioms alone do not establish these scope facts; the printed main theorem types
and inspected definitions establish the exact boundary described in
`docs/statement.md` and `docs/bridge.md`.

## Reproduction and packaging

After copying this folder to a repository, run `lake build --wfail` and
`lake env lean -DwarningAsError=true Audit.lean` using the pinned environment.
The included Windows setup and GitHub workflow keep installations and caches
inside that repository. See `REPRODUCE.md` for details.
The Lean build does not require Python/SymPy or the optional authoring scripts.
The supplementary fifty-row audit can be repeated from retained data with
`scripts/verify-row-restorations.py`; `--source PATH` additionally checks the
preserved complete TeX against its recorded hash and literal snippets.

No commit, push or publication was performed. The original paper, both expanded
sections and v1/v2 publication snapshots remain unchanged. No license choice
was recorded in v2; adding the owner's chosen LICENSE remains a packaging
decision, not an unfinished mathematical proof step.

## Standalone PDF statement audit (version 1)

The final five-page statement is `formalized_theorem_v1.pdf`, built from the
complete retained TeX source. The README links to it as the full standalone
statement of the explicit-kernel Haar theorem. The document states every
scalar and local-field assumption, supplies the entire kernel formula, and
does not assume or assert a spherical-coefficient identification.

`StatementAudit_v1.lean` independently transcribes the displayed coefficient
table, matrix, normalizing constant, prefactors, integrand, core and quotient.
It proves agreement with the existing definitions and derives all four theorem
parts and the direct positive-endpoint zero limit. Its guard checks all 62
named declarations and current-module private helpers, rejects unsafe/partial
declarations and unapproved transitive axioms, and prints the complete types.
This is an additional audit file; the 69 mathematical modules, root import,
original exhaustive audit and all version pins are unchanged.

Final repeated checks are retained separately from the earlier records:

| Check | Output |
|---|---|
| Full new-publication Lake build with `--wfail` | `verification/pdf-statement-v1-build.txt` |
| Exhaustive original-module axiom audit | `verification/pdf-statement-v1-axioms.txt` |
| New PDF definition/statement implication and axiom audit | `verification/pdf-statement-v1-implication.txt` |
| Final pdfLaTeX pass | `verification/pdf-statement-v1-tex-build.txt` |
| PDF structure, self-containment, references, output paths and hashes | `verification/pdf-statement-v1-qa.json` |
| Final commands, outcomes and source identity | `verification/pdf-statement-v1-checks.json` |

The clause-by-clause review is in `verification/pdf-statement-audit-v1.md`.
The Lean audit does not parse TeX: the transcription-to-PDF comparison is an
explicit manual audit of the source and rendered pages, backed by the
machine-checked consequences. This distinction is part of the verification
record. No hidden analytic hypothesis was introduced.

The original source and record manifests have been retained as
`verification/pre-pdf-source-sha256-v1.json` and
`verification/pre-pdf-record-sha256-v1.json`; the current manifests include the
new PDF, source, audit, scripts and updated documentation. The unchanged 74
entries in `verification/checked-lean-sha256.json` were rechecked.

The PDF was compiled with the installed MiKTeX read-only. Sandbox launch failed
with access denied, with no compiler process left running. The necessary
compilation then used the authorized narrow compilation exception and the
project-local state script. All recorded output paths resolve inside the
workspace; no installation, upgrade or global configuration change occurred.
The final log has no unresolved references or overfull/underfull boxes. Its
only warning is that the unused EPS-conversion feature has shell escape
disabled. All five final pages were rendered and inspected. The GitHub script
now includes `StatementAudit_v1.lean`; no hosted CI run is claimed.
