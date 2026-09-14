# Compiled statement comparison correction

Baseline: `287a501a353c874bb112e7ff674b577327ea5c5d`.

[Palomar run 34848167581](https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/34848167581)
built the Solution successfully and passed its axiom/safety audit, then rejected
the compiled declaration `FourierJacobiPalomar.I` during Comparator comparison.
The earlier `ring` message in the diagnostic did not prevent the Lean build.

The definition's written formula and type agreed, but typeclass inference
selected different `NormedSpace ℝ ℂ` terms. The Challenge used
`NormedSpace.complexToReal`; the Solution used
`InnerProductSpace.toNormedSpace` through `instInnerProductSpaceRealComplex`.
Comparator requires literal declaration agreement, not mathematical equivalence
of those structures. The source-only package checker did not catch this.

The correction explicitly imports `Mathlib.Analysis.InnerProductSpace.Basic`
in both files. It changes no written definition, theorem statement, theorem
proof, metadata, Lean version, or dependency pin. The package still uses Lean
v4.33.1 and mathlib `0df444a360eaa60ab8c11dca51a86af692955474`.

`scripts/check-palomar-statements.lean` compares the compiled theorem types and
their transitive statement dependencies in separate environments, excluding
only the selected theorem bodies. It follows the dependency traversal used by
[the pinned Comparator](https://github.com/leanprover/comparator/blob/575674928e239f5bc452aab72d1dd7b0f1326494/Comparator/Compare.lean).
It is stricter about expression metadata than the export comparison. The Windows
verification script and GitHub proof workflow now run it after both modules
have been built. This is a local regression check, not independent kernel replay
or a claim that Palomar's hosted checks have passed.

## Completed checks

- [Original compiled comparison](baseline-comparison.txt): fails at `I`, as expected.
- [Corrected compiled comparison](compiled-statements.txt): all four theorem types
  and 29,437 transitive statement dependencies match exactly.
- [Lake build](build.txt): passes all 3,167 jobs with warnings treated as errors.
  The fresh Solution audit checks 89 declarations and permits only the three
  standard axioms.
- [Challenge build](challenge.txt): passes all 2,669 jobs, with exactly the four
  authorized statement-placeholder warnings.
- Metadata and package checks pass, including the saved upstream v0.4 schema.

[results.json](results.json) records the pins, scope, and normalized source
hashes. An isolated copy of the submitted commit was checked using the pinned
project-local Windows toolchain. Unchanged dependencies and proof modules could
reuse build artifacts; both affected modules were compiled again. No original
proof-module text changed except for the additional import in each file.

The new local comparison is run through Lake by the standard verification
script. Protected Comparator, NanoDa replay, and hosted editorial review have
not been rerun for this correction; they must check the new pushed commit.
