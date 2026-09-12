# Fourier–Jacobi core evaluation

This Lean publication formalizes a substantial chunk of the local calculations in the paper "An explicit refined Gan--Gross--Prasad identity for Fourier--Jacobi periods of degree 2 Siegel cusp forms" by Biplab Paul, Ameya Pitale, Abhishek Saha, and Ralf Schmidt.

The [complete formalized theorem, as a standalone PDF](formalized_theorem_v1.pdf)
contains the full statement proved here: all field and scalar assumptions,
both Haar normalizations, the complete formula defining \(\Phi_0\), ordinary
integrability, the principal evaluation and Abel convergence, and the signed
special Abel limit with its exact exclusions. It requires no other project
document to understand the statement. The [statement implication audit](verification/pdf-statement-audit-v1.md)
records the clause-by-clause comparison and the checked Lean consequences in
[StatementAudit_v1.lean](StatementAudit_v1.lean).

The main declarations are in
[HaarLimits.lean](FourierJacobi/Analysis/HaarLimits.lean), in namespace
`FourierJacobi.Analysis`:

- `explicit_haar_core_evaluation`
- `explicit_haar_special_abel`
- `corrected_principal_haar_comparison`
- `corrected_special_haar_comparison`


The [exact statement](docs/statement.md), [human proof](docs/proof.md),
[bridge report](docs/bridge.md), and [fifty-row source map](docs/source-map.md)
give the detailed mathematical record.

Lean is pinned to `leanprover/lean4:v4.33.1`, with mathlib revision
`0df444a360eaa60ab8c11dca51a86af692955474`.
The full local Lake build passed all 3,164 jobs with `--wfail`. The exhaustive
audit passed 4,609 declarations across all 69 modules, permitting only
`propext`, `Classical.choice`, and `Quot.sound`. Commands, current logs and
matching source hashes are in [VERIFICATION.md](VERIFICATION.md).
The additional PDF statement audit checks 62 named declarations and their
private helpers with the same axiom restriction; it is included in the
automatic Lean verification script.
[REPRODUCE.md](REPRODUCE.md) describes the project-local environment.

