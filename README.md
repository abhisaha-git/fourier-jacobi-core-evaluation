# Fourier–Jacobi core evaluation

This Lean publication proves an explicit local-field Haar-integral evaluation
and its principal and signed special Abel limits, adapting the local calculations
in [An explicit refined Gan–Gross–Prasad identity for Fourier–Jacobi periods of
degree 2 Siegel cusp forms](https://arxiv.org/abs/2608.26007) by Biplab Paul,
Ameya Pitale, Abhishek Saha and Ralf Schmidt. The kernel is a concrete eight-term
Weyl sum whose indices come from valuations of matrix entries and two-by-two
minors. Its identification with the paper's independently defined spherical
coefficient, and the full period identity, are outside the proved result.

For Palomar, start with the self-contained [Challenge](Challenge.lean), its
[proved Solution](Solution.lean), and [submission instructions](PALOMAR.md).
[formalization.yaml](formalization.yaml) records the authorship, mathematical
sources, AI assistance, review status and limitations. The author and responsible
maintainer is Abhishek Saha; the existing repository license is
[Apache-2.0](LICENSE). [PROVENANCE.md](PROVENANCE.md) explains the prior work.

The calculation concerns local factors in the theory of automorphic forms and
Fourier–Jacobi periods. Its mathematical content is the passage from actual
normalized Haar integrals to fifty infinite valuation regions, their justified
summation and an explicit rational formula. The field has actual residue
cardinality q>2; no characteristic-zero assumption is needed. With t=q⁻¹ᐟ²,
the parameters satisfy |α|=|β|=1, α,β≠1, α≠β and αβ≠1. The undamped theorem
requires t<|δ|≤1. At δ=εt, ε=±1, the signed Abel theorem additionally excludes
α,β=ε and asserts no ordinary undamped endpoint integrability. Its positive
sign is the identically zero product. No extension to exceptional Weyl walls
or novelty claim is made.

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
The original local Lake build passed all 3,164 jobs with `--wfail`. The exhaustive
audit passed 4,609 declarations across all 69 modules, permitting only
`propext`, `Classical.choice`, and `Quot.sound`. Commands, current logs and
matching historical source hashes are in [VERIFICATION.md](VERIFICATION.md).
The current submission checks and source hashes are recorded in
[verification/palomar-v1/README.md](verification/palomar-v1/README.md).
The additional PDF statement audit checks 62 named declarations and their
private helpers with the same axiom restriction; it is included in the
automatic Lean verification script.
[REPRODUCE.md](REPRODUCE.md) describes the project-local environment.
