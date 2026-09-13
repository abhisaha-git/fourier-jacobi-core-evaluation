# Mathematical and verification status

The development reaches **Stage B: actual explicit-kernel Haar-core evaluation
and the whole signed special Abel limit**. Stage A is complete. Identification
with the paper's independently defined spherical coefficient has not been done.

| Scope | Result |
|---|---|
| Independent lattice, Stage A | All fifty actual infinite rows, exact partitions and reindexings, full-family norm summability, undamped interior evaluation, principal Abel convergence, and whole signed special limit |
| Actual explicit-kernel Haar core, Stage B | Actual matrix indices, measurable kernel and partitions, normalized shell/collision measures, integrability, Haar-to-lattice identity, and both corrected comparisons |
| Paper's spherical-coefficient core, Stage C | Not established: the independently defined coefficient has not been identified with the explicit kernel |
| Exceptional Weyl walls and negative special endpoint exclusions | No extension asserted |

## Exact range and conclusions

The arithmetic series theorem takes real \(q>2\). The Haar theorem takes a
nonarchimedean local field with actual residue cardinality \(q>2\), its canonical
normalized valuation, actual source-normalized Haar measures, and an actual
uniformizer of valuation one. The Lean field theorem does not require
characteristic zero or oddness beyond \(q>2\); it includes the paper's
characteristic-zero fields of odd residue cardinality.

Write \(t=q^{-1/2}\). The parameter assumptions are
\[
 |\alpha|=|\beta|=1,\quad
 \alpha\ne1,\ \beta\ne1,\ \alpha\ne\beta,\ \alpha\beta\ne1.
\]
Damped summability and Haar integrability hold for \(0<T<1\) and
\(t\le|\delta|\le1\). At \(T=1\), the evaluation and integrability require
\(t<|\delta|\le1\). No auxiliary geometric-denominator conditions are left as
extra assumptions.

`explicit_haar_core_evaluation` proves all three undamped integrands are
integrable, the unscaled core equals \(E_q\), the literal quotient denominator
is nonzero, and the damped core tends to that value.
`corrected_principal_haar_comparison` then applies \(2/(q+1)\) on both sides.

At \(\delta=\varepsilon t\), \(\varepsilon=\pm1\), the literal special theorem
also assumes \(\alpha,\beta\ne\varepsilon\).
`explicit_haar_special_abel` proves integrability of each damped integral,
the endpoint quotient's nonzero denominator, and the limit of the whole signed
product. `corrected_special_haar_comparison` supplies the special comparison
without any extra factor. No ordinary undamped endpoint integral or series is
asserted. The positive-sign branch is directly the identically zero product.

All four main declarations are in namespace `FourierJacobi.Analysis` in
[HaarLimits.lean](FourierJacobi/Analysis/HaarLimits.lean).
The [statement](docs/statement.md) records their full signatures and formulas.

## Inherited and new work

Preserved v2 supplied the finite fifty-row/eight-Weyl identity, four genuine
infinite I0 row proofs, and general local-field valuation, Haar/null-set,
collision, and matrix/minor results. These are dependencies, not new progress.

This publication adds the remaining 46 infinite rows and their full assembly,
actual norm summability and Abel arguments, the exact \(E_q\) transcription,
all-integer Haar shell results, multiplicative source normalization, actual
shell collision transport, intrinsic measurable kernel indices, actual lattice
cells and masses, cell integrand values, and justified countable integration.
[PROVENANCE.md](PROVENANCE.md) records the preserved baseline.

## Verification and packaging

The full pinned Lake build passed 3,164 jobs with `--wfail`. The exhaustive
audit passed 4,609 declarations across all 69 modules, including all 39 new
modules and their private helpers. Current outputs, commands, exact theorem
hypotheses and matching source hashes are in [VERIFICATION.md](VERIFICATION.md).
The permitted foundational axioms are only `propext`, `Classical.choice`,
and `Quot.sound`.

The toolchain and mathlib pins are unchanged. The GitHub workflow is supplied;
the historical verification record does not certify a hosted run. The root
`LICENSE` now records the owner's Apache-2.0 selection. For the current Palomar
package and the checks still performed by the submission service, see
[PALOMAR.md](PALOMAR.md). Preparation does not itself register the result.
