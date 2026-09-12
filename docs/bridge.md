# Bridge to the corrected core-integral goal, version 1

**Completed: Stage A and Stage B.** The strongest endpoint is the actual
explicit-kernel Haar-core evaluation, with ordinary integrability and both
principal and whole signed special Abel limits. The left side uses actual
local-field measures and actual matrix-entry/minor valuation minima. No
integral-to-series identity, integrability, row evaluation or limit is assumed.

**Not completed: Stage C.** The paper's independently defined normalized
spherical coefficient has not been identified with this explicit kernel.
Consequently the literal source spherical-coefficient RHS goal remains open
at that precise bridge. The original Fourier–Jacobi period, its unfolding and
intertwining argument, and later local L-factors were not needed or claimed.

The companion statement, proof and fifty-row source map are
`core_evaluation_statement_v1.md`, `core_evaluation_proof_v1.md`, and
`core_evaluation_source_map_v1.md`. Final source-matched verification is in
`publications/fourier-jacobi-core-evaluation/VERIFICATION.md`.

## Corrected comparisons actually proved

Write J_T for the independently defined sum of the three explicit-kernel
Haar integrals, and L_T for the independent full valuation series. The
proved chain is

\[
\mathcal J_T=\mathcal L_T
\quad(0<T\le1,\ t\le|\delta|\le1,\ Tt<|\delta|),
\qquad \mathcal J_1=\mathcal L_1=E_q
\quad(t<|\delta|\le1).
\]

The principal Abel convergence is established before multiplying the factor:

\[
\lim_{T\uparrow1}\frac2{q+1}\mathcal J_T
=\frac2{q+1}\mathcal J_1=\frac2{q+1}E_q.
\]

The special comparison is the whole-product limit

\[
\lim_{T\uparrow1}\frac{1-\varepsilon}{q+1}\mathcal J_T(\varepsilon t)
=\frac{1-\varepsilon}{q+1}E_q(\alpha,\beta,\varepsilon t).
\]

The declarations are `FourierJacobi.Analysis.corrected_principal_haar_comparison`
and `FourierJacobi.Analysis.corrected_special_haar_comparison`. Their complete
integrability/evaluation packages are `explicit_haar_core_evaluation` and
`explicit_haar_special_abel` in the same namespace. They prove exactly the
normalizations required for RHS(77) = [2/(q+1)] RHS(184) and RHS(80) = RHS(191),
**with the source coefficient replaced by the independently defined explicit
kernel**. There is no additional factor in the second comparison.

## Dependency boundary and inherited work

| Component | Status and proof basis |
|---|---|
| Finite fifty-row/eight-Weyl-term identity | Inherited v2 `Algebra.finiteCore_eq_closedCore`, rechecked |
| Four actual I0 infinite sums | Inherited cases 1,2,6,7, reused |
| Other 46 actual infinite rows | New `HasSum` proofs, no row-value assumptions |
| Partitions and parity/depth reindexing | New proved disjoint/exhaustive partitions and both inverse laws |
| Full unordered norm summability and row assembly | New, before rearranging or evaluating the sum |
| Exact E_q and natural denominator conditions | New independent transcription and checked match with `closedCore` |
| Interior evaluation and principal Abel theorem | New actual-series domination and Tannery argument |
| Special whole-product limit | New damped rational assembly; ε=1 direct zero |
| Canonical field valuation and basic Haar/null/matrix results | Inherited v2; not new progress |
| All integer shells and source multiplicative normalization | New actual measures, no shell-volume assumptions |
| Intrinsic finite measurable matrix indices and explicit kernel | New, including H=−u and the kernel norm bound |
| Actual joint collision-depth cell mass and AE partition | New field proof using fixed-y centered x sections |
| Integrand constancy and prefactor-times-cell identity | New, retaining real powers and integer valuations |
| Ordinary integrability and integral/sum interchange | New, derived from full norm summability |
| Haar evaluation and both Abel comparisons | New, complete Stage B |
| Independently defined spherical coefficient = explicit kernel | Unformalized Stage C mathematical bridge |
| Actual-object extension at excluded Weyl/special parameters | Unproved additional analysis |

The independent Stage A and Haar reviews found no concealed assumptions or
source-normalization mismatch. These reviews are supplementary; the final
Lean build, exhaustive axiom audit and displayed theorem hypotheses are the
formal evidence. A declaration count is not a theorem count.

## Source measure normalization, checked rather than assumed

The complete source at lines 221–228 normalizes additive Haar by μ(O)=1 and
multiplicative Haar by ν(π^k O×)=S=1−q⁻¹. The construction first supplies
multiplicative Haar with unit-subgroup mass one, then scales by S for the
source integrals. The actual wrapper `paperExplicitHaarCore` supplies both
`additiveHaar` and `paperMultiplicativeHaar` and the actual residue cardinality.

Every full cell has mass S³q^(−j−h)ω_r(j,h,c). With the source prefactors
(a₀,a₁,a₂)=(S⁻¹,q,−q/S), the checked identity is a_r S³=κ_r S²,
where κ=(1,qS,−q). This matches the independent master summand exactly.
The stored row data already include their restorations. All fifty source
restorations were separately audited and were not applied a second time.

The joint collision proof fixes y and uses x₀=y²/z. It proves centered ball
and shell measures directly. It does not assume that squaring sends uniform
units to uniform units. The zero-coordinate/determinant locus is proved null;
its complement is a countable measurable disjoint partition with unique
integer valuations and cancellation depth.

## Human proof and formalization status

Sections 1–6 of the companion proof supply the infinite-series argument.
Sections 7–11 supply the actual Haar argument in dependency order: intrinsic
indices, measures, partition, constant values, a summable norm majorant,
ordinary integrability, and only then countable integral summation and Abel
transfer. All of these steps are now formalized, including the generic
countable-fiber integration lemma with its hypotheses discharged for the
actual field. No open mathematical flaw is being hidden as a missing
library lemma in Stage A or B.

The remaining spherical step is substantive mathematics: starting from the
paper's normalized coefficient (defined from its unramified principal-series
representation), prove bi-invariance, identify the actual Cartan double coset
from the minima, prove the correctly normalized Macdonald formula, and match
its eight terms and powers with Ψ. The source contains the Cartan argument
under `expanded:cartan` and invokes the Macdonald formula in
`GSp4macdonald`; the expanded explanation is supplied in the preserved source.
The formalization does not contain that representation-theoretic proof.
No counterexample or normalization defect in this source bridge has been
identified; it is an unformalized theorem, not an established flaw.

The installed pinned mathlib supplied substantial valuation, Haar, topology,
real-power, summability and integration infrastructure used above. Inspection
of its representation/group/number-theory directories found no ready-made
Macdonald spherical formula or Iwasawa/Cartan decomposition matching this
source. This library gap does not replace the mathematical obligation: a
construction of the group/compact subgroup, normalized induction, spherical
vector and coefficient, and the bridge proof are still required. Merely
introducing a structure field Φ=Ψ would prove no part of that obligation.

If one starts instead from the source's stabilized central truncation,
fixed-cutoff integrability and the required central-shell cancellation must
also identify that independently defined limit with the three actual Haar
integrals. That identification is not part of the Stage B object and is not
claimed. It is distinct from the proved real-T Abel limit.

## Parameter coverage and genuine remaining analysis

The arithmetic theorem permits every real q>2. The Haar theorem sets q equal
to the field's actual residue cardinality and assumes q>2, thus covering the
paper's odd residue cardinalities. It does not require characteristic zero.
Both evaluation theorems use |α|=|β|=1 with
α≠1, β≠1, α≠β and αβ≠1. The principal interior is t<|δ|≤1, which includes
the paper's |δ|=1 range. All scalar, Weyl and geometric denominator conditions
used by the evaluation follow from these natural assumptions.

At δ=εt require α,β≠ε for the literal special quotient. For ε=1 the signed
product is zero directly; no undamped endpoint integral or series is required
or asserted. For ε=−1 the excluded α=−1 or β=−1 values remain excluded.
The principal interior does permit one of α,β to equal −1 if the four generic
conditions remain satisfied.

The nonsingular rational special expression G_sp alone cannot extend the
actual Abel limit through these excluded parameters. Such an extension needs
a parameter-continuity majorant or a direct cancellation argument for the
actual damped object. Likewise individual Weyl fractions at a wall cannot be
interpreted using totalized division as a continued spherical kernel. These
are unproved additional analytic obligations; this report supplies no full
proof of that extension and claims none. Broad helper theorems about literal
totalized expressions are not an extension of the intended object.

## Packaging and final handoff

The new publication contains source, manifest, pins, exact data, proof reports,
reproduction scripts, ignore rules and automatic GitHub Lean checks. Build
products and downloaded packages remain outside the publication and inside
the workspace. The original paper, both expanded sections and v1/v2 snapshots
are preserved. No commit, push, publication, or hosted CI run is claimed.
No license choice was recorded in v2, so the LICENSE file remains the owner's
outstanding packaging decision; no licensing choice was invented.
