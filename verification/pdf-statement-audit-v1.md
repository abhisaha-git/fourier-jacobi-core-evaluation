# Audit of the standalone formalized theorem statement, version 1

Audited on 11 September 2026. The deliverable is
[`formalized_theorem_v1.pdf`](../formalized_theorem_v1.pdf), a five-page
standalone statement compiled from the complete
[`formalized_theorem_v1.tex`](../formalized_theorem_v1.tex).

**Conclusion:** the existing checked development implies every mathematical
assertion of Theorem 1 and its endpoint explanation in this PDF, with exactly
the data and restrictions printed there. The scope is the actual explicit-kernel
Haar core (Stage B). Identification with an independently defined spherical
coefficient is neither an assumption hidden in this statement nor a conclusion
of it. The PDF explains that separate identification explicitly.

## What was checked mechanically

[`StatementAudit_v1.lean`](../StatementAudit_v1.lean) imports the existing
development, transcribes the PDF's definitions, proves that they equal the
existing definitions, and derives the theorem clauses. It contains no new
analytic hypotheses. In the following table, unqualified audit names are in
namespace `FourierJacobiPdfV1`.

| PDF content | Checked audit declarations | Existing formalized object or result |
|---|---|---|
| Section 1: normalized additive and multiplicative Haar measures | `measure_normalizations` | `Measure.additiveHaar_integers`, `Measure.paperMultiplicativeHaar_valuationRingUnits`, actual Haar instances |
| Section 1: product measure in the order stated | `product_measure` | `Analysis.paperCoreMeasure` |
| Equation (2): the constant (C_q) | `C_coe`, `C_eq_poincare` | `Analysis.paperC`, `Algebra.poincare` at (t=q^{-1/2}) |
| Entire eight-row coefficient table | `A_eq`, `U_eq`, `V_eq` | `Algebra.weylWeights`, `weylU`, `weylV` |
| Every denominator in the table is nonzero | `roots_regular` | Direct proof from unitarity and the four printed generic restrictions |
| Equation (3): all sixteen matrix entries | `matrix_eq` | `LocalMatrix.g` |
| Equations (4)–(5): all entry and minor minima, finite without dropping zeros | `minor_index_coverage`, `minima_finite`, `minima_eq` | `LocalMatrix.indexPairs`, `secondCompound`, `Valuations.matrixMinimum`, `actual_minima_finite` and the integer-extraction equalities |
| Equation (7): the entire formula for (Phi_0) | `Phi_eq` | `Analysis.explicitWeylKernel` |
| Equation (8): three central coordinates and three prefactors | `central_eq`, `prefactor_eq` | `Analysis.coreCentral`, `coreIntegralPrefactor` |
| Equations (9)–(10): actual integrand and Haar core | `f_eq`, `I_eq` | `Analysis.explicitCoreIntegrand`, `paperExplicitHaarCore` |
| Equations (11)–(15): products and the literal closed quotient | `D1_eq`, `D2_eq`, `E_eq` | `Analysis.paperD1`, `paperD2`, `paperE` |
| Theorem 1(i): ordering, nonnegative indices, height and bound | `minima_finite`, `part_i` | `Valuations.actualInteger_bounds`, `kernel_indices_nonnegative`, `kernel_height_eq`, `Analysis.explicitWeylKernel_q_norm_le` |
| Theorem 1(i): Borel measurability | `part_i_measurable` | All six index measurability results and `Analysis.explicitWeylKernel_measurable` |
| Theorem 1(ii): measurable, absolutely integrable integrands on the printed range | `part_ii` | `Analysis.explicitCoreIntegrand_integrable`, with the proved central-representative property |
| Theorem 1(iii): unscaled evaluation, principal Abel convergence and corrected normalization | `part_iii` | `Analysis.explicit_haar_core_evaluation`, `corrected_principal_haar_comparison` |
| Theorem 1(iv): damped endpoint integrability, denominator regularity and whole-product limit | `part_iv` | `Analysis.explicit_haar_special_abel` |
| Section 5: direct zero-product statement and limit | `positive_product`, `positive_limit` | Direct zero multiplication and `Analysis.tendsto_haar_special_positive` |

`E_eq` unfolds the independently transcribed numerator products as well as
the denominator; agreement is not established merely by reusing the name
`paperE`. Similarly, the coefficient-table proof checks all eight rows and
all four factors in each row. The minor-index coverage proof checks that the
six increasing pairs are exactly all the pairs used by the PDF's 36 minors.
The finiteness and extraction equalities ensure that the integer indices
really are these minima, including at zero coordinates and zero minors.

The audit prints complete declaration types and transitive axiom lists. Its
guard checks all 62 named declarations and current-module private helpers.
The only permitted axioms are `propext`, `Classical.choice`, and `Quot.sound`.
It rejects unsafe or partial declarations and any unapproved axiom. A new
strict check of the original exhaustive audit separately covers all 4,609
declarations in the 69 mathematical modules. These are declaration counts,
not counts of distinct theorems.

## Hypothesis and interpretation review

The type assumptions of the actual Haar results are precisely a field, a
valuation relation, its compatible nonarchimedean local-field topology, and
the Borel measurable structure. The units use the induced Borel structure;
this is proved by `Analysis.coreUnits_borelSpace`. The PDF specifies these
standard structures. Its (v) is the normalized additive valuation defining
that topology, corresponding to `Valuations.localFieldValuation`. The
valuation of a nonzero element is finite and that of zero is (+infty).
The coordinate exponent in (9) agrees with it by
`Analysis.coreScaleExponent_coe`.

The residue cardinality is `Measure.residueCardinality F`, not a freely chosen
real number in the Haar theorem. The uniformizer is an actual nonzero field
element with valuation one. The PDF's normalized Haar measures are the actual
Haar measures with the stated masses; it does not allow a free measure chosen
to force the answer. Existence and normalization are provided by the
development. The use of “the normalized Haar measure” has its usual unique
meaning. No extra sigma-finiteness, regularity of a selected kernel, or
integrability assumption is inserted into the final theorem.

Unitarity makes (alpha,eta) nonzero. The common restrictions are exactly

\[
|\alpha|=|\beta|=1,\quad \alpha\ne1,\quad\beta\ne1,
\quad\alpha\ne\beta,\quad\alpha\beta\ne1.
\]

The range in (17) is (t\le|\delta|\le1), (0<T\le1) and
(Tt<|\delta|). Since (q>2) gives (0<t<1), it implies
\(\delta\ne0\), and includes the two particular ranges printed immediately
after it. This specialization also appears directly in the existing
`explicitCoreIntegrand_integrable_damped` and
`explicitCoreIntegrand_integrable_undamped` declarations.

The principal part requires (t<|\delta|\le1). The endpoint part requires
\(\varepsilon=1\) or \(-1\) and \(\alpha,\beta\ne\varepsilon\).
No auxiliary nonzero-denominator conditions are silently assumed. The
closed denominator's nonvanishing is a conclusion of `part_iii` or `part_iv`;
the remaining elementary scalar denominators follow from
`Analysis.core_scalar_denominators_ne_zero`, positivity of (C_q), and
`Measure.paperMultiplicativeFactor_pos`. The table's denominators are checked
separately by `roots_regular`.

All integer powers in the PDF correspond to integer powers in Lean. The
positive real (3/2) power in (9) corresponds exactly to `Real.rpow` in `f`.
The tuple products retain multiplicities. The PDF's one-based matrix indices
are a relabeling of `Fin 4`; the eight coefficient rows retain the same order.

Every limit is a `Tendsto` statement along `nhdsWithin 1 (Set.Ioo 0 1)` in the
real variable (T). Although Lean integrals and division are total functions,
the PDF only uses them where integrability and nonzero denominators have been
proved. For the positive special branch, `part_iv` justifies the damped
integrals before `positive_product` and `positive_limit` are interpreted as
ordinary integral assertions. Neither endpoint branch asserts existence of
an ordinary undamped integral. In particular, no multiplication by zero is
used to disguise an undefined endpoint integral.

The extra factor in the principal equation (19) is exactly (2/(q+1)).
The special equation (21) applies the signed factor to the whole damped core
and introduces no further factor. No extension to excluded Weyl parameters,
no source-period identity, and no representation-theoretic identification is
included in the PDF theorem.

## PDF and source identity

The Lean checker does not parse TeX or certify typography. The final audit
therefore has two parts: the mechanically checked transcription/implication
above, and a manual comparison of that transcription with the complete TeX
source and all five rendered PDF pages. That comparison found no omitted
hypothesis, changed factor, altered exponent, or enlarged parameter range.
All formulas, the 32 coefficient factors, both Haar normalizations, the three
integral prefactors and both limit filters were reviewed.

The PDF contains its own definitions and only internal equation/section
references. It contains no external citations, linked resources, or project
paths needed to understand the theorem. Final document QA found five A4
pages, all references resolved, no external PDF actions, and no compiler
errors or overfull/underfull boxes. All five rendered pages were visually
inspected for legibility, clipping, formula layout and page completeness.

The exact reviewed files have these SHA-256 hashes:

| File | SHA-256 |
|---|---|
| `formalized_theorem_v1.tex` | `854ec609055c8e8c0d2c500120ee3747c0e7d548bcb42f76fe9fc0d7a028ea60` |
| `formalized_theorem_v1.pdf` | `9027a2b47d933eaffff462bf49d856a3a73b9b14acf36118dc04504a322a039f` |
| `StatementAudit_v1.lean` | `2dcefac96b47299dcb843cb27542aad1ebd8448780953b5aec252e99fa59c775` |

Current outputs are `pdf-statement-v1-build.txt`,
`pdf-statement-v1-axioms.txt`, `pdf-statement-v1-implication.txt`,
`pdf-statement-v1-tex-build.txt`, `pdf-statement-v1-qa.json`, and
`pdf-statement-v1-checks.json`, all in this verification directory. They use
Lean `leanprover/lean4:v4.33.1` and mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`. The checked source location is the
new core-evaluation publication. All 74 previously checked proof/configuration
hashes are unchanged. The original papers and v1/v2 publication snapshots were
not edited. No hosted CI execution or external publication is claimed.
