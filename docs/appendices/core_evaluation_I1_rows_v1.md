# I1: complete valuation-row development

This report concerns new files in `publications/fourier-jacobi-core-evaluation`.
The original paper, expanded sections, and v1/v2 snapshots are preserved. The
finite rational expressions and integer Cartan table are inherited from v2;
the I1 infinite-domain equivalences, infinite sums, collision-weight insertion,
and complete I1 lattice assembly are new work.

## Independent summand and normalization

Write (X=TU, Y=TV, Q=1-t^2), and impose (t\ne0, qt^2=1). The
new `Analysis.i1Raw` is

\[
 Q^3\delta^k t^{3k+2j+2h+3\ell+4b-2}X^{\ell/2}Y^b,
 \qquad (\ell,b)=\operatorname{cartanIndices}(1,k,j,h,c).
\]

All valuation exponents are integer powers. The independently defined
master family of the brief is used: `i1Raw_eq_shell` proves this expression
equals `shellCoeff q 1 * shellMonomial ... 1 ...`, before collision weights
are attached. In particular, (\kappa_1=q(1-q^{-1})) is already incorporated.
The expanded source defines \(\mathcal E_{1,\nu}=-q^{-1}I_{1,\nu}\);
the stored expressions are the restored \(I_{1,\nu}=-q\mathcal E_{1,\nu}\).
No additional restoration is applied to the stored fractions.

Set

\[
 P=1-\delta Yt,\quad N=1-Yt/\delta,\quad E=1-Y^2t^2,
 \quad F=1-Xt^2,\quad G=1-Xt^4.
\]

The following table compares every expanded final expression, after its
explicit multiplication by (-q) and the substitution

\[
q^{-1}=t^2,\qquad \gamma^2L_i^2=U_i,\qquad M_i=V_i,
\]

with the stored fraction. The common Weyl multiplier (A_i/C_q) is omitted.

| Source row / label | Stored index | Restored damped fraction | New base-cone declarations |
|---|---:|---|---|
| 1 / I1eqq1 | 10 | \(QX\delta t/P\) | `i1r1Equiv`, `hasSum_i1r1_raw` |
| 2 / I1eqq2 | 11 | \(Q^2XY\delta t^3/(GP)\) | `i1r2Equiv`, `hasSum_i1r2_raw` |
| 3a / I1eqq3a | 12 | \(Q^2XY\delta t^3(1+Y)/(EP)\) | `i1r3aeEquiv`, `i1r3aoEquiv`, both corresponding `hasSum_*_raw` |
| 3b / I1eqq3b | 13 | \(Q^2(1-2t^2)XY\delta t/(EP)\) | `i1r3bEquiv`, `hasSum_i1r3b_raw` |
| 3c / I1eqq3c | 14 | \(Q^2Y^2\delta t/(EP)\) | `i1r3cEquiv`, `hasSum_i1r3c_raw` |
| 4 / I1eqq4 | 15 | \(Q^3X^2Y\delta t^3/(EFP)\) | `i1r4Equiv`, `hasSum_i1r4_raw` |
| 5 / I1eqq5 | 16 | \(Q^3X^2Y\delta t^5/(FGP)\) | `i1r5Equiv`, `hasSum_i1r5_raw` |
| 6a / I1eqq6a | 17 | \(QYt^2\) | `i1r6aEquiv`, `hasSum_i1r6a_raw` |
| 6b / I1eqq6b | 18 | \(QXt/(\delta N)\) | `i1r6bEquiv`, `hasSum_i1r6b_raw` |
| 7 / I1eqq7 | 19 | \(Q^2Xt^2/(GN)\) | `i1r7Equiv`, `hasSum_i1r7_raw` |
| 8a / I1eqq8a | 20 | \(Q^2Xt^2(1+Y)/(EN)\) | `i1r8aeEquiv`, `i1r8aoEquiv`, both corresponding `hasSum_*_raw` |
| 8b / I1eqq8b | 21 | \(Q^2(1-2t^2)X/(EN)\) | `i1r8bEquiv`, `hasSum_i1r8b_raw` |
| 8c / I1eqq8c | 22 | \(Q^2Y/(EN)\) | `i1r8cEquiv`, `hasSum_i1r8c_raw` |
| 9 / I1eqq9 | 23 | \(Q^3X^2t^2/(EFN)\) | `i1r9Equiv`, `hasSum_i1r9_raw` |
| 10 / I1eqq10 | 24 | \(Q^3X^2t^4/(FGN)\) | `i1r10Equiv`, `hasSum_i1r10_raw` |

All declarations listed here have namespace `FourierJacobi.Analysis`. Each
base-cone declaration has accompanying `_cartan`, `_reindexed`, and
`summable_norm_*_raw` results. The assembled master-cell results use the
same names with `_master` in place of `_raw`.

`I1SourceRows.lean` supplies the fifteen direct row declarations
`hasSum_i1_source_case1`, `hasSum_i1_source_case2`,
`hasSum_i1_source_case3a`, `hasSum_i1_source_case3b`,
`hasSum_i1_source_case3c`, `hasSum_i1_source_case4`,
`hasSum_i1_source_case5`, `hasSum_i1_source_case6a`,
`hasSum_i1_source_case6b`, `hasSum_i1_source_case7`,
`hasSum_i1_source_case8a`, `hasSum_i1_source_case8b`,
`hasSum_i1_source_case8c`, `hasSum_i1_source_case9`, and
`hasSum_i1_source_case10`. Each concludes `HasSum` to the exact corresponding
stored `regionTerms` entry. Cases 3a and 8a use the disjoint sum of their two
explicit parity cells; all other cases use a single full lattice cell.

## Proof order

1. Parameterize the exact integer inequalities by two or three independent
   nonnegative integers. Every `Equiv` carries Lean proofs of both inverse
   laws, including the parity maps. No finite cutoff or generated test is
   used as a proof certificate.
2. Substitute the checked integer minima into each cone. All noncollision
   and depth-insensitive rows allow arbitrary cancellation depth. Rows 3b/8b
   use depth zero; rows 3c/8c use every depth at least one.
3. Rewrite the unsummed monomial into a product of geometric families. Each
   family includes (X=TU) and (Y=TV) at this point. For example, row 4 is

   \[
   k=a+1,\quad j=-2a-2b-c-4,\quad h=-a-b-c-3,
   \]

   with (a,b,c\ge0), and its raw summand becomes

   \[
   Q^3\delta X^2Yt^3(\delta Yt)^a(Y^2t^2)^b(Xt^2)^c.
   \]

   Its norm-summability and HasSum follow from three genuine convergent
   geometric series. The same argument applies to the other cones.
4. Attach the actual depth distribution. On depth-insensitive rows the
   distribution has total mass one, including collision points that happen
   to lie in those rows. On 3b/8b its mass is
   \((q-2)/(q-1)=(1-2t^2)/(1-t^2)\). On 3c/8c the sum over depths at least
   one is \(q^{-1}(1-q^{-1})^{-1}=t^2/(1-t^2)\).
5. Use the common summable depth majorant from `MasterSeries` to establish
   norm-summability on the full base-times-depth family before interchanging
   sums. This step includes every depth, rather than inserting a total mass
   after an unjustified rearrangement.
6. `i1CellIndex` is a disjoint, exhaustive 17-cell classification of the
   entire integer lattice. Its 17 `_cell_iff` lemmas state the exact source
   inequalities; the additional cells only split 3a and 8a by parity.
   `i1PartitionEquiv` is the full lattice equivalence. The new depth
   equivalences include both inverse laws.
7. Restore the exact stored fractions using `i1r*_value_eq`, merge the two
   parity pairs, and obtain `hasSum_i1_master`. Its left side is the complete
   independently defined `masterTerm ... 1`, with no row-value assumptions.

## Parameter scope and remaining bridges

The I1 assembly uses nonzero (t,\delta,q,q-1), the relation (qt^2=1),
and `GeometricRange t δ U V T`: all six norms

\[
|t^2|,\ |\delta TVt|,\ |TVt/\delta|,\ |(TV)^2t^2|,
\ |TUt^2|,\ |TUt^4|
\]

are strictly below one. These are analytic convergence assumptions, not
asserted row values or unproved integrability. The root parameter development
derives them on the stated damped and undamped interior ranges. The norm
condition involving (TVt/\delta) fails at the undamped special endpoint;
this report makes no ordinary endpoint-series convergence assertion.

This I1 result is a component of Stage A. By itself it supplies neither the
full three-shell series evaluation nor an Abel limit, Haar identity, or
spherical-coefficient identification. Those conclusions require the other
shells and the separate assembly and analytic bridges.

The strongest I1 declaration is `FourierJacobi.Analysis.i1_master_of_bounds`.
For real (q,t,T) and complex (\delta,U,V), it assumes

\[
 qt^2=1,\quad 0<t<1,\quad 0\le T\le1,\quad
 t\le|\delta|\le1,\quad Tt<|\delta|,\quad |U|=|V|=1.
\]

It concludes both norm-summability of the entire `masterTerm ... 1` family
on (\mathbb Z^3\times\mathbb N), and its `HasSum` to

\[
 \sum_{\nu=10}^{24}\operatorname{regionTerms}(t,\delta,TU,TV,\nu).
\]

In particular, (q>2, t=q^{-1/2}) satisfies the arithmetic part. Damping
(0<T<1) permits (t\le|\delta|\le1), and the undamped case (T=1)
permits (t<|\delta|\le1). Auxiliary nonzero conditions follow in
`i1_basic_nonzero` and are absent from this natural-parameter theorem.

## Verification record

`I1Complete.lean`, `I1Partition.lean`, `I1Assembly.lean`, and
`I1SourceRows.lean` have all passed direct checks with the pinned Lean
toolchain and `-DwarningAsError=true`. Every command activated
`build/fourier-jacobi-core-lean/direct-env.ps1`; exported oleans remain
under the workspace build cache, outside the publication. No new toolchain
or dependency was installed, and no source pin was changed.

The parent task's final full build, exhaustive
axiom audit, and source-hash manifest are the authoritative verification
record for all delivered I1 modules; see the new publication's verification
directory. No hosted CI run is asserted here.

`scripts/generate-i1-series.py` is an authoring aid, not a reproduction step.
It generated the cone-map and proof drafts; the delivered `I1Complete.lean`
also contains subsequent manual elaboration, import, and linter fixes.
The script does not recreate the final checked file verbatim and must not be
rerun over it as part of verification. The delivered Lean sources and Lake
commands are the reproducible proof development.
