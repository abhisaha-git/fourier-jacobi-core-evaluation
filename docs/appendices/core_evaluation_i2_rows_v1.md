# I2 source rows, infinite sums, and depth bookkeeping

This report concerns only the twenty-five `I2eq4` rows in the preserved
`section_2_expanded_complete.tex`, beginning at line 3866. The mathematical
source remains unchanged. The new development is in
`publications/fourier-jacobi-core-evaluation/FourierJacobi/Analysis/`.

The individually checked spatial results are in `I2Complete.lean`; their
domain bijections and Cartan calculations are in `I2Domains.lean`.
`I2Assembly.lean` and `I2Master.lean` supply the additional depth and ambient
lattice interfaces. Their verification is recorded by the publication's
final build and exhaustive axiom audit; this report is not a substitute for
those checks.

## Verified full I2 lattice statement

Let `q,t,d,U,V,T ∈ ℂ` satisfy `t≠0`, `d≠0`, `q≠0`,
`q-1≠0`, `q-2≠0`, and `qt²=1`. Assume that each of
`t²`, `dTVt`, `TVt/d`, `(TV)²t²`, `TUt²`, and `TUt⁴` has norm
strictly less than one. These six inequalities are exactly
`GeometricRange t d U V T`.

Then the family
`(k,j,h,c) ↦ masterTerm q t d U V T 2 (k,j,h,c)` on
`ℤ × ℤ × ℤ × ℕ` is norm summable and has sum
`∑ ν : Fin 25, Algebra.regionTerms t d (T*U) (T*V) (25+ν)`.
Here the last index is made precise by `i2Offset : Fin 25 → Fin 50`.
The Lean declarations are
`FourierJacobi.Analysis.summable_norm_i2_master` and
`FourierJacobi.Analysis.hasSum_i2_master` in `I2Master.lean`.

The independent summand is the integer-minimum Cartan shell, with
coefficient `-q`, multiplied by the true cancellation weight.
Off `2h=j-2` its only nonzero depth is `c=0`, of weight one.
On `2h=j-2` the depth-zero weight is `(q-2)/(q-1)` and the
positive-depth weight is `q^(-c)`. Thus the left side is defined without
reference to any of the 25 stored fractions. This is a complete theorem
for the I2 component of the master lattice; the full three-shell/eight-Weyl
assembly is a separate declaration in the containing publication.

## Normalization and exact source-to-Lean map

Write `R = 1-t²`, `P = 1-dVt`, `N = 1-Vt/d`, `E = 1-V²t²`,
`F = 1-Ut²`, and `G = 1-Ut⁴`. Here `t²=q⁻¹`, `U=γ²Lᵢ²`,
`V=Mᵢ`, and `d=δ`. The common Weyl factor `Aᵢ/Cq` is omitted.
Every entry below is the **actual I2 contribution**. It equals the last
displayed source fraction `E₂,ν` divided by `R`, as required by
`expanded:row-renormalization-I2`. No second restoration is applied.
For damping, replace `U,V` by `TU,TV` in each entry.

| Source label | Spatial row | Stored index | Actual restored fraction |
|---|---:|---:|---|
| `I2eqq1a` | 0 | 25 | `-U²d²t⁴/P` |
| `I2eqq1b` | 1 | 26 | `-UVdt⁵` |
| `I2eqq2` | 2 | 27 | `-UVdt³R/(GP)` |
| `I2eqq3a` | 3 | 28 | `-dU²t³R(1+Vt²)/(EP)` |
| `I2eqq3b` | 4 | 29 | `-dU²Vt³R(1-2t²)/(EP)` |
| `I2eqq3c` | 5 | 30 | `-dUV²t³R²/(EP)` |
| `I2eqq3d` | 6 | 31 | `-dV³t³R/(EP)` |
| `I2eqq4` | 7 | 32 | `-dU³Vt⁵R²/(EFP)` |
| `I2eqq5` | 8 | 33 | `-dU²Vt⁵R²/(FGP)` |
| `I2eqq6a` | 9 | 34 | `-V²t⁴` |
| `I2eqq6aa` | 10 | 35 | `-UVt⁴R` |
| `I2eqq6aaa` | 11 | 36 | `-U²t⁴R/G` |
| `I2eqq6b` | 12 | 37 | `-UVt⁵/d` |
| `I2eqq6bb` | 13 | 38 | `-U²t³R/d` |
| `I2eqq6bbb` | 14 | 39 | `-U²Vt⁵R²/(Gd)` |
| `I2eqq6c` | 15 | 40 | `-U²t⁴/(Nd²)` |
| `I2eqq6cc` | 16 | 41 | `-U²Vt⁴R/(Nd²)` |
| `I2eqq6ccc` | 17 | 42 | `-U²V²t⁶R²/(GNd²)` |
| `I2eqq7` | 18 | 43 | `-UVt³R/(GNd)` |
| `I2eqq8a` | 19 | 44 | `-U²t⁴R(1+V)/(EN)` |
| `I2eqq8b` | 20 | 45 | `-U²t²R(1-2t²)/(EN)` |
| `I2eqq8c` | 21 | 46 | `-UVt²R²/(EN)` |
| `I2eqq8d` | 22 | 47 | `-V²t²R/(EN)` |
| `I2eqq9` | 23 | 48 | `-U³t⁴R²/(EFN)` |
| `I2eqq10` | 24 | 49 | `-U³t⁶R²/(FGN)` |

Each row `X` has declarations `i2CaseXEquiv`, `i2CaseX_cartan`,
`i2_caseX_reindexed`, `summable_norm_i2_caseX`, and
`hasSum_i2_caseX_regionTerm`, all in `FourierJacobi.Analysis`.
The final equality in each HasSum theorem uses the **existing**
`Algebra.regionTerm25` through `Algebra.regionTerm49`; those stored
fractions are inherited data, whereas the domain sums are new proofs.

The uniform ambient-row declarations are `hasSum_i2_rowTerm` and
`summable_norm_i2_rowTerm` in `I2Ambient.lean`. Here `i2RowTerm` is the
original `masterTerm` at shell index 2, restricted by the conjunction of
the displayed spatial inequalities and the prescribed depth condition,
and extended by zero to all of `ℤ × ℤ × ℤ × ℕ`.
`i2RegionTerm_eq_regionTerms` proves its target is exactly stored row
`25+ν`. The final interfaces are `hasSum_i2_master` and
`summable_norm_i2_master`; `i2_rows_partition` proves that the ambient
rows are disjoint and exhaustive before they are assembled.

## Unsummed monomial parameter table

For this table set `A=TU`, `B=TV`, and use the ratio symbols
`ρQ=t²`, `ρP=dBt`, `ρN=Bt/d`, `ρE=B²t²`, `ρF=At²`, and `ρG=At⁴`.
These are ratios, distinct from the denominator symbols used above.
The constant determined by a tuple `(k₀,e₀,n₀,b₀)` is
`Cν=-q(1-t²)² d^k₀ t^e₀ A^n₀ B^b₀ wν`, where
`wν=(q-2)/(q-1)` for rows 4 and 20, `wν=q⁻¹` for rows 5 and 21,
`wν=q⁻²/(1-q⁻¹)` for rows 6 and 22, and `wν=1` otherwise.
If the listed ratios are `x,y,z`, the reindexed term is
`Cν x^a y^b z^c`, with all free coordinates nonnegative.
Rows 3 and 19 also have a coordinate `e∈Fin 2`, with the indicated
factor raised to `e`. A negative `k₀` denotes an integer power of `d`.

| ν | Source suffix | `(k₀,e₀,n₀,b₀)` | Ratios in free-coordinate order | Parity factor |
|---:|---|---|---|---|
| 0 | 1a | `(2,6,2,0)` | `ρP,ρQ,ρQ` | |
| 1 | 1b | `(1,7,1,1)` | `ρQ,ρQ` | |
| 2 | 2 | `(1,5,1,1)` | `ρP,ρQ,ρG` | |
| 3 | 3a | `(1,5,2,0)` | `ρP,ρE,ρQ` | `Bt²` |
| 4 | 3b | `(1,5,2,1)` | `ρP,ρE` | |
| 5 | 3c | `(1,3,1,2)` | `ρP,ρE` | |
| 6 | 3d | `(1,1,0,3)` | `ρP,ρE` | |
| 7 | 4 | `(1,7,3,1)` | `ρP,ρE,ρF` | |
| 8 | 5 | `(1,7,2,1)` | `ρP,ρF,ρG` | |
| 9 | 6a | `(0,6,0,2)` | `ρQ,ρQ` | |
| 10 | 6aa | `(0,6,1,1)` | `ρQ` | |
| 11 | 6aaa | `(0,6,2,0)` | `ρQ,ρG` | |
| 12 | 6b | `(-1,7,1,1)` | `ρQ,ρQ` | |
| 13 | 6bb | `(-1,5,2,0)` | `ρQ` | |
| 14 | 6bbb | `(-1,7,2,1)` | `ρG` | |
| 15 | 6c | `(-2,6,2,0)` | `ρN,ρQ,ρQ` | |
| 16 | 6cc | `(-2,6,2,1)` | `ρN,ρQ` | |
| 17 | 6ccc | `(-2,8,2,2)` | `ρN,ρG` | |
| 18 | 7 | `(-1,5,1,1)` | `ρN,ρQ,ρG` | |
| 19 | 8a | `(0,6,2,0)` | `ρN,ρE,ρQ` | `B` |
| 20 | 8b | `(0,4,2,0)` | `ρN,ρE` | |
| 21 | 8c | `(0,2,1,1)` | `ρN,ρE` | |
| 22 | 8d | `(0,0,0,2)` | `ρN,ρE` | |
| 23 | 9 | `(0,6,3,0)` | `ρN,ρE,ρF` | |
| 24 | 10 | `(0,8,3,0)` | `ρN,ρF,ρG` | |

Each line is the equality proved by `i2_caseX_reindexed`; the table is
not used as an assumed summation formula. The source-generation script
computes the affine exponents, and Lean proves their equalities using
integer arithmetic and checks the resulting power identity.

## Mathematical proof and dependency order

The source table defines simultaneous inequalities on integer valuations
`k,j,h`. They are preserved verbatim as `i2SpatialPredicate`. The ordinary
rows retain every cancellation depth. Rows 3b/8b require `c=0`, rows
3c/8c require `c=1`, and rows 3d/8d require `c≥2`.

First substitute these inequalities into the inherited integer Cartan
table `tableTwo`, already proved equal to the entry/minor minima. The
resulting Cartan indices are independent of depth within each prescribed
row. This independence also applies to ordinary rows which happen to meet
the collision locus. Thus a collision inside, for example, row 6a is not
silently counted as an off-collision point.

Every original spatial region is then put in bijection with one, two, or
three independent nonnegative integers. The two parity rows use
`Fin 2 × ℕ × ℕ × ℕ`. Both inverse laws are Lean proofs. To illustrate the
nontrivial substitutions, write the free coordinates as `a,b,c≥0` and
the parity coordinate as `e∈{0,1}`:

* Row 3a: `k=a+1`, `j=-2k-2b-e-1`, `h=-k-b-1+c`.
* Row 8a: `k=-a`, `j=-2b-e-2`, `h=-b-e-1+c`.
* Row 4: `k=a+1`, `j=-2k-2b-c-3`, `h=-k-b-c-3`.
* Row 9: `k=-a`, `j=-2b-c-3`, `h=-b-c-3`.
* Rows 3b–3d: `k=a+1`, `j=-2k-2b-2`, `h=-k-b-2`.
* Rows 8b–8d: `k=-a`, `j=-2b-2`, `h=-b-2`.

These substitutions act on the unsummed Cartan shell monomial, including
`(TU)^(ℓ/2)(TV)^b`. All original exponents are integer powers. The
substitutions prove that the Cartan exponents become nonnegative affine
forms, after which integer powers agree with ordinary natural powers.
Negative valuations of `a` continue to contribute inverse powers of `d`.

The possible infinite geometric ratios are
`t²`, `dTVt`, `TVt/d`, `(TV)²t²`, `TUt²`, and `TUt⁴`.
Their strict norm bounds prove norm summability on the unordered product
index before its sum is rearranged. The parity summation contributes
`1+TVt²` in row 3a and `1+TV` in row 8a.

Next sum the true cancellation weights. Off a collision only depth zero
has weight one. On a collision the weights are
`p₀=(q-2)/(q-1)` and `p_c=q^(-c)` for `c≥1`. Their total is one. The
depth masses for the b/c/d collision rows are respectively
`(q-2)/(q-1)`, `q⁻¹`, and `q⁻²/(1-q⁻¹)`. These are derived probability
sums; they are not asserted row evaluations. Multiplying the depth sum
by the constant Cartan shell gives exactly `i2SpatialTerm`.

The coefficient multiplying every I2 shell is `-q`. Cancelling `qt²=1`
and the genuine nonzero geometric denominators in the convergent range
gives the twenty-five restored fractions above. The finite row identity
alone is not used to define the independent lattice sum.

For exhaustiveness, first split at `k≥1`, `k=0`, and `k≤-1`.
On the first piece split at `j≥-2k`, and then at `h≥-k` or
`h≥k+j` as applicable. On the second split at `j≥-1` and `h≥j`;
on the third split at `j≥0`, `j=-1`, and `j≤-2`.
The remaining low-`j` pieces use the three alternatives
`2h≥j-1`, `2h=j-2`, and `2h≤j-3`. The middle alternative is
further split by `c=0`, `c=1`, and `c≥2`.
The finite decisions separating `k=1`, `k=-1`, `j=-1`, and the
adjacent integer boundary values select exactly the source rows.
`i2Classify_mem` proves the selected row contains the input;
`i2Classify_eq_of_mem` proves every containing row is the selected one.
Together these prove uniqueness, including all boundary and depth cases.

The passage from spatial sums to the ambient lattice uses a uniform
summable depth majorant. For each spatial point the absolute collision
weight is bounded by the same depth sequence, independently of `j,h`.
Its sum is finite when `‖q⁻¹‖<1`. Multiplying this sequence by the
summable spatial norm gives absolute summability on the product index.
Cartan depth independence then identifies that product with the original
row term. An explicit equivalence between `I2SpatialRow ν × ℕ` and the
corresponding subtype of the four-coordinate lattice has both inverse
laws equal by reflexivity; extension by zero yields the ambient row.

Finally, uniqueness of the partition says that the sum of the 25 row
terms is the original master term at every lattice point, and the sum
of their norms is its norm. The finite sum of the norm-summable row
families proves norm summability of the full I2 family. Only then does
the sum of the 25 row HasSum statements yield its restored finite-row
value. Thus the final assembly does not assign a value to a nonsummable
`tsum` and does not posit a row-evaluation hypothesis.

## Range, endpoint, and bridge limits

The spatial row theorems state their exact strict geometric norm bounds.
The full lattice assembly additionally uses `q≠0`, `q-1≠0`, and
`q-2≠0`; each follows from the intended real assumption `q>2`.
It uses nonzero `t,d`, and `qt²=1`. Broader complex-q parameter coverage
is not claimed by this helper interface.

At the literal special endpoint `T=1`, `d=±t`, and `|V|=1`, the ratio
`TVt/d` has modulus one. These row proofs therefore do not assert
ordinary endpoint summability or evaluate a nonsummable tsum. The full
special target must be obtained as the one-sided limit of the damped
signed Weyl combination. A nonzero rational denominator alone does not
replace this limit argument.

These I2 results concern the independently defined lattice family. Haar
shell measures and integral/sum interchange, and the further identification
with the paper's normalized spherical coefficient, are separate bridges.
