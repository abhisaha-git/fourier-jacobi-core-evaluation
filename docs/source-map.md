# Source-to-Lean map for all fifty rows, version 1

Every index below is the zero-based `Algebra.regionTerms` index. All declaration names have prefix `FourierJacobi`. The precise original inequalities and depth predicates are in the named row modules; all reindexing maps have both inverse laws proved.

Write S=1−t², P=1−δVt, N=1−Vt/δ, E=1−V²t², F=1−Ut², G=1−Ut⁴. The raw column omits the common Aᵢ/C_q. To obtain each actual contribution, the source's E₀ rows are divided by S, its E₁ rows multiplied by −q=−1/t², and its E₂ rows divided by S. The stored fraction already contains this restoration. Damping replaces U,V by TU,TV in the unsummed monomial and then in its proved row fraction; it is never applied to the simplified E_q.

| Stored index | Source label (complete TeX line) | Raw source fraction | Restoration | Infinite HasSum proof | Provenance |
|---:|---|---|---|---|---|
| 0 | `I0eqq1` (3251) | `S/P` | `1/S` | `Analysis.hasSum_i0_case1_regionTerm` | inherited v2 |
| 1 | `I0eqq2` (3263) | `S**2*U*t**4/(G*P)` | `1/S` | `Analysis.hasSum_i0_case2_regionTerm` | inherited v2 |
| 2 | `I0eqq3` (3276) | `S**2*V*t**2*(V + 1)/(E*P)` | `1/S` | `Analysis.hasSum_i0_case3_regionTerm` | new I0Complete |
| 3 | `I0eqq4` (3292) | `S**3*U*t**2/(E*F*P)` | `1/S` | `Analysis.hasSum_i0_case4_regionTerm` | new I0Complete |
| 4 | `I0eqq5` (3318) | `S**3*U**2*t**6/(F*G*P)` | `1/S` | `Analysis.hasSum_i0_case5_regionTerm` | new I0Complete |
| 5 | `I0eqq6` (3334) | `S*V*t/(N*d)` | `1/S` | `Analysis.hasSum_i0_case6_regionTerm` | inherited v2 |
| 6 | `I0eqq7` (3346) | `S**2*U*V*t**5/(G*N*d)` | `1/S` | `Analysis.hasSum_i0_case7_regionTerm` | inherited v2 |
| 7 | `I0eqq8` (3359) | `S**2*V**2*t**3*(V + 1)/(E*N*d)` | `1/S` | `Analysis.hasSum_i0_case8_regionTerm` | new I0Complete |
| 8 | `I0eqq9` (3373) | `S**3*U*V*t**3/(E*F*N*d)` | `1/S` | `Analysis.hasSum_i0_case9_regionTerm` | new I0Complete |
| 9 | `I0eqq10` (3398) | `S**3*U**2*V*t**7/(F*G*N*d)` | `1/S` | `Analysis.hasSum_i0_case10_regionTerm` | new I0Complete |
| 10 | `I1eqq1` (3554) | `-S*U*d*t**3/P` | `-1/t**2` | `Analysis.hasSum_i1_source_case1` | new I1SourceRows |
| 11 | `I1eqq2` (3568) | `-S**2*U*V*d*t**5/(G*P)` | `-1/t**2` | `Analysis.hasSum_i1_source_case2` | new I1SourceRows |
| 12 | `I1eqq3a` (3584) | `-S**2*U*V*d*t**5*(V + 1)/(E*P)` | `-1/t**2` | `Analysis.hasSum_i1_source_case3a` | new I1SourceRows |
| 13 | `I1eqq3b` (3598) | `-S**2*U*V*d*t**3*(1 - 2*t**2)/(E*P)` | `-1/t**2` | `Analysis.hasSum_i1_source_case3b` | new I1SourceRows |
| 14 | `I1eqq3c` (3621) | `-S**2*V**2*d*t**3/(E*P)` | `-1/t**2` | `Analysis.hasSum_i1_source_case3c` | new I1SourceRows |
| 15 | `I1eqq4` (3640) | `-S**3*U**2*V*d*t**5/(E*F*P)` | `-1/t**2` | `Analysis.hasSum_i1_source_case4` | new I1SourceRows |
| 16 | `I1eqq5` (3667) | `-S**3*U**2*V*d*t**7/(F*G*P)` | `-1/t**2` | `Analysis.hasSum_i1_source_case5` | new I1SourceRows |
| 17 | `I1eqq6a` (3685) | `-S*V*t**4` | `-1/t**2` | `Analysis.hasSum_i1_source_case6a` | new I1SourceRows |
| 18 | `I1eqq6b` (3694) | `-S*U*t**3/(N*d)` | `-1/t**2` | `Analysis.hasSum_i1_source_case6b` | new I1SourceRows |
| 19 | `I1eqq7` (3707) | `-S**2*U*t**4/(G*N)` | `-1/t**2` | `Analysis.hasSum_i1_source_case7` | new I1SourceRows |
| 20 | `I1eqq8a` (3720) | `-S**2*U*t**4*(V + 1)/(E*N)` | `-1/t**2` | `Analysis.hasSum_i1_source_case8a` | new I1SourceRows |
| 21 | `I1eqq8b` (3735) | `-S**2*U*t**2*(1 - 2*t**2)/(E*N)` | `-1/t**2` | `Analysis.hasSum_i1_source_case8b` | new I1SourceRows |
| 22 | `I1eqq8c` (3756) | `-S**2*V*t**2/(E*N)` | `-1/t**2` | `Analysis.hasSum_i1_source_case8c` | new I1SourceRows |
| 23 | `I1eqq9` (3777) | `-S**3*U**2*t**4/(E*F*N)` | `-1/t**2` | `Analysis.hasSum_i1_source_case9` | new I1SourceRows |
| 24 | `I1eqq10` (3803) | `-S**3*U**2*t**6/(F*G*N)` | `-1/t**2` | `Analysis.hasSum_i1_source_case10` | new I1SourceRows |
| 25 | `I2eqq1a` (3982) | `-S*U**2*d**2*t**4/P` | `1/S` | `Analysis.hasSum_i2_rowTerm (ν=0)` | new I2Ambient |
| 26 | `I2eqq1b` (3994) | `-S*U*V*d*t**5` | `1/S` | `Analysis.hasSum_i2_rowTerm (ν=1)` | new I2Ambient |
| 27 | `I2eqq2` (4005) | `-S**2*U*V*d*t**3/(G*P)` | `1/S` | `Analysis.hasSum_i2_rowTerm (ν=2)` | new I2Ambient |
| 28 | `I2eqq3a` (4020) | `-S**2*U**2*d*t**3*(V*t**2 + 1)/(E*P)` | `1/S` | `Analysis.hasSum_i2_rowTerm (ν=3)` | new I2Ambient |
| 29 | `I2eqq3b` (4033) | `-S**2*U**2*V*d*t**3*(1 - 2*t**2)/(E*P)` | `1/S` | `Analysis.hasSum_i2_rowTerm (ν=4)` | new I2Ambient |
| 30 | `I2eqq3c` (4056) | `-S**3*U*V**2*d*t**3/(E*P)` | `1/S` | `Analysis.hasSum_i2_rowTerm (ν=5)` | new I2Ambient |
| 31 | `I2eqq3d` (4077) | `-S**2*V**3*d*t**3/(E*P)` | `1/S` | `Analysis.hasSum_i2_rowTerm (ν=6)` | new I2Ambient |
| 32 | `I2eqq4` (4095) | `-S**3*U**3*V*d*t**5/(E*F*P)` | `1/S` | `Analysis.hasSum_i2_rowTerm (ν=7)` | new I2Ambient |
| 33 | `I2eqq5` (4120) | `-S**3*U**2*V*d*t**5/(F*G*P)` | `1/S` | `Analysis.hasSum_i2_rowTerm (ν=8)` | new I2Ambient |
| 34 | `I2eqq6a` (4138) | `-S*V**2*t**4` | `1/S` | `Analysis.hasSum_i2_rowTerm (ν=9)` | new I2Ambient |
| 35 | `I2eqq6aa` (4147) | `-S**2*U*V*t**4` | `1/S` | `Analysis.hasSum_i2_rowTerm (ν=10)` | new I2Ambient |
| 36 | `I2eqq6aaa` (4158) | `-S**2*U**2*t**4/G` | `1/S` | `Analysis.hasSum_i2_rowTerm (ν=11)` | new I2Ambient |
| 37 | `I2eqq6b` (4170) | `-S*U*V*t**5/d` | `1/S` | `Analysis.hasSum_i2_rowTerm (ν=12)` | new I2Ambient |
| 38 | `I2eqq6bb` (4180) | `-S**2*U**2*t**3/d` | `1/S` | `Analysis.hasSum_i2_rowTerm (ν=13)` | new I2Ambient |
| 39 | `I2eqq6bbb` (4191) | `-S**3*U**2*V*t**5/(G*d)` | `1/S` | `Analysis.hasSum_i2_rowTerm (ν=14)` | new I2Ambient |
| 40 | `I2eqq6c` (4203) | `-S*U**2*t**4/(N*d**2)` | `1/S` | `Analysis.hasSum_i2_rowTerm (ν=15)` | new I2Ambient |
| 41 | `I2eqq6cc` (4216) | `-S**2*U**2*V*t**4/(N*d**2)` | `1/S` | `Analysis.hasSum_i2_rowTerm (ν=16)` | new I2Ambient |
| 42 | `I2eqq6ccc` (4228) | `-S**3*U**2*V**2*t**6/(G*N*d**2)` | `1/S` | `Analysis.hasSum_i2_rowTerm (ν=17)` | new I2Ambient |
| 43 | `I2eqq7` (4240) | `-S**2*U*V*t**3/(G*N*d)` | `1/S` | `Analysis.hasSum_i2_rowTerm (ν=18)` | new I2Ambient |
| 44 | `I2eqq8a` (4253) | `-S**2*U**2*t**4*(V + 1)/(E*N)` | `1/S` | `Analysis.hasSum_i2_rowTerm (ν=19)` | new I2Ambient |
| 45 | `I2eqq8b` (4269) | `-S**2*U**2*t**2*(1 - 2*t**2)/(E*N)` | `1/S` | `Analysis.hasSum_i2_rowTerm (ν=20)` | new I2Ambient |
| 46 | `I2eqq8c` (4289) | `-S**3*U*V*t**2/(E*N)` | `1/S` | `Analysis.hasSum_i2_rowTerm (ν=21)` | new I2Ambient |
| 47 | `I2eqq8d` (4313) | `-S**2*V**2*t**2/(E*N)` | `1/S` | `Analysis.hasSum_i2_rowTerm (ν=22)` | new I2Ambient |
| 48 | `I2eqq9` (4332) | `-S**3*U**3*t**4/(E*F*N)` | `1/S` | `Analysis.hasSum_i2_rowTerm (ν=23)` | new I2Ambient |
| 49 | `I2eqq10` (4358) | `-S**3*U**3*t**6/(F*G*N)` | `1/S` | `Analysis.hasSum_i2_rowTerm (ν=24)` | new I2Ambient |

## Partitions, inverse maps, and assembly

- I0: `Analysis.i0Region_partition`; the four inherited maps in `Analysis/ValuationSeries.lean` and the new `i0UpperRowEquiv`, `i0MiddleRowEquiv`, `i0LowerRowEquiv` in `Analysis/I0Complete.lean`. The upper map includes both parity classes. `hasSum_i0_master` inserts the actual r=0 depth rule into the four-coordinate family.
- I1: `Analysis/I1Partition.lean` proves unique membership in seventeen cells. `Analysis/I1Complete.lean` contains every cell Equiv, both inverse laws, Cartan substitution, geometric HasSum, and norm proof. The two parity pairs are combined in `I1SourceRows.lean`; `hasSum_i1_master` assembles the fifteen source rows with their true collision weights.
- I2: `Analysis.i2_rows_partition` proves unique membership in twenty-five spatial/depth rows. `I2Domains.lean` contains their exact Equiv maps and both inverse laws; `I2Complete.lean` their infinite spatial sums; `I2Assembly.lean` the true depth sums; `I2Ambient.lean` transport to the original full lattice. The generic row theorem reaches the exact stored entry through `i2RegionTerm_eq_regionTerms`, with `i2Offset ν=25+ν`. `hasSum_i2_master` performs the final disjoint assembly.
- `Analysis.summable_norm_weightedLatticeTerm` proves norm summability of the full eight-Weyl/three-central/integer-depth family. `hasSum_weightedLatticeTerm` justifies its grouping, and `latticeCore_eq_dampedRational` identifies its sum with all fifty rows.

## Source audit and proof status

`data/source-row-restorations.json` retains every literal final TeX right side, independent transcription, restoration, and exact symbolic difference. All fifty differences are zero. This SymPy check is supplementary source-matching evidence, not a Lean proof certificate. The declarations above prove the infinite identities; the final full build and axiom audit certify the delivered sources.

Complete TeX SHA256: `8609500624491e699d064331361717b74e9f035ca1f505e400362c3511cec387`.
Inherited stored-data SHA256: `8e8d78adb74230e98969bddb5af260ab90d75878645fbf0b0df1c55d32f0a9b3`.

## Endpoints

The row sums require strict geometric norm bounds. Their full natural range is 0≤T≤1, t≤|δ|≤1, Tt<|δ|. At δ=εt, only 0<T<1 is used for ordinary summation. The signed whole-product Abel theorem is `Analysis.infinite_lattice_special_abel`, on the generic unitary locus with α,β≠ε. Its ε=1 branch is a direct zero-product limit. Negative special α=−1 or β=−1 and Weyl walls are not covered by continuation; no ordinary endpoint summability is inferred from a nonzero denominator.

The detailed human row proofs and exact monomial tables are in the I0, I1, and I2 appendices under `docs/appendices/`. The separate proved `Analysis.paperExplicitHaarCore_eq_latticeCore` completes the actual explicit-kernel Haar bridge, and `Analysis.explicit_haar_special_abel` transfers the whole signed limit. The independently defined source spherical-coefficient identification remains unproved.
