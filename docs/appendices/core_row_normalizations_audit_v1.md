# Independent audit of all fifty row restorations, version 1

All fifty final source fractions match the exact stored restored fractions. The source was read independently of the JSON: each literal final TeX right side was extracted by its `Ireqqν` label, and its coefficient was transcribed into the `RAW` table in `audit_core_row_normalizations_v1.py`. The literal snippets, transcriptions, restoration factors and zero differences are retained in `core_row_normalizations_audit_v1.json`.

This is a source transcription and normalization check. SymPy exact rational arithmetic is supplementary evidence, not a Lean proof certificate or a proof that an infinite row sum or integral equals its final displayed fraction. The separate Lean infinite-row proofs and the final exhaustive audit supply those formal results where completed.

## Conventions and conversion

The table removes the common `A_i/C_q` from each final source coefficient. Use `t=q^(-1/2)`, `S=1-t²`, `d=δ`, `U=γ² L_i²`, and `V=M_i`. Here `P=1-d V t`, `N=1-V t/d`, `E=1-V²t²`, `F=1-Ut²`, and `G=1-Ut⁴`. Products count factors with their original multiplicities.

The source defines `E0ν=S I0ν`, `E1ν=-q^(-1) I1ν`, and `E2ν=S I2ν`. Their restoration factors are therefore `1/S`, `-1/t²`, and `1/S`. For the paper range `q>2`, these scalar divisions are nonsingular. The stored JSON and `Algebra.regionTerm0`–`regionTerm49` already contain these restorations. Applying them again would change the mathematics.

Each row below has exact symbolic difference zero after applying the indicated restoration, substituting `S=1-t²`, and comparing with the stored expression. The Lean algebra map is in namespace `FourierJacobi.Algebra`.

| Index | Source label / line | Raw source coefficient of `A_i/C_q` | Restore | Exact Lean fraction | Infinite proof provenance |
|---:|---|---|---|---|---|
| 0 | `I0eqq1` / 3251 | `S/P` | `1/S` | `regionTerm0` | inherited v2 |
| 1 | `I0eqq2` / 3263 | `S**2*U*t**4/(G*P)` | `1/S` | `regionTerm1` | inherited v2 |
| 2 | `I0eqq3` / 3276 | `S**2*V*t**2*(V + 1)/(E*P)` | `1/S` | `regionTerm2` | new checked I0Complete |
| 3 | `I0eqq4` / 3292 | `S**3*U*t**2/(E*F*P)` | `1/S` | `regionTerm3` | new checked I0Complete |
| 4 | `I0eqq5` / 3318 | `S**3*U**2*t**6/(F*G*P)` | `1/S` | `regionTerm4` | new checked I0Complete |
| 5 | `I0eqq6` / 3334 | `S*V*t/(N*d)` | `1/S` | `regionTerm5` | inherited v2 |
| 6 | `I0eqq7` / 3346 | `S**2*U*V*t**5/(G*N*d)` | `1/S` | `regionTerm6` | inherited v2 |
| 7 | `I0eqq8` / 3359 | `S**2*V**2*t**3*(V + 1)/(E*N*d)` | `1/S` | `regionTerm7` | new checked I0Complete |
| 8 | `I0eqq9` / 3373 | `S**3*U*V*t**3/(E*F*N*d)` | `1/S` | `regionTerm8` | new checked I0Complete |
| 9 | `I0eqq10` / 3398 | `S**3*U**2*V*t**7/(F*G*N*d)` | `1/S` | `regionTerm9` | new checked I0Complete |
| 10 | `I1eqq1` / 3554 | `-S*U*d*t**3/P` | `-1/t**2` | `regionTerm10` | separate analytic proof; not certified here |
| 11 | `I1eqq2` / 3568 | `-S**2*U*V*d*t**5/(G*P)` | `-1/t**2` | `regionTerm11` | separate analytic proof; not certified here |
| 12 | `I1eqq3a` / 3584 | `-S**2*U*V*d*t**5*(V + 1)/(E*P)` | `-1/t**2` | `regionTerm12` | separate analytic proof; not certified here |
| 13 | `I1eqq3b` / 3598 | `-S**2*U*V*d*t**3*(1 - 2*t**2)/(E*P)` | `-1/t**2` | `regionTerm13` | separate analytic proof; not certified here |
| 14 | `I1eqq3c` / 3621 | `-S**2*V**2*d*t**3/(E*P)` | `-1/t**2` | `regionTerm14` | separate analytic proof; not certified here |
| 15 | `I1eqq4` / 3640 | `-S**3*U**2*V*d*t**5/(E*F*P)` | `-1/t**2` | `regionTerm15` | separate analytic proof; not certified here |
| 16 | `I1eqq5` / 3667 | `-S**3*U**2*V*d*t**7/(F*G*P)` | `-1/t**2` | `regionTerm16` | separate analytic proof; not certified here |
| 17 | `I1eqq6a` / 3685 | `-S*V*t**4` | `-1/t**2` | `regionTerm17` | separate analytic proof; not certified here |
| 18 | `I1eqq6b` / 3694 | `-S*U*t**3/(N*d)` | `-1/t**2` | `regionTerm18` | separate analytic proof; not certified here |
| 19 | `I1eqq7` / 3707 | `-S**2*U*t**4/(G*N)` | `-1/t**2` | `regionTerm19` | separate analytic proof; not certified here |
| 20 | `I1eqq8a` / 3720 | `-S**2*U*t**4*(V + 1)/(E*N)` | `-1/t**2` | `regionTerm20` | separate analytic proof; not certified here |
| 21 | `I1eqq8b` / 3735 | `-S**2*U*t**2*(1 - 2*t**2)/(E*N)` | `-1/t**2` | `regionTerm21` | separate analytic proof; not certified here |
| 22 | `I1eqq8c` / 3756 | `-S**2*V*t**2/(E*N)` | `-1/t**2` | `regionTerm22` | separate analytic proof; not certified here |
| 23 | `I1eqq9` / 3777 | `-S**3*U**2*t**4/(E*F*N)` | `-1/t**2` | `regionTerm23` | separate analytic proof; not certified here |
| 24 | `I1eqq10` / 3803 | `-S**3*U**2*t**6/(F*G*N)` | `-1/t**2` | `regionTerm24` | separate analytic proof; not certified here |
| 25 | `I2eqq1a` / 3982 | `-S*U**2*d**2*t**4/P` | `1/S` | `regionTerm25` | separate analytic proof; not certified here |
| 26 | `I2eqq1b` / 3994 | `-S*U*V*d*t**5` | `1/S` | `regionTerm26` | separate analytic proof; not certified here |
| 27 | `I2eqq2` / 4005 | `-S**2*U*V*d*t**3/(G*P)` | `1/S` | `regionTerm27` | separate analytic proof; not certified here |
| 28 | `I2eqq3a` / 4020 | `-S**2*U**2*d*t**3*(V*t**2 + 1)/(E*P)` | `1/S` | `regionTerm28` | separate analytic proof; not certified here |
| 29 | `I2eqq3b` / 4033 | `-S**2*U**2*V*d*t**3*(1 - 2*t**2)/(E*P)` | `1/S` | `regionTerm29` | separate analytic proof; not certified here |
| 30 | `I2eqq3c` / 4056 | `-S**3*U*V**2*d*t**3/(E*P)` | `1/S` | `regionTerm30` | separate analytic proof; not certified here |
| 31 | `I2eqq3d` / 4077 | `-S**2*V**3*d*t**3/(E*P)` | `1/S` | `regionTerm31` | separate analytic proof; not certified here |
| 32 | `I2eqq4` / 4095 | `-S**3*U**3*V*d*t**5/(E*F*P)` | `1/S` | `regionTerm32` | separate analytic proof; not certified here |
| 33 | `I2eqq5` / 4120 | `-S**3*U**2*V*d*t**5/(F*G*P)` | `1/S` | `regionTerm33` | separate analytic proof; not certified here |
| 34 | `I2eqq6a` / 4138 | `-S*V**2*t**4` | `1/S` | `regionTerm34` | separate analytic proof; not certified here |
| 35 | `I2eqq6aa` / 4147 | `-S**2*U*V*t**4` | `1/S` | `regionTerm35` | separate analytic proof; not certified here |
| 36 | `I2eqq6aaa` / 4158 | `-S**2*U**2*t**4/G` | `1/S` | `regionTerm36` | separate analytic proof; not certified here |
| 37 | `I2eqq6b` / 4170 | `-S*U*V*t**5/d` | `1/S` | `regionTerm37` | separate analytic proof; not certified here |
| 38 | `I2eqq6bb` / 4180 | `-S**2*U**2*t**3/d` | `1/S` | `regionTerm38` | separate analytic proof; not certified here |
| 39 | `I2eqq6bbb` / 4191 | `-S**3*U**2*V*t**5/(G*d)` | `1/S` | `regionTerm39` | separate analytic proof; not certified here |
| 40 | `I2eqq6c` / 4203 | `-S*U**2*t**4/(N*d**2)` | `1/S` | `regionTerm40` | separate analytic proof; not certified here |
| 41 | `I2eqq6cc` / 4216 | `-S**2*U**2*V*t**4/(N*d**2)` | `1/S` | `regionTerm41` | separate analytic proof; not certified here |
| 42 | `I2eqq6ccc` / 4228 | `-S**3*U**2*V**2*t**6/(G*N*d**2)` | `1/S` | `regionTerm42` | separate analytic proof; not certified here |
| 43 | `I2eqq7` / 4240 | `-S**2*U*V*t**3/(G*N*d)` | `1/S` | `regionTerm43` | separate analytic proof; not certified here |
| 44 | `I2eqq8a` / 4253 | `-S**2*U**2*t**4*(V + 1)/(E*N)` | `1/S` | `regionTerm44` | separate analytic proof; not certified here |
| 45 | `I2eqq8b` / 4269 | `-S**2*U**2*t**2*(1 - 2*t**2)/(E*N)` | `1/S` | `regionTerm45` | separate analytic proof; not certified here |
| 46 | `I2eqq8c` / 4289 | `-S**3*U*V*t**2/(E*N)` | `1/S` | `regionTerm46` | separate analytic proof; not certified here |
| 47 | `I2eqq8d` / 4313 | `-S**2*V**2*t**2/(E*N)` | `1/S` | `regionTerm47` | separate analytic proof; not certified here |
| 48 | `I2eqq9` / 4332 | `-S**3*U**3*t**4/(E*F*N)` | `1/S` | `regionTerm48` | separate analytic proof; not certified here |
| 49 | `I2eqq10` / 4358 | `-S**3*U**3*t**6/(F*G*N)` | `1/S` | `regionTerm49` | separate analytic proof; not certified here |

## Independent I0 completion and endpoints

The four inherited I0 evaluations are source cases 1, 2, 6, and 7 only. The other six I0 cases, including the two parity decompositions, are now proved in `Analysis/I0Complete.lean`. Its `hasSum_i0_region` covers all ten original domains; `i0Region_partition` proves disjointness and exhaustion; `summable_norm_i0_full` proves norm summability of the entire integer lattice; and `hasSum_i0_full` evaluates its independently defined summand. I0Complete passed the pinned direct Lean check with warnings as errors and was exported for the parent publication build.

Damping belongs in each unsummed monomial: substitute `U→TU`, `V→TV` in these row fractions only after proving their actual damped sums. No restoration or damping substitution is applied to an already simplified closed core in this audit. At `δ=εt`, an undamped geometric ratio can have modulus one even where its denominator is nonzero. This table certifies no ordinary special-endpoint series convergence, no exceptional-parameter continuation, and no signed whole-core Abel limit. Their precise status belongs to the final statement and bridge reports.

## Reproduction and source identity

Run from the workspace root with the existing project virtual environment:

```powershell
.venv/Scripts/python.exe 'Fourier Jacobi project/verification/audit_core_row_normalizations_v1.py'
```

SymPy version: `1.14.0`. Result: **50/50 exact differences zero**.

Complete TeX SHA256: `8609500624491e699d064331361717b74e9f035ca1f505e400362c3511cec387`.

Stored JSON SHA256: `8e8d78adb74230e98969bddb5af260ab90d75878645fbf0b0df1c55d32f0a9b3`.

The original TeX/PDF, expanded versions, and v1/v2 snapshots were not edited. No dependency or global installation was changed.
