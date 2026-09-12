# Dependencies of the completed explicit-kernel theorem

The necessary chain starts with an independently defined valuation summand and
an independently defined kernel on actual local-field matrices. It proves their
relationship. It contains no structure field asserting an evaluation,
integrability, a row sum, or a limit.

## Mathematical dependency order

| Layer | Principal modules | Role |
|---|---|---|
| Exact source algebra and integer minima | `Algebra/RegionSum`, `Algebra/WeylData`, `Algebra/WeylSum`, `Algebra/FiniteCalculation`, `Valuations/Cartan` | Preserved finite calculation and integer entry/minor indices |
| Independent master family | `Analysis/MasterSeries`, `Analysis/CoreParameters` | Correct central coefficients, collision weights, integer powers, nonnegative exponents, natural convergence bounds, exact \(E_q\) |
| All infinite regions | `I0Complete`, `I0Master`; `I1Complete`, `I1Partition`, `I1Assembly`, `I1SourceRows`; the `I2` modules through `I2Master` | Actual row `HasSum` proofs, both inverse laws, depth/parity partitions, norm summability |
| Complete series and limits | `LatticeCore`, `MasterDamping`, `RationalLimits`, `PaperDomain`, `LatticeLimits` | Full norm-summable family, row-damped rational identity, unscaled evaluation, ordinary interior Abel convergence, signed endpoint Abel limit |
| Actual local-field infrastructure | `Valuations/LocalField`, `Valuations/MatrixBridge`, `Valuations/LocalMatrix`, `Measure/LocalHaar`, `Measure/NullSets` | Preserved canonical valuation, matrix-minimum and actual Haar/null-set results |
| Actual shell measures | `Measure/IntegerShells`, `MultiplicativeHaar`, `PaperMultiplicativeHaar`, `UnitScaling`, `ShellCollision`, `JointCollision` | Integer shell measures and actual transported collision probabilities with source normalization |
| Actual kernel and partition | `Valuations/KernelIndices`, `KernelShells`, `Analysis/ExplicitKernel`, `HaarKernel`, `HaarLatticePartition` | Finite ordered measurable indices, independent kernel and integrals, exact disjoint measurable cells, almost-everywhere cover |
| Actual cell identities | `HaarCellMass`, `HaarCellValue`, `HaarCellMaster` | Proved field-cell mass and value multiply to the independent master summand |
| Integration and final transfer | `FiberIntegration`, `CentralWeylSeries`, `HaarCoreAssembly`, `HaarLimits` | Integrability from a summable majorant, justified integral/sum interchange, Haar-to-series identity, both corrected comparisons |

Paths without a directory prefix in the lower rows are under the directory
named earlier in that row or under `FourierJacobi/Analysis`; see
[PROOF_GUIDE.md](PROOF_GUIDE.md) for direct entry points.
The [fifty-row source map](docs/source-map.md) records every row and restoration.

The finite core identity and four infinite I0 rows are inherited from v2.
Completing the remaining 46 rows and proving the full infinite and Haar
assemblies is new. The Haar proof uses the elementary finite Weyl bound from
the actual indices; no representation-theoretic coefficient estimate is assumed.

The source's normalized spherical coefficient, the Cartan/Macdonald
identification with this kernel, and any parameter-wall extension are not
dependencies silently supplied as hypotheses. They remain outside the completed
result. The original period, its intertwining/unfolding argument, stabilized
central truncation when not needed for these explicit integrals, and later local
\(L\)-factors are outside this necessary chain. Retained baseline modules about
broader goals do not enlarge the new theorem's claim.

## Pinned software and verification

- Lean: `leanprover/lean4:v4.33.1`.
- mathlib: `0df444a360eaa60ab8c11dca51a86af692955474`.
- Transitive dependency revisions: `lake-manifest.json`.
- Build configuration: `lakefile.toml`; automatic check:
  `.github/workflows/lean.yml`.
- Build and audit entry points: [REPRODUCE.md](REPRODUCE.md).
- Current checked-source hashes and verification outputs:
  [VERIFICATION.md](VERIFICATION.md).

Dependencies and build products remain outside the publication sources in
project-local writable storage during workspace verification. They are
reproducible from the retained pins and manifest. No toolchain pin was changed,
and no new global installation is required by this publication.

Only `propext`, `Classical.choice`, and `Quot.sound` are acceptable
foundational axioms. The final integrated build and exhaustive audit passed;
their source-matched outputs are in the separate verification record.
No hosted CI run is asserted.


