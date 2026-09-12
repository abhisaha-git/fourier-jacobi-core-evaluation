# I2 source-generation aids

The reviewed Lean files delivered in `FourierJacobi/Analysis/` are the
authoritative proof sources. The scripts listed here are retained
authoring aids; byte-for-byte regeneration of the final reviewed sources
is not promised. They are not part of the Lean build or the proof trust
chain. They should not be run while a source verification is in progress.

| Script | Purpose |
|---|---|
| `generate-i2-domains.py` | Original spatial/depth predicates, affine domain maps, inverse laws, and Cartan substitutions |
| `generate-i2-partition-facts.py` | Concrete predicate simplification lemmas in `I2Predicates.lean` |
| `generate-i2-series.py` | Unsummed affine monomial identities, norm convergence, and spatial HasSum proofs |
| `generate-i2-assembly.py` | Actual collision-depth sums and row-family bridges |
| `generate-i2-partition.py` | Arithmetic classifier and disjoint/exhaustive partition proofs |

The scripts use Python's standard library, except `generate-i2-series.py`,
which also uses Sympy to prepare affine expressions. Lean independently
proves the generated integer exponent equalities and every resulting
identity, inverse law, and HasSum assertion. No numerical or symbolic
calculation is accepted as a proof certificate.

The ambient-lattice transport and finite assembly are maintained directly
in `I2Ambient.lean` and `I2Master.lean`. Ordinary reproduction of the
publication requires only its pinned Lean/Lake/mathlib environment and
the delivered sources; Python and Sympy are not additional build
dependencies.
