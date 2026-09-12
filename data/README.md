# Source-expression provenance

region-expressions.json records the fifty rational expressions from the
manuscript's three central-coordinate tables, with the common Weyl coefficient
removed and t substituted for q^(-1/2).

- Lean indices 0–9 are the ten rows of the central-zero table.
- Indices 10–24 are the fifteen rows for valuation -1.
- Indices 25–49 are the twenty-five rows for valuation -2.
- Each JSON record retains the manuscript's row label.

The transcription was obtained from the existing check_damping.py in the
paper's verification directory and checked against the proof audit. It uses
the denominator abbreviations P = 1 - d V t, N = 1 - V t / d,
E = 1 - V^2 t^2, F = 1 - U t^2, and G = 1 - U t^4.

The Weyl generator records the eight root lists from Proposition 2.10, in
manuscript order. Lean indices 0–7 correspond to manuscript indices 1–8.
Its substitutions U = L^2/(a b) and V = M use a b gamma^2 = 1.
The gamma substitution is separately proved in WeylEvaluation.lean.

The JSON is transcription data, not proof evidence. Lean checks the generated
finite identities independently. The new development also proves every actual
infinite row, the full norm-summable lattice assembly, and its identification
with the independently defined explicit-kernel Haar integrals.

`source-row-restorations.json` separately records all fifty printed expanded
source fractions, their restoration factors, and their exact stored fractions.
The raw-source symbolic comparison is supplementary evidence; the actual
infinite `HasSum` identities are proved in Lean. See `docs/source-map.md` and
`docs/appendices/core_row_normalizations_audit_v1.md` for the normalization
conversion and source-to-Lean declarations. The restored factors are applied
exactly once.
