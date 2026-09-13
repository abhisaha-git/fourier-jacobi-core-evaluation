# Mathematical and formalization provenance

Abhishek Saha is the formalization author and responsible maintainer. He
confirmed this attribution during Palomar preparation on 13 September 2026.
The mathematical paper is by Biplab Paul, Ameya Pitale, Abhishek Saha and Ralf
Schmidt: [An explicit refined Gan–Gross–Prasad identity for Fourier–Jacobi
periods of degree 2 Siegel cusp forms](https://arxiv.org/abs/2608.26007).
Attribution as a paper author does not imply authorship or endorsement of every
part of this formalization.

The source calculation is in Section 2. The author-supplied expanded Section 2
and corrected core-evaluation brief were used for the fifty-region
transcription and the precise explicit-kernel target. The original expanded
TeX and PDF are retained in the author's workspace, outside this publication;
their hashes are preserved in
[source-preservation.json](verification/source-preservation.json). Absolute
paths in that historical record identify the original files and are not build
dependencies. [source-map.md](docs/source-map.md) identifies every row, source
label, restoration factor and infinite-series proof. The raw restoration
record is [source-row-restorations.json](data/source-row-restorations.json).

The standalone [theorem PDF](formalized_theorem_v1.pdf), its
[TeX source](formalized_theorem_v1.tex), and the
[checked PDF transcription](StatementAudit_v1.lean) describe the actual result
without requiring the author's expanded source document. The theorem concerns
the independently specified explicit kernel. Its identification with the
paper's spherical coefficient, and the full period theorem, remain outside
the proved scope. No priority or novelty claim is made.

The preceding `fourier-jacobi-theorem-2-2-v2` development supplied thirty
modules, including the finite fifty-region/eight-Weyl identity, four infinite
I0 rows, and local-field valuation, measure, collision and matrix lemmas. The
core-evaluation development adds thirty-nine modules completing the remaining
forty-six rows, infinite summation, integrability, Haar assembly and limits.
The [preservation recheck](verification/preservation-recheck.json) records
the earlier snapshots; [Audit.lean](Audit.lean) lists inherited and added
modules explicitly. All substantive sources are included here. The build
needs only the pinned public dependencies in `lake-manifest.json`.

Codex agents assisted with Lean proofs, mathematical exposition, source
transcription, symbolic checks, reviews and packaging under the author's
direction. The retained reports do not establish a complete historical model
or prompt log, so none is reconstructed. The Palomar preparation used GPT-6
through Codex, with Lean checking and local metadata validation. AI systems are
credited in `formalization.yaml` as tools; human authors retain responsibility.

The review record consists of agent review reports in
[docs/appendices](docs/appendices/README.md), Lean verification, the PDF
implication audit, and the Palomar preparation checks. This does not establish
independent human peer review, approval by all paper authors, or acceptance by
Palomar. The selected repository license is [Apache-2.0](LICENSE); this
preparation preserves that existing choice.
