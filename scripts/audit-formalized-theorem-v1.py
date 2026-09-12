"""Document QA for the standalone theorem PDF; not a mathematical proof checker.

Uses an already available pypdf. Run after build-formalized-theorem-v1.ps1.
All inputs and the JSON output must remain inside the selected workspace.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re

import pypdf


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    publication = Path(__file__).resolve().parent.parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--workspace-root", type=Path, default=publication)
    parser.add_argument("--build-dir", type=Path)
    parser.add_argument("--output", type=Path,
                        default=publication / "verification/pdf-statement-v1-qa.json")
    args = parser.parse_args()
    workspace = args.workspace_root.resolve(strict=True)
    build = (args.build_dir or workspace / "build/fourier-jacobi-core-statement-v1").resolve()
    output = args.output.resolve()
    pdf = publication / "formalized_theorem_v1.pdf"
    tex = publication / "formalized_theorem_v1.tex"
    audit = publication / "StatementAudit_v1.lean"
    for path in (publication, build, output, pdf, tex, audit):
        if not path.is_relative_to(workspace):
            raise ValueError(f"Path escapes workspace: {path}")

    source = tex.read_text(encoding="utf-8")
    if re.search(r"\\(?:input|include|includegraphics|bibliography|addbibresource|cite\w*|href|url)\b", source):
        raise ValueError("Unexpected external content or reference in standalone TeX")
    refs = set(re.findall(r"\\(?:eqref|ref)\{([^}]+)\}", source))
    labels = set(re.findall(r"\\label\{([^}]+)\}", source))
    if refs - labels:
        raise ValueError(f"Undefined TeX labels: {refs - labels}")
    aux = (build / "formalized_theorem_v1.aux").read_text(encoding="utf-8")
    if any("\\newlabel{" + ref + "}" not in aux for ref in refs):
        raise ValueError("A referenced label was not resolved in the compiled auxiliary file")

    reader = pypdf.PdfReader(pdf)
    if reader.is_encrypted or len(reader.pages) != 5:
        raise ValueError("Expected five unencrypted PDF pages")
    root = reader.trailer["/Root"]
    if "/AcroForm" in root or "/AA" in root:
        raise ValueError("Unexpected form or document action")
    if "/Names" in root and "/JavaScript" in root["/Names"]:
        raise ValueError("Unexpected JavaScript")
    page_text = []
    internal_links = 0
    for page in reader.pages:
        text = page.extract_text()
        if not text or "??" in text or "\ufffd" in text:
            raise ValueError("Empty page, unresolved reference, or replacement character")
        page_text.append(text)
        for ref in page.get("/Annots", []):
            annotation = ref.get_object()
            action = annotation.get("/A")
            if action is not None and action.get("/S") != "/GoTo":
                raise ValueError(f"External or active PDF annotation: {action}")
            internal_links += 1

    log = (build / "formalized_theorem_v1.log").read_text(encoding="utf-8", errors="replace")
    if re.search(r"Overfull|Underfull|undefined references|Reference .* undefined|Fatal error|^!", log, re.M):
        raise ValueError("Compiler errors, unresolved references, or box warnings")
    warnings = [line for line in log.splitlines() if "Warning:" in line]
    expected_warning = "Package epstopdf Warning: Shell escape feature is not enabled."
    if any(line != expected_warning for line in warnings):
        raise ValueError(f"Unexpected compiler warning: {warnings}")

    fls = (build / "formalized_theorem_v1.fls").read_text(encoding="utf-8")
    output_paths = []
    for line in fls.splitlines():
        if line.startswith("OUTPUT "):
            path = Path(line[7:].strip('"'))
            path = (path if path.is_absolute() else publication / path).resolve()
            if not path.is_relative_to(workspace):
                raise ValueError(f"Compiler output escapes workspace: {path}")
            output_paths.append(path.relative_to(workspace).as_posix())
    if not output_paths:
        raise ValueError("No compiler output paths recorded")
    if sha256(build / pdf.name) != sha256(pdf):
        raise ValueError("Delivered PDF differs from the final compiler output")

    renders = {f"page-{n}.png": sha256(build / f"page-{n}.png")
               for n in range(1, 6) if (build / f"page-{n}.png").is_file()}
    report = {
        "checked_at_utc": datetime.now(timezone.utc).isoformat(),
        "purpose": "Document QA only; implication proof is checked separately by Lean",
        "pypdf_version": pypdf.__version__,
        "page_count": len(reader.pages),
        "page_text_lengths": [len(text) for text in page_text],
        "self_contained_tex": True,
        "resolved_reference_labels": sorted(refs),
        "external_pdf_actions": 0,
        "internal_pdf_links": internal_links,
        "compiler_warnings": warnings,
        "compiler_outputs_inside_workspace": sorted(set(output_paths)),
        "delivered_pdf_matches_compiler_output": True,
        "sha256": {path.name: sha256(path) for path in (tex, pdf, audit)},
        "rendered_page_sha256": renders,
        "visual_review": "Rendering hashes identify pages; manual review is recorded in the audit report",
        "result": "passed",
    }
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(f"PDF document QA passed: {len(reader.pages)} pages; report {output}")


if __name__ == "__main__":
    main()
