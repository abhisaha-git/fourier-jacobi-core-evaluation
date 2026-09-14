"""Local package checks; this does not run Palomar, Comparator, or NanoDa."""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
from datetime import datetime, timezone
from pathlib import Path
from urllib.parse import unquote, urlsplit

import yaml

ROOT = Path(__file__).resolve().parents[1]
AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
NAMES = ["measure_normalizations", "integrability", "principal_evaluation", "special_abel_limit"]
PREFIX = "FourierJacobiPalomar."


class UniqueLoader(yaml.SafeLoader):
    """Reject duplicate mapping keys and YAML merge keys, as Palomar requires."""


def mapping(loader, node, deep=False):
    result = {}
    for key_node, value_node in node.value:
        if key_node.tag == "tag:yaml.org,2002:merge":
            raise ValueError("YAML merge key is forbidden")
        key = loader.construct_object(key_node, deep=deep)
        if key in result:
            raise ValueError(f"Duplicate YAML key: {key}")
        result[key] = loader.construct_object(value_node, deep=deep)
    return result


UniqueLoader.add_constructor(yaml.resolver.BaseResolver.DEFAULT_MAPPING_TAG, mapping)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def git(*args):
    return subprocess.check_output(
        ["git", "-c", f"safe.directory={ROOT.as_posix()}", "-C", str(ROOT), *args]
    ).decode("utf-8")


def lean_code(text, erase_strings=False):
    """Remove nested block/line comments; preserve strings for token comparison."""
    out, i = [], 0
    while i < len(text):
        if text.startswith("/-", i):
            depth = 1
            i += 2
            while depth:
                require(i < len(text), "Unterminated Lean comment")
                if text.startswith("/-", i):
                    depth += 1
                    i += 2
                elif text.startswith("-/", i):
                    depth -= 1
                    i += 2
                else:
                    out.append("\n" if text[i] == "\n" else " ")
                    i += 1
            out.append(" ")
        elif text.startswith("--", i):
            j = text.find("\n", i)
            i = len(text) if j < 0 else j
        elif text[i] == '"':
            j = i + 1
            while j < len(text):
                if text[j] == "\\":
                    j += 2
                elif text[j] == '"':
                    j += 1
                    break
                else:
                    j += 1
            out.append(" " if erase_strings else text[i:j])
            i = j
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def tokens(text):
    return re.findall(r'"(?:\\.|[^"\\])*"|[\w\u2080-\u209f]+|[^\s]', text)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--schema", type=Path, help="Local upstream v0.4 schema JSON")
    parser.add_argument("--require-clean", action="store_true")
    parser.add_argument("--output", type=Path, help="Write a JSON evidence report")
    args = parser.parse_args()

    names = sorted(set(git("ls-files", "--cached", "--others", "--exclude-standard", "-z").split("\0")) - {""})
    paths = [ROOT / name for name in names]
    for path in paths:
        require(path.is_file() and not path.is_symlink(), f"Missing or nonregular source: {path}")
        require(path.resolve().is_relative_to(ROOT), f"Source path escapes repository: {path}")
        require(path.suffix.lower() not in {".olean", ".ilean", ".a", ".bc", ".dll", ".dylib", ".o", ".obj", ".so", ".trace"}, f"Compiled artifact: {path}")
        with path.open("rb") as stream:
            require(not stream.read(100).startswith(b"version https://git-lfs.github.com/spec/v1"), f"Git LFS pointer: {path}")
    require(not (ROOT / ".gitmodules").exists(), "Submitted Git submodules are forbidden")
    require(not any(line.startswith("160000 ") for line in git("ls-files", "--stage").splitlines()), "Git submodule entry")
    size = sum(p.stat().st_size for p in paths)
    require(size <= 500 * 1024**2, "Source tree exceeds 500 MiB")
    require((ROOT / "lakefile.toml").is_file() and not (ROOT / "lakefile.lean").exists(), "Expected exactly the TOML Lakefile")
    import tomllib
    lake = tomllib.loads((ROOT / "lakefile.toml").read_text(encoding="utf-8"))
    require({"FourierJacobi", "Solution"} <= set(lake["defaultTargets"]), "Default build omits proof targets")
    require({"FourierJacobi", "StatementAudit_v1", "Solution", "Challenge"} <= {lib["name"] for lib in lake["lean_lib"]}, "Missing Lake library")
    require((ROOT / "lean-toolchain").read_text().strip() == "leanprover/lean4:v4.33.1", "Unexpected toolchain change")
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    for package in manifest["packages"]:
        require(package["type"] == "git", f"Non-Git dependency: {package['name']}")
        require(re.fullmatch(r"https://github\.com/[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+", package["url"]), f"Non-public-GitHub dependency URL: {package['name']}")
        require(re.fullmatch(r"[0-9a-f]{40}", package["rev"]), f"Unpinned dependency: {package['name']}")
    mathlib = next(p for p in manifest["packages"] if p["name"] == "mathlib")
    require(mathlib["rev"] == "0df444a360eaa60ab8c11dca51a86af692955474", "Unexpected mathlib change")
    require(lake["require"][0]["rev"] == mathlib["rev"], "Lakefile/manifest pin mismatch")

    config = json.loads((ROOT / "comparator.json").read_text())
    require(set(config) == {"challenge_module", "solution_module", "theorem_names", "permitted_axioms"}, "Unexpected Comparator keys")
    require(config["challenge_module"] == "Challenge" and config["solution_module"] == "Solution", "Unexpected module selection")
    require(config["theorem_names"] == [PREFIX + n for n in NAMES], "Unexpected theorem selection")
    require(set(config["permitted_axioms"]) == AXIOMS, "Unexpected Comparator axioms")
    challenge_text = (ROOT / "Challenge.lean").read_text(encoding="utf-8")
    solution_text = (ROOT / "Solution.lean").read_text(encoding="utf-8")
    challenge = lean_code(challenge_text)
    solution = lean_code(solution_text)
    lines = len(challenge_text.splitlines())
    byte_count = len(challenge_text.encode("utf-8"))
    require(lines <= 1000 and byte_count <= 100 * 1024, "Challenge exceeds hard size limits")
    imports = re.findall(r"^import\s+(\S+)\s*$", challenge, re.M)
    require(imports and all(i.startswith("Mathlib.") for i in imports), "Challenge imports project-specific source")
    require("Mathlib.Analysis.InnerProductSpace.Basic" in imports,
            "Challenge must use the same complex real normed-space instance as Solution")
    c_prefix = challenge[challenge.index("set_option autoImplicit"):challenge.index("theorem measure_normalizations")]
    s_prefix = solution[solution.index("set_option autoImplicit"):solution.index("open FourierJacobi.Valuations")]
    require(tokens(c_prefix) == tokens(s_prefix), "Challenge/Solution definition or context mismatch")
    for name in NAMES:
        pattern = rf"^theorem {name}\b([\s\S]*?) := by"
        c, s = re.search(pattern, challenge, re.M), re.search(pattern, solution, re.M)
        require(c and s and tokens(c[0]) == tokens(s[0]), f"Theorem type mismatch: {name}")
        require(re.search(rf"^theorem {name}\b[\s\S]*? := by\s+sorry\b", challenge, re.M), f"Missing expected statement hole: {name}")
    require(len(re.findall(r"\bsorry\b", lean_code(challenge_text, True))) == 4, "Unexpected number of Challenge holes")
    require(not re.search(r"\b(admit|axiom|unsafe|partial|native_decide)\b", lean_code(challenge_text, True)), "Unexpected Challenge escape hatch")
    lean_paths = [p for p in paths if p.suffix == ".lean" and p.name != "Challenge.lean"]
    for path in lean_paths:
        code = lean_code(path.read_text(encoding="utf-8"), True)
        require(not re.search(r"\b(sorry|admit|axiom|native_decide|unsafe|partial)\b", code), f"Proof placeholder/escape hatch: {path}")
        require(not re.search(r"^\s*(?:public\s+)?import\s+Challenge\b", code, re.M), f"Proof imports Challenge: {path}")

    metadata_path = ROOT / "formalization.yaml"
    require(metadata_path.stat().st_size <= 256 * 1024, "Metadata exceeds 256 KiB")
    metadata = yaml.load(metadata_path.read_text(encoding="utf-8"), Loader=UniqueLoader)
    require(isinstance(metadata, dict) and metadata.get("version") == "v0.4", "Expected v0.4 YAML mapping")
    project = metadata["project"]
    for key, limit in [("name", 300), ("description", 10000)]:
        require(isinstance(project[key], str) and 0 < len(project[key]) <= limit, f"Invalid project.{key}")
    for key in ["authors", "responsible_maintainers"]:
        require(isinstance(project[key], list) and project[key] and all(isinstance(n, str) and n.strip() for n in project[key]), f"Invalid {key}")
    licenses = [p for p in paths if p.parent == ROOT and re.fullmatch(r"(?:LICENSE|LICENCE|COPYING|UNLICENSE|OFL)(?:\.(?:md|markdown|txt))?", p.name, re.I)]
    require(len(licenses) == 1 and licenses[0].stat().st_size <= 1024**2, "Expected one root license")
    license_text = licenses[0].read_text(encoding="utf-8")
    require(project["license"] == "Apache-2.0" and "Apache License" in license_text and "Version 2.0, January 2004" in license_text, "Apache license/metadata mismatch")
    require(metadata["classification"]["arxiv"] == ["math.NT", "math.RT"], "Review changed arXiv classification")
    require(metadata["classification"]["msc2020"] == ["11F70", "11F85"], "Review changed MSC classification")
    sources = metadata["sources"]
    require(sources and all(s.get("title") and s.get("relationship") in {"formalizes", "adapts", "independently-proves", "background", "other"} for s in sources), "Invalid source attribution")
    require(any(s["relationship"] in {"formalizes", "adapts", "independently-proves"} for s in sources) and all(s.get("type") != "original-proof" for s in sources), "Expected source-based provenance")
    require(metadata["automation"]["methods"] and all(m.get("method") for m in metadata["automation"]["methods"]), "Missing automation disclosure")
    require(metadata["review"]["status"] and metadata["fidelity"]["divergences"], "Missing review/limitations")
    require([r["declaration"] for r in metadata["status"]["main_results"]] == config["theorem_names"], "Metadata theorem selection mismatch")
    schema_hash = None
    if args.schema:
        import jsonschema
        schema_data = args.schema.read_bytes()
        schema = json.loads(schema_data)
        jsonschema.Draft7Validator.check_schema(schema)
        jsonschema.Draft7Validator(schema).validate(metadata)
        schema_hash = hashlib.sha256(schema_data).hexdigest()

    for path in (p for p in paths if p.suffix == ".md"):
        prose = re.sub(r"```[\s\S]*?```", "", path.read_text(encoding="utf-8"))
        prose = re.sub(r"\\\([\s\S]*?\\\)|\\\[[\s\S]*?\\\]|`[^`]*`", "", prose)
        for target in re.findall(r"\[[^\]\n]*\]\(([^)]+)\)", prose):
            target = target.strip().strip("<>").split(' "', 1)[0]
            parts = urlsplit(target)
            if parts.scheme or not parts.path:
                continue
            resolved = (path.parent / unquote(parts.path)).resolve()
            require(resolved.is_relative_to(ROOT) and resolved.exists(), f"Broken local link in {path.relative_to(ROOT)}: {target}")
    dirty = git("status", "--porcelain")
    if args.require_clean:
        require(not dirty, "Commit the complete reviewed package before selecting a submission SHA")
    files, normalized_text_files = {}, []
    for path in paths:
        relative = path.relative_to(ROOT).as_posix()
        if relative.startswith("verification/"):
            continue
        data = path.read_bytes()
        try:
            data.decode("utf-8")
        except UnicodeDecodeError:
            pass
        else:
            data = data.replace(b"\r\n", b"\n")
            normalized_text_files.append(relative)
        files[relative] = hashlib.sha256(data).hexdigest()
    report = {"checked_at": datetime.now(timezone.utc).isoformat(), "scope": "Local preparation checks; not official Palomar verification",
              "git_head": git("rev-parse", "HEAD").strip(), "working_tree_clean": not bool(dirty),
              "source_bytes": size, "challenge_lines": lines, "challenge_bytes": byte_count,
              "challenge_imports": imports, "theorems": config["theorem_names"], "proof_source_files": len(lean_paths),
              "statement_holes": 4, "proof_holes": 0, "upstream_schema_sha256": schema_hash,
              "definition_and_theorem_text_match": True,
              "hash_algorithm": "SHA256; CRLF normalized to LF for listed UTF-8 text files",
              "normalized_text_files": normalized_text_files, "files": files}
    if args.output:
        output = args.output.resolve()
        require(output.is_relative_to(ROOT), "Evidence output must stay inside publication")
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print(f"PASS: {len(paths)} files; {lines}-line/{byte_count}-byte Challenge; four identical theorem types; no proof holes.")
    print(f"PASS: metadata, pins, license consistency, source hygiene and local links; schema checked: {bool(schema_hash)}.")
    print(f"Working tree clean: {not bool(dirty)}. Official Comparator/NanoDa and hosted review are separate.")


if __name__ == "__main__":
    main()
