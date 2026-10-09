"""Check the independent statement surface and pinned source layout."""
import json
import pathlib
import re

root = pathlib.Path(__file__).resolve().parents[1]
config = json.loads((root / "comparator.json").read_text())
challenge = root / (config["challenge_module"] + ".lean")
solution = root / (config["solution_module"] + ".lean")
assert challenge.is_file() and solution.is_file()
assert challenge != solution
assert challenge.stat().st_size <= 100 * 1024
assert len(challenge.read_text().splitlines()) <= 1000
assert len(config["theorem_names"]) == len(set(config["theorem_names"]))
assert set(config["permitted_axioms"]) == {"propext", "Classical.choice", "Quot.sound"}
files = list(root.glob("*.lean")) + list((root / "THGGradient").rglob("*.lean"))
for file in files:
    text = file.read_text()
    assert not file.is_symlink(), file
    assert text.startswith("module\n"), file
    assert len(text.splitlines()) <= 10000, file
    if file != challenge:
        assert not re.search(r"\b(sorry|admit|axiom|native_decide|unsafe)\b", text), file
imports = re.findall(r"^public import (\S+)", challenge.read_text(), re.M)
assert imports and all(x == "Mathlib" or x.startswith("Mathlib.") for x in imports)
for name in config["theorem_names"]:
    assert re.search(r"^theorem " + re.escape(name.split(".")[-1]) + r"\b", challenge.read_text(), re.M), name
manifest = json.loads((root / "lake-manifest.json").read_text())
for pkg in manifest["packages"]:
    assert re.fullmatch(r"[0-9a-f]{40}", pkg["rev"]), pkg["name"]
    assert re.fullmatch(r"https://github.com/[\w.-]+/[\w.-]+", pkg["url"]), pkg["name"]
assert manifest["name"] == "thgGradientCurve"
print(f"Source checks passed: {len(files)} Lean modules; {len(config['theorem_names'])} contracts.")
