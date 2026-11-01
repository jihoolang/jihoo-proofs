#!/usr/bin/env python3
"""Run the MIR obligation regressions: negative cases at runtime, the
compile-time example, which needs more evaluator steps than 0.4.2 allows,
and samples verified from `emit-obligations` when the compiler has it."""
import argparse
import json
import re
import shutil
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
HERE = Path(__file__).resolve().parent
EXPECTED = [
    "clamp: 6 of 6 obligations proved",
    "sum: 8 of 10 obligations proved",
]
# Each sample's verdicts from the compiler's own MIR; abs.jh must agree with
# the hand-written models.
SAMPLES = {
    "abs": EXPECTED,
    "bugs": [
        "last: 5 of 6 obligations proved",
        "  UNPROVED bb4: index-out-of-bounds: no linear proof",
        "after_call: 0 of 1 obligations proved",
        "scale: 3 of 3 obligations proved",
    ],
}
# Changes that make the model wrong; the differential test must notice.
MUTATIONS = [
    ("bugs", "(set 4 (cmp le (local 3) (local 13)))", "(set 4 (cmp lt (local 3) (local 13)))"),
    ("bugs", "(set 5 (use (opaque escaped)))", "(set 5 (use (local 1)))"),
]


def run(*args, timeout=300):
    return subprocess.run(list(map(str, args)), cwd=ROOT, capture_output=True, text=True, timeout=timeout)


def main():
    ap = argparse.ArgumentParser(__doc__)
    ap.add_argument("--compiler", type=Path, default=Path(shutil.which("jihoo") or "jihoo"))
    ap.add_argument("--corpus", type=Path, help="also run corpus.py over this jihoo checkout")
    args = ap.parse_args()
    out = ROOT / "out/obligations"
    out.mkdir(parents=True, exist_ok=True)
    jihoo = args.compiler.resolve(strict=True)

    tests = run(jihoo, "test", "-I", HERE, HERE / "tests.jh")
    if tests.returncode:
        raise SystemExit(tests.stdout + tests.stderr)
    passed = int(re.search(r"(\d+) passed", tests.stdout).group(1))

    # The example either fits the compiler's step limit and reports exactly
    # the expected verdicts, or fails at the limit, which is recorded.
    report_path = out / "comptime.json"
    example = run(jihoo, "run", "-I", HERE, "--comptime-report", report_path, HERE / "example.jh")
    if example.returncode == 0:
        lines = example.stdout.splitlines()
        for line in EXPECTED:
            if line not in lines:
                raise SystemExit(f"missing {line!r} in\n{example.stdout}")
        status = "checked at compile time"
    elif "exceeded its step limit" in example.stderr:
        status = "step limit"
    else:
        raise SystemExit(example.stdout + example.stderr)
    steps = []
    if report_path.exists():
        for e in json.loads(report_path.read_text())["evaluations"]:
            steps.append({"line": e["span"]["start"]["line"], "success": e["success"], "steps": e["steps"]})

    samples = {}
    probe = run(jihoo, "emit-obligations", HERE / "samples/abs.jh")
    if probe.returncode == 0:
        for name, expected in SAMPLES.items():
            emitted = out / f"{name}.obligations"
            emitted.write_text(run(jihoo, "emit-obligations", HERE / f"samples/{name}.jh").stdout)
            r = run(jihoo, "run", "-I", HERE, "-I", ROOT / "kernel", HERE / "emitted.jh", "--",
                    emitted, HERE / f"samples/{name}.contracts")
            if r.returncode:
                raise SystemExit(r.stdout + r.stderr)
            lines = r.stdout.splitlines()
            for line in expected:
                if line not in lines:
                    raise SystemExit(f"{name}: missing {line!r} in\n{r.stdout}")
            samples[name] = [l for l in lines if not l.startswith(" ")]
    elif "unknown command" not in probe.stderr:
        raise SystemExit(probe.stderr)

    # The generator against the interpreter: no proved check may fail.
    differential = {}
    if samples:
        for name in ["abs", "bugs", "ints", "arrays"]:
            for mode in [[], ["--release"]]:
                key = name + (" --release" if mode else "")
                result = out / f"differential-{name}{'-release' if mode else ''}.json"
                r = run(sys.executable, HERE / "differential.py", "--compiler", jihoo,
                        HERE / f"samples/{name}.jh", "--count", "20", "--report", result, *mode)
                if r.returncode:
                    raise SystemExit(f"differential {key}:\n{r.stdout}{r.stderr}")
                differential[key] = json.loads(result.read_text())["results"]
        for name, old, new in MUTATIONS:
            r = run(sys.executable, HERE / "differential.py", "--compiler", jihoo,
                    HERE / f"samples/{name}.jh", "--count", "20", "--mutate", old, new)
            if r.returncode != 3 or "BUG" not in r.stdout:
                raise SystemExit(f"a wrong model went unnoticed ({old} -> {new}):\n{r.stdout}{r.stderr}")
            differential[f"mutation {old} -> {new}"] = "noticed"

    corpus = None
    if args.corpus and samples:
        r = run(sys.executable, HERE / "corpus.py", "--compiler", jihoo, "--checkout", args.corpus,
                "--report", out / "corpus.json", "--infer", timeout=3600)
        if r.returncode:
            raise SystemExit(f"corpus:\n{r.stdout[-3000:]}{r.stderr[-3000:]}")
        corpus = json.loads((out / "corpus.json").read_text())["totals"]

    report = {"negative_tests_passed": passed, "example": status, "evaluations": steps, "corpus": corpus,
              "emitted_samples": samples or "the compiler has no emit-obligations",
              "differential": differential}
    (out / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(f"obligations: {passed} tests; example: {status}; {len(samples)} emitted samples; "
          f"{len(differential)} differential runs")


if __name__ == "__main__":
    main()
