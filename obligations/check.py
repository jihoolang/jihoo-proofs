#!/usr/bin/env python3
"""Run the MIR obligation regressions: negative cases at runtime, the
compile-time example, which needs more evaluator steps than 0.4.2 allows,
and samples verified from `emit-obligations` when the compiler has it."""
import argparse
import json
import re
import shutil
import subprocess
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


def run(*args):
    return subprocess.run(list(map(str, args)), cwd=ROOT, capture_output=True, text=True, timeout=300)


def main():
    ap = argparse.ArgumentParser(__doc__)
    ap.add_argument("--compiler", type=Path, default=Path(shutil.which("jihoo") or "jihoo"))
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

    report = {"negative_tests_passed": passed, "example": status, "evaluations": steps,
              "emitted_samples": samples or "the compiler has no emit-obligations"}
    (out / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(f"obligations: {passed} tests; example: {status}; {len(samples)} emitted samples")


if __name__ == "__main__":
    main()
