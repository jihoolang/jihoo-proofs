#!/usr/bin/env python3
"""Run the model over a corpus of real programs: a jihoo checkout's
tests/run and examples. For each file, every function of its own module
must load and verify with the contracts its source states, and differential.py must find no
check that was proved and fails.

    corpus.py --compiler JIHOO --checkout ../jihoo [--count N] [--filter TEXT]
"""
import argparse
import json
import re
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
HERE = Path(__file__).resolve().parent


def run(*args, timeout=600):
    return subprocess.run(list(map(str, args)), cwd=ROOT, capture_output=True, text=True, timeout=timeout)


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--compiler", type=Path, required=True)
    ap.add_argument("--checkout", type=Path, required=True)
    ap.add_argument("--count", type=int, default=5)
    ap.add_argument("--filter", default="")
    ap.add_argument("--infer", action="store_true", help="infer invariants for loops without one")
    ap.add_argument("--report", type=Path, default=ROOT / "out/obligations/corpus.json")
    args = ap.parse_args()
    jihoo = args.compiler.resolve(strict=True)
    files = sorted((args.checkout / "tests/run").glob("*.jh")) + sorted((args.checkout / "examples").glob("*.jh"))
    files = [f for f in files if args.filter in str(f)]
    args.report.parent.mkdir(parents=True, exist_ok=True)

    with tempfile.TemporaryDirectory() as tmp:
        tmp = Path(tmp)
        verifier = tmp / "verifier"
        built = run(jihoo, "build", "-O2", "-I", HERE, "-I", ROOT / "kernel", HERE / "emitted.jh", "-o", verifier)
        if built.returncode:
            sys.exit(built.stderr)
        totals = {"files": 0, "skipped": 0, "functions": 0, "checks": 0, "proved": 0,
                  "probes": 0, "unproved check failed": 0, "unmodelled failure": 0, "bug": 0}
        skipped, load_errors, bugs, model_errors = [], [], [], {}
        # Why each unproved check is: the function was not followed
        # (`incomplete:...`), or where its claim's values come from.
        reasons = {}
        for f in files:
            name = str(f.relative_to(args.checkout))
            emitted = run(jihoo, "emit-obligations", f)
            if emitted.returncode:
                skipped.append(f"{name}: emit-obligations failed")
                totals["skipped"] += 1
                continue
            model = tmp / "model.obligations"
            model.write_text(emitted.stdout)
            own = re.findall(r"^\(function (\S+) main\.", emitted.stdout, re.M)
            infer = ["--infer"] if args.infer else []
            verified = run(verifier, "--machine", *infer, model, *own)
            if verified.returncode:
                load_errors.append(f"{name}: {(verified.stderr or verified.stdout).strip()[:300]}")
                continue
            totals["files"] += 1
            totals["functions"] += len(own)
            checks, why = {}, {}
            for line in verified.stdout.splitlines():
                parts = line.split()
                if parts[0] == "check":
                    key = (parts[1], parts[2], parts[3])
                    checks[key] = checks.get(key, True) and parts[4] == "proved"
                    if parts[4] != "proved" and len(parts) > 5:
                        why.setdefault(key, set()).update(parts[5].split(","))
            for key, ws in why.items():
                if not checks[key]:
                    label = "+".join(sorted(ws))
                    reasons[label] = reasons.get(label, 0) + 1
            totals["checks"] += len(checks)
            totals["proved"] += sum(checks.values())

            report = tmp / "differential.json"
            d = run(sys.executable, HERE / "differential.py", "--compiler", jihoo, f, "--count", args.count,
                    "--verifier", verifier, "--report", report, *infer)
            if d.returncode == 3:
                bugs.append(f"{name}:\n{d.stdout}")
            elif d.returncode:
                skipped.append(f"{name}: differential: {(d.stdout + d.stderr).strip().splitlines()[-1][:200]}")
                continue
            r = json.loads(report.read_text())
            totals["probes"] += r["probes"]
            for k in ["unproved check failed", "unmodelled failure", "bug"]:
                totals[k] += r["results"][k]
            for u in r["unmodelled"]:
                kind = re.sub(r" at bytes.*", "", u.split(": ", 1)[1])
                model_errors[kind] = model_errors.get(kind, 0) + 1
            print(f"{name}: {len(own)} functions, {sum(checks.values())}/{len(checks)} checks proved, "
                  f"{r['probes']} probes" + (" BUG" if d.returncode == 3 else ""), flush=True)

    summary = {"totals": totals, "load_errors": load_errors, "bugs": bugs, "skipped": skipped,
               "unmodelled_failures": model_errors,
               "unproved_because": dict(sorted(reasons.items(), key=lambda kv: -kv[1]))}
    args.report.write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(totals))
    print("unproved because: " + json.dumps(summary["unproved_because"]))
    for e in load_errors:
        print("LOAD " + e)
    for b in bugs:
        print("BUG " + b)
    sys.exit(3 if bugs else (1 if load_errors else 0))


if __name__ == "__main__":
    main()
