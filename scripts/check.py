#!/usr/bin/env python3
"""Run the kernel, proof and codec regressions, without Horn by default."""
import argparse
import hashlib
import json
from pathlib import Path
import platform
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
HORN_REVISION = "18caf6d39088e1569beff678bc4461a28b8d2827"


def main():
    parser = argparse.ArgumentParser(__doc__)
    parser.add_argument("--compiler", type=Path, default=Path(shutil.which("jihoo") or "jihoo"))
    parser.add_argument("--horn", type=Path, help="also compare against this pinned Horn checkout (requires Rust)")
    parser.add_argument("--horn-revision", default=HORN_REVISION)
    args = parser.parse_args()
    compiler = args.compiler.resolve(strict=True)
    out = ROOT / "out"
    out.mkdir(parents=True, exist_ok=True)
    report = {"status": "running", "host": platform.platform(),
              "compiler": str(compiler),
              "compiler_sha256": hashlib.sha256(compiler.read_bytes()).hexdigest(),
              "revision": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
              "source_tree_dirty": bool(subprocess.check_output(["git", "status", "--porcelain"], cwd=ROOT)),
              "mode": "differential" if args.horn else "local", "suites": {}}

    def save():
        (out / "report.json").write_text(json.dumps(report, indent=2) + "\n")

    save()
    try:
        reference = (["--horn", args.horn.resolve(), "--horn-revision", args.horn_revision]
                     if args.horn else ["--local"])
        suites = [
            ("kernel", "kernel/check.py", reference, out / "kernel/report.json"),
            ("proofs", "proofs/check.py", reference, out / "proofs/report.json"),
            ("codec", "verified-codec/check.py", [], out / "verified-codec/report.json"),
        ]
        for name, script, options, result in suites:
            print(f"Checking {name}", flush=True)
            command = [sys.executable, ROOT / script, "--compiler", compiler, *options]
            subprocess.run(list(map(str, command)), cwd=ROOT, check=True)
            report["suites"][name] = json.loads(result.read_text())
            save()
        report["status"] = "passed"
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        report["status"] = "failed"
        report["error"] = str(error)
        raise
    finally:
        save()
    print(f"Regressions passed; report: {out / 'report.json'}", flush=True)


if __name__ == "__main__":
    main()
