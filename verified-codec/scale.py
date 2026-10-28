#!/usr/bin/env python3
"""Measure certificate and exhaustive codecs without changing evaluator limits."""
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import platform
import re
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
sys.dont_write_bytecode = True


def measure(command, stem):
    start = time.perf_counter()
    with stem.with_suffix(".stdout").open("wb") as stdout, stem.with_suffix(".stderr").open("wb") as stderr:
        with subprocess.Popen(list(map(str, command)), cwd=ROOT, stdout=stdout, stderr=stderr) as child:
            _, status, usage = os.wait4(child.pid, 0)
            child.returncode = os.waitstatus_to_exitcode(status)
    return {"exit_code": child.returncode, "elapsed_seconds": time.perf_counter() - start,
            "peak_process_memory_kib": usage.ru_maxrss}


def resources(path):
    report = json.loads(path.read_text())
    stages = {}
    for e in report["evaluations"]:
        span = e["span"]
        source = (ROOT / span["file"]).read_bytes()[span["start"]["byte"]:span["end"]["byte"]]
        stage = ("certificate_production" if b"certificate(" in source else
                 "certificate_checking" if b"verify(" in source else
                 "exhaustive_checking" if b"model.exhaustive" in source else "other")
        counts = stages.setdefault(stage, {"evaluations": 0, "steps": 0, "max_steps": 0, "allocation_bytes": 0, "failed": 0})
        counts["evaluations"] += 1
        counts["steps"] += e["steps"]
        counts["max_steps"] = max(counts["max_steps"], e["steps"])
        counts["allocation_bytes"] += e["allocation_bytes"]
        counts["failed"] += not e["success"]
    return {"target": report["target"], "limits": report["limits"], "stages": stages}


def main():
    parser = argparse.ArgumentParser(__doc__)
    parser.add_argument("--compiler", type=Path, default=ROOT / "out/jihoo")
    parser.add_argument("--output", type=Path, default=ROOT / "out/codec-scaling")
    parser.add_argument("--sizes", nargs="+", type=int, default=[4, 16, 64, 256])
    args = parser.parse_args()
    if min(args.sizes) < 1:
        parser.error("sizes must be positive")
    compiler, out = args.compiler.resolve(strict=True), args.output.resolve()
    out.mkdir(parents=True, exist_ok=True)
    spec = importlib.util.spec_from_file_location("codec_cases", HERE / "check.py")
    cases = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(cases)
    report = {"compiler": str(compiler), "compiler_sha256": hashlib.sha256(compiler.read_bytes()).hexdigest(),
              "revision": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
              "source_tree_dirty": bool(subprocess.check_output(["git", "status", "--porcelain"], cwd=ROOT)),
              "host": platform.platform(), "measurements": []}
    sources = [*sorted((ROOT / "compiler").glob("*.jh")), ROOT / "lib/std/utf8.jh",
               *sorted((ROOT / "experimental/kernel").glob("*.jh")),
               *sorted(HERE.glob("*.jh")), HERE / "check.py", HERE / "scale.py"]
    report["source_sha256"] = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in sources}
    includes = ["-I", HERE, "-I", ROOT / "experimental/kernel", "-I", ROOT / "experimental/proofs"]
    passed = True
    for n in args.sizes:
        for exhaustive in (False, True):
            mode = "exhaustive" if exhaustive else "certificate"
            base = out / f"{mode}-{n}"
            source = base.with_suffix(".jh")
            source.write_text(cases.candidate(variants=", ".join(f"V{i}" for i in range(n)), exhaustive=exhaustive))
            item = {"variants": n, "mode": mode}
            for phase in ("check", "build"):
                profile = out / f"{mode}-{n}-{phase}.json"
                profile.unlink(missing_ok=True)
                command = [compiler, phase, source, *includes, "--comptime-report", profile]
                if phase == "build":
                    command.extend(["-o", base])
                result = measure(command, out / f"{mode}-{n}-{phase}")
                if result["exit_code"]:
                    diagnostic = (out / f"{mode}-{n}-{phase}.stderr").read_text(errors="replace")
                    result["failure_diagnostic"] = diagnostic.splitlines()[0] if diagnostic else "no diagnostic"
                    result["evaluator_limit_reached"] = result["exit_code"] == 1 and re.search(
                        r"compile-time evaluation exceeded its (?:step|memory|call depth) limit", diagnostic) is not None
                    if not result["evaluator_limit_reached"]:
                        passed = False
                if profile.is_file():
                    result["resources"] = resources(profile)
                item[phase] = result
                if result["exit_code"]:
                    break
            if item.get("build", {}).get("exit_code") == 0:
                item["runtime"] = measure([base], out / f"{mode}-{n}-run")
                assert item["runtime"]["exit_code"] == 0
                assert (out / f"{mode}-{n}-run.stdout").read_bytes() == b"ok\n"
            # Larger unary certificate failures are measurements, not silently
            # accepted constructions. The four-variant regression must pass.
            required = exhaustive or n <= 4
            if required and item.get("runtime", {}).get("exit_code") != 0:
                passed = False
            report["measurements"].append(item)
            (out / "report.json").write_text(json.dumps(report, indent=2) + "\n")
            print(f"{mode} {n}: check exit {item['check']['exit_code']}, "
                  f"{item['check']['elapsed_seconds']:.3f}s, "
                  f"{item['check']['peak_process_memory_kib']} KiB", flush=True)
    if not passed:
        raise SystemExit(f"Required scaling cases failed; see {out / 'report.json'}")


if __name__ == "__main__":
    main()
