#!/usr/bin/env python3
"""Test the obligation generator against the compiler's interpreter.

For each function of a sample with integer and `[i64]` parameters, random
inputs that meet its `requires` are evaluated at compile time (a `const`
per input, `jihoo check`). The interpreter reports a failing check with its
span; `emit-obligations` gives each check's span. A check the generator
proved must never fail, and an `ensures` it proved must hold: either is a
soundness bug in the model, and the exit status is 3 (other failures
exit with 1).

    differential.py --compiler JIHOO samples/bugs.jh [--count N] [--seed S]
        [--mutate OLD NEW]

`--mutate` replaces text in the emitted model before verifying it, so a
test can make the model wrong on purpose and expect a bug to be found.
"""
import argparse
import json
import random
import re
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
HERE = Path(__file__).resolve().parent

INTS = {f"{s}{b}": (s == "i", b) for s in "iu" for b in (8, 16, 32, 64)}
INTS["int"] = (True, 64)


def run(*args, timeout=300):
    return subprocess.run(list(map(str, args)), cwd=ROOT, capture_output=True, text=True, timeout=timeout)


def sexps(text):
    text = re.sub(r";[^\n]*", "", text)
    tokens = text.replace("(", " ( ").replace(")", " ) ").split()
    stack = [[]]
    for t in tokens:
        if t == "(":
            stack.append([])
        elif t == ")":
            done = stack.pop()
            stack[-1].append(done)
        else:
            stack[-1].append(t)
    assert len(stack) == 1, "unbalanced parentheses"
    return stack[0]


def int_range(name):
    signed, bits = INTS[name]
    return (-(1 << (bits - 1)), (1 << (bits - 1)) - 1) if signed else (0, (1 << bits) - 1)


def signatures(source):
    """The sample's functions whose parameters the harness can generate."""
    out = {}
    for m in re.finditer(r"^fn (\w+)\(([^)]*)\)(?:\s*->\s*([\w\[\]]+))?\s*\{", source, re.M):
        name, params, ret = m.group(1), m.group(2).strip(), m.group(3)
        if name == "main":
            continue
        kinds = []
        for p in [p.strip() for p in params.split(",")] if params else []:
            pm = re.fullmatch(r"(\w+)\s*:\s*(\[i64\]|\w+)", p)
            if not pm or (pm.group(2) not in INTS and pm.group(2) != "[i64]"):
                kinds = None
                break
            kinds.append(pm.group(2))
        if kinds is not None:
            out[name] = (kinds, ret)
    return out


def value(rng, kind, near):
    """A random value, often at a boundary of its type or of a contract's
    constants (`near`)."""
    if kind == "[i64]":
        return [value(rng, "i64", near) for _ in range(rng.choice([0, 0, 1, 2, 3, 5]))]
    lo, hi = int_range(kind)
    pick = rng.random()
    if pick < 0.2 and near:
        return max(lo, min(hi, rng.choice(near)))
    if pick < 0.5:
        return rng.choice([lo, lo + 1, hi - 1, hi, 0, 1, max(lo, -1), 2])
    if pick < 0.8:
        return max(lo, min(hi, rng.randint(-10, 10)))
    return rng.randint(lo, hi)


def literal(v):
    if isinstance(v, list):
        return "[" + ", ".join(literal(x) for x in v) + "]"
    if v == -(1 << 63):
        return f"({v + 1} - 1)"
    return f"({v})" if v < 0 else str(v)


def evaluate(fact, env):
    op, a, b = fact
    def operand(o):
        if o[0] == "const":
            return int(o[1])
        return env[int(o[1])]
    x, y = operand(a), operand(b)
    return {"lt": x < y, "le": x <= y, "gt": x > y, "ge": x >= y, "eq": x == y, "ne": x != y}[op]


def condition(facts, env_text):
    def operand(o):
        return f"({o[1]} as i128)" if o[0] == "const" else f"({env_text[int(o[1])]} as i128)"
    ops = {"lt": "<", "le": "<=", "gt": ">", "ge": ">=", "eq": "==", "ne": "!="}
    return " && ".join(f"{operand(a)} {ops[op]} {operand(b)}" for op, a, b in facts) or "true"


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--compiler", type=Path, required=True)
    ap.add_argument("sample", type=Path)
    ap.add_argument("--count", type=int, default=30)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--mutate", nargs=2, action="append", default=[])
    ap.add_argument("--report", type=Path)
    ap.add_argument("--release", action="store_true", help="overflow wraps, in the model and the interpreter")
    ap.add_argument("--infer", action="store_true", help="infer invariants for loops without one")
    ap.add_argument("--verifier", type=Path, help="emitted.jh, already built (else it is compiled and run)")
    args = ap.parse_args()
    jihoo = args.compiler.resolve(strict=True)
    sample = args.sample.resolve(strict=True)
    source = sample.read_text()
    contracts_path = sample.with_suffix(".contracts")
    contracts = {}
    if contracts_path.exists():
        for c in sexps(contracts_path.read_text()):
            parts = {p[0]: p[1:] for p in c[2:] if p[0] in ("requires", "ensures")}
            contracts[c[1]] = parts
    rng = random.Random(args.seed)
    near = sorted({int(c) + d for c in re.findall(r"\(const (-?\d+)\)", contracts_path.read_text())
                   for d in (-1, 0, 1)} if contracts_path.exists() else set())

    with tempfile.TemporaryDirectory() as tmp:
        tmp = Path(tmp)
        mode = ["--release"] if args.release else []
        emitted = run(jihoo, "emit-obligations", *mode, sample)
        if emitted.returncode:
            sys.exit(emitted.stderr)
        model = emitted.stdout
        for old, new in args.mutate:
            if old not in model:
                sys.exit(f"--mutate: {old!r} is not in the model")
            model = model.replace(old, new)
        (tmp / "model.obligations").write_text(model)
        layout = {f[1]: f for f in sexps(model)}
        sigs = signatures(source)
        names = [n for n in sigs] + [n for n in re.findall(r"^fn (\w+)", source, re.M)
                                     if n not in sigs and n != "main"]
        names = [n for n in names if n in layout]
        verifier = [args.verifier.resolve()] if args.verifier else \
            [jihoo, "run", "-I", HERE, "-I", ROOT / "kernel", HERE / "emitted.jh", "--"]
        verified = run(*verifier, "--machine", *(["--infer"] if args.infer else []), tmp / "model.obligations",
                       contracts_path if contracts_path.exists() else HERE / "samples/none.contracts",
                       *names)
        if verified.returncode:
            sys.exit(verified.stdout + verified.stderr)

        # A check is proved when every obligation with its span is.
        checks, ensures = {}, {}
        for line in verified.stdout.splitlines():
            parts = line.split()
            if parts[0] == "check":
                key = (int(parts[2]), int(parts[3]))
                checks.setdefault(key, (parts[1], True))
                checks[key] = (parts[1], checks[key][1] and parts[4] == "proved")
            elif parts[0] == "ensures":
                ensures[parts[1]] = parts[2] == "proved"

        # Inputs that meet each function's `requires`, as compile-time probes.
        probes = []
        for name, (kinds, ret) in sigs.items():
            f = layout[name]
            lengths = {int(a): int(b) for a, b in f[5][1:]}
            requires = contracts.get(name, {}).get("requires", [])
            post = contracts.get(name, {}).get("ensures", [])
            made, tries = 0, 0
            while made < args.count and tries < args.count * 200:
                tries += 1
                vals = [value(rng, k, near) for k in kinds]
                env, text = {}, {0: "r"}
                for i, v in enumerate(vals):
                    if isinstance(v, list):
                        env[lengths[i + 1]] = len(v)
                        text[lengths[i + 1]] = str(len(v))
                    else:
                        env[i + 1] = v
                        text[i + 1] = literal(v)
                if not all(evaluate(x, env) for x in requires):
                    continue
                made += 1
                probes.append((name, vals, post, text))

        def program(live):
            out = [source, "\n// Probes made by differential.py.\n"]
            starts = {}
            for k in live:
                name, vals, post, text = probes[k]
                call = f"{name}({', '.join(literal(v) for v in vals)})"
                body = f"    let r = {call}\n" if sigs[name][1] else f"    {call}\n"
                if post:
                    # `panic` cannot print at compile time; a trap in the
                    # probe is the failed `ensures`.
                    body += f"    if !({condition(post, text)}) {{ trap() }}\n"
                out.append(f"fn probe_{k}() -> i64 {{\n{body}    0\n}}\n")
                line = f"const PROBE_{k}: i64 = probe_{k}()\n"
                starts[k] = sum(len(s.encode()) for s in out) + len("const PROBE_{k}: i64 = ".format(k=k))
                out.append(line)
            # A `const` is evaluated only when something refers to it.
            out.append("fn probes() -> i64 {\n    0" + "".join(f" + PROBE_{k}" for k in live) + "\n}\n")
            return "".join(out), starts

        live = list(range(len(probes)))
        results = {"passed": 0, "unproved check failed": 0, "ensures failed": 0,
                   "unmodelled failure": 0, "bug": 0}
        bugs, unmodelled = [], []
        prefix = len(source.encode())
        while live:
            text, starts = program(live)
            path = tmp / "probes.jh"
            path.write_text(text)
            r = run(jihoo, "check", *mode, "--error-format=json", path)
            if r.returncode == 0:
                break
            diags = json.loads(r.stdout or r.stderr)["diagnostics"]
            d = diags[0]
            if d.get("kind") != "source" or not d.get("span"):
                sys.exit(f"the probes do not compile:\n{r.stdout}{r.stderr}")
            const = [n["span"]["start"]["byte"] for n in d["notes"]
                     if n["message"] == "while evaluating this compile-time obligation" and n["span"]]
            hit = [k for k, s in starts.items() if const and s == const[0]]
            if not hit:
                sys.exit(f"cannot tell which probe failed:\n{json.dumps(d, indent=1)}")
            k = hit[0]
            live.remove(k)
            name, vals = probes[k][0], probes[k][1]
            lo, hi = d["span"]["start"]["byte"], d["span"]["end"]["byte"]
            where = f"{name}{tuple(vals)}: {d['message']} at bytes {lo}..{hi}"
            if lo >= prefix:
                if ensures.get(name):
                    results["bug"] += 1
                    bugs.append(where + " (ensures was proved)")
                else:
                    results["ensures failed"] += 1
            elif (lo, hi) in checks and lo < prefix:
                owner, proved = checks[(lo, hi)]
                if proved:
                    results["bug"] += 1
                    bugs.append(where + f" (proved in {owner})")
                else:
                    results["unproved check failed"] += 1
            else:
                results["unmodelled failure"] += 1
                unmodelled.append(where)
        results["passed"] = len(live)

    report = {"sample": str(args.sample), "seed": args.seed, "release": args.release, "infer": args.infer,
              "probes": len(probes),
              "functions": list(sigs), "results": results, "bugs": bugs, "unmodelled": unmodelled}
    if args.report:
        args.report.write_text(json.dumps(report, indent=2) + "\n")
    print(f"{args.sample.name}: {len(probes)} probes, " +
          ", ".join(f"{v} {k}" for k, v in results.items() if v))
    for b in bugs:
        print("  BUG " + b)
    for u in unmodelled[:5]:
        print("  unmodelled " + u)
    sys.exit(3 if bugs else 0)


if __name__ == "__main__":
    main()
