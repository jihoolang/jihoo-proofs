#!/usr/bin/env python3
"""Test the obligation generator against the compiler's interpreter.

For each function of a sample with integer and `[i64]` parameters, random
inputs that meet its `requires` are evaluated at compile time (a `const`
per input, `jihoo check`). The interpreter reports a failing check with its
span; `emit-obligations` gives each check's span and each function's
contract. A check the generator proved must never fail, and an `ensures` it
proved must hold: either is a soundness bug in the model, and the exit
status is 3 (other failures exit with 1). Proofs are modular, so a failure
in a function whose proof assumed a contract that is not proved (a callee's
`ensures`, or its own `requires` at a call) is not a bug.

    differential.py --compiler JIHOO samples/bugs.jh [--count N] [--seed S]
        [--mutate OLD NEW] [--verdicts compiler]

`--verdicts compiler` takes the verdicts from the compiler's own verifier
(`jihoo verify --machine`) instead of this experiment's, so the same test
checks the checker that removes proved checks from programs. Its verdicts
already count a proof resting on an unproved contract as unproved.

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
    for m in re.finditer(r"^fn (\w+)\(([^)]*)\)(?:\s*->\s*([\w\[\]]+))?\s*(?:\{|requires|ensures)", source, re.M):
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


def section(f, name):
    return [x for x in f if isinstance(x, list) and x and x[0] == name]


def pairs(f, name):
    rows = section(f, name)
    return [(int(a), int(b)) for a, b in rows[0][1:]] if rows else []


def clauses(f, name):
    """A function's `requires` or `ensures`: (op, a, b), each side a
    (constant, [(variable, coefficient)]) or None when it is opaque."""
    out = []
    for c in section(f, name):
        op, a, b = c[1][0], c[1][1], c[1][2]
        def side(x):
            if x[0] != "lin":
                return None
            return int(x[1]), [(int(v), int(k)) for v, k in x[2:]]
        out.append((op, side(a), side(b)))
    return out


OPS = {"lt": "<", "le": "<=", "gt": ">", "ge": ">=", "eq": "==", "ne": "!="}


def evaluate(fact, env):
    op, a, b = fact
    if a is None or b is None:
        return True
    def value(x):
        return x[0] + sum(k * env[v] for v, k in x[1])
    x, y = value(a), value(b)
    return {"lt": x < y, "le": x <= y, "gt": x > y, "ge": x >= y, "eq": x == y, "ne": x != y}[op]


def condition(facts, env_text):
    def value(x):
        return " + ".join([f"({x[0]} as i128)"] + [f"({k} as i128) * ({env_text[v]} as i128)" for v, k in x[1]])
    return " && ".join(f"{value(a)} {OPS[op]} {value(b)}" for op, a, b in facts
                       if a is not None and b is not None) or "true"


def tainted(layout, ensures, requires):
    """The functions whose proofs assumed a contract that is not proved."""
    by_symbol = {f[2]: n for n, f in layout.items()}
    calls = {n: set() for n in layout}
    for n, f in layout.items():
        for block in section(f, "block"):
            for c in [t for t in block if isinstance(t, list) and t and t[0] == "call"]:
                for part in c[3:]:
                    if part[0] == "fn" and part[1] in by_symbol:
                        calls[n].add(by_symbol[part[1]])
    # A caller assumes its callees' `ensures`; a callee assumes its
    # `requires`, which its callers prove.
    has = {n: (bool(section(f, "requires")), bool(section(f, "ensures"))) for n, f in layout.items()}
    bad = set()
    for (_, callee), proved in requires.items():
        if not proved and callee in by_symbol:
            bad.add(by_symbol[callee])
    changed = True
    while changed:
        changed = False
        for n, callees in calls.items():
            for g in callees:
                if n not in bad and has[g][1] and (g in bad or ensures.get(g) is False):
                    bad.add(n)
                    changed = True
                if g not in bad and has[g][0] and n in bad:
                    bad.add(g)
                    changed = True
    return bad


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
    ap.add_argument("--verdicts", choices=["experiment", "compiler"], default="experiment",
                    help="whose verdicts to test: emitted.jh's, or `jihoo verify --machine`")
    args = ap.parse_args()
    jihoo = args.compiler.resolve(strict=True)
    sample = args.sample.resolve(strict=True)
    source = sample.read_text()
    rng = random.Random(args.seed)

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
        # The constants of the program's contracts, where inputs often go wrong.
        near = sorted({side[0] + d for f in layout.values() if f[2].startswith("main.")
                       for _, x, y in clauses(f, "requires") + clauses(f, "ensures")
                       for side in (x, y) if side for d in (-1, 0, 1)})
        sigs = signatures(source)
        names = [n for n in sigs] + [n for n in re.findall(r"^fn (\w+)", source, re.M)
                                     if n not in sigs and n != "main"]
        names = [n for n in names if n in layout]
        verifier = [args.verifier.resolve()] if args.verifier else \
            [jihoo, "run", "-I", HERE, "-I", ROOT / "kernel", HERE / "emitted.jh", "--"]
        if args.verdicts == "compiler":
            if args.mutate:
                sys.exit("--mutate changes the experiment's model, not the compiler's")
            verified = run(jihoo, "verify", "--machine", *mode, sample)
        else:
            verified = run(*verifier, "--machine", *(["--infer"] if args.infer else []),
                           tmp / "model.obligations", *names)
        # `jihoo verify` exits with 1 after printing its verdicts when a
        # contract is not proved, which the samples have on purpose.
        failed = verified.returncode != 0
        if args.verdicts == "compiler" and verified.returncode == 1 and not verified.stderr:
            failed = False
        if failed:
            sys.exit(verified.stdout + verified.stderr)

        # A check is proved when every obligation with its span is.
        checks, ensures, requires = {}, {}, {}
        for line in verified.stdout.splitlines():
            parts = line.split()
            if not parts:
                continue
            if parts[0] == "check":
                key = (int(parts[2]), int(parts[3]))
                checks.setdefault(key, (parts[1], True))
                checks[key] = (parts[1], checks[key][1] and parts[4] == "proved")
            elif parts[0] == "requires":
                key = (parts[1] + " " + parts[2] + " " + parts[3], parts[4])
                requires[key] = requires.get(key, True) and parts[5] == "proved"
            elif parts[0] == "ensures":
                ensures[parts[1]] = parts[2] == "proved"
        # The compiler's verdicts are not modular: nothing proved rests on
        # an unproved contract.
        assumed = set() if args.verdicts == "compiler" else tainted(layout, ensures, requires)

        # Inputs that meet each function's `requires`, as compile-time probes.
        probes = []
        for name, (kinds, ret) in sigs.items():
            f = layout[name]
            lengths = dict(pairs(f, "lengths"))
            entries = pairs(f, "entries")
            pre = clauses(f, "requires")
            post = clauses(f, "ensures")
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
                for v, e in entries:
                    env[e], text[e] = env[v], text[v]
                if not all(evaluate(x, env) for x in pre):
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
                   "failed under an unproved contract": 0, "unmodelled failure": 0, "bug": 0}
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
            here = d["span"]["file"] == str(path)
            where = f"{name}{tuple(vals)}: {d['message']} at bytes {lo}..{hi}"
            # A panic in a callee fails with the callee's message: the calls
            # that led there, innermost first, are the call to the function
            # that never returns (its check) and the call to the function
            # that reached it (a check when the caller proved its panics
            # away).
            chain = [(n["span"]["start"]["byte"], n["span"]["end"]["byte"]) for n in d["notes"]
                     if n["message"].startswith("in compile-time call to") and n["span"]
                     and n["span"]["file"] == str(path) and n["span"]["start"]["byte"] < prefix][:2]
            if here and lo >= prefix:
                if ensures.get(name) and name in assumed:
                    results["failed under an unproved contract"] += 1
                elif ensures.get(name):
                    results["bug"] += 1
                    bugs.append(where + " (ensures was proved)")
                else:
                    results["ensures failed"] += 1
            else:
                spans = [(lo, hi)] if here and (lo, hi) in checks else chain
                known = [x for x in spans if x in checks]
                proved = [x for x in known if checks[x][1]]
                if proved and checks[proved[0]][0] in assumed:
                    results["failed under an unproved contract"] += 1
                elif proved:
                    results["bug"] += 1
                    bugs.append(where + f" (proved in {checks[proved[0]][0]} at bytes "
                                f"{proved[0][0]}..{proved[0][1]})")
                elif known:
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
