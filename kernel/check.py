#!/usr/bin/env python3
"""Compare the jihoo port with the original Rust kernel, including reports."""
import argparse
import json
import random
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]


def run(*args):
    return subprocess.run(args, cwd=ROOT, capture_output=True, timeout=60)


def build(*args):
    p = run(*args)
    if p.returncode:
        raise RuntimeError(p.stderr.decode(errors="replace"))


def cases(horn):
    t = (horn / "examples/nat.horn").read_text()
    g = (horn / "examples/nat.goals").read_text()
    p = (horn / "examples/nat.proof").read_text()
    yield "upstream nat", t, g, p, True
    compact = "(step 0 zero ()) (step 1 plus-two (0)) (step 2 plus-two (1)) (result four-is-even 2)"
    yield "inferred conclusions", t, g, compact, True
    for name, proof in [
        ("step order", p.replace("step 1", "step 9")),
        ("self reference", p.replace("plus-two (0)", "plus-two (1)")),
        ("forward reference", p.replace("plus-two (0)", "plus-two (2)")),
        ("premise count", p.replace("plus-two (0)", "plus-two ()")),
        ("extra premise", p.replace("plus-two (0)", "zero (0)")),
        ("unknown rule", p.replace("plus-two (0)", "unknown (0)")),
        ("conclusion", p.replace("(step 1 plus-two (0) (even (s (s z))))", "(step 1 plus-two (0) (even z))")),
        ("invalid unused step", p + "(step 3 zero () (even (s z)))"),
        ("rule injection", p + "(rule injected () (even z))"),
        ("missing result", p.replace("(result four-is-even 2)", "")),
        ("repeated result", p + "(result four-is-even 2)"),
        ("unknown goal", p.replace("result four-is-even", "result unknown")),
        ("wrong result", p.replace("result four-is-even 2", "result four-is-even 0")),
        ("unknown result step", p.replace("result four-is-even 2", "result four-is-even 3")),
        ("negative index", p.replace("step 0", "step -0")),
        ("index overflow", p.replace("step 0", "step 18446744073709551616")),
    ]:
        yield name, t, g, proof, False
    yield "plus index", t, g, p.replace("step 0", "step +0"), True
    yield "empty goals", t, "", p, False
    yield "duplicate goals", t, g + g, p, False
    yield "missing extra goal", t, g + "(goal another (even z))", p, False
    yield "multiple goals", t, g + "(goal another (even z))", p + "(result another 0)", True
    for j in ["(even ?x)", "(even (z))", "(even (s))", "(even (s z z))", "(even z z)", "(even missing)", "(unknown z)", "(even (even z))"]:
        yield "bad goal " + j, t, f"(goal g {j})", "", False
        yield "bad statement " + j, t, "(goal g (even z))", f"(step 0 zero () {j}) (result g 0)", False
    for source in ["(sort A) (sort A)", "(ctor x () Missing)", "(sort A) (ctor x () A) (ctor x () A)", "(sort A) (pred p (A)) (pred p (A))", "(pred p ()) (rule r () (p)) (rule r () (p))", "(sort ?A)", "(unknown A)", "()", "(", ")", "(a", "((a)", "(" * 300 + "x" + ")" * 300, "(sort A) (sort B) (pred p (A B)) (rule bad () (p ?x ?x))", "(sort A) (pred p (A)) (rule bad () (p ?))"]:
        yield "invalid theory " + source[:80], source, g, p, False
    join = "(sort N) (ctor z () N) (ctor s (N) N) (pred p (N)) (pred q (N)) (pred r (N N)) (rule p0 () (p z)) (rule q1 () (q (s z))) (rule join ((p ?x) (q ?x)) (r ?x ?x))"
    for conclusion in ["(r z z)", "(r z (s z))", "(r (s z) (s z))"]:
        proof = f"(step 0 p0 () (p z)) (step 1 q1 () (q (s z))) (step 2 join (0 1) {conclusion}) (result g 2)"
        yield "consistent assignment " + conclusion, join, f"(goal g {conclusion})", proof, False
    simple = "(sort N) (sort M) (ctor z () N) (ctor s (N) N) (ctor other () M) (pred p (N)) (rule any () (p ?x)) (rule copy ((p ?x)) (p ?x))"
    for tail, expected in [
        ("(?x z)", True), ("(p z)", True), ("(?x z) (p z)", True),
        ("", False), ("(?x other)", False), ("(?bad z)", False),
        ("(?x z) (?x z)", False), ("(p z) (p z)", False),
        ("(?x (s z)) (p z)", False),
    ]:
        yield "bindings " + tail, simple, "(goal g (p z))", f"(step 0 any () {tail}) (result g 0)", expected
    for defs, expected in [
        ("(def ?a z)", True), ("(def ?a z) (def ?b ?a)", True),
        ("(def ?a z) (def ?a z)", False), ("(def a z)", False),
        ("(def ? z)", False), ("(def ?a ?a)", False), ("(def ?a ?b) (def ?b z)", False),
    ]:
        yield "definitions " + defs, simple, "(goal g (p z))", defs + "(step 0 any () (?x ?a)) (result g 0)", expected
    yield "goals cannot use proof definitions", simple, "(goal g (p ?a))", "(def ?a z) (step 0 any () (?x ?a)) (result g 0)", False
    yield "nullary predicate", "(pred p ()) (rule r () (p))", "(goal g (p))", "(step 0 r ()) (result g 0)", True
    spaces = [*range(9, 14), 0x20, 0x85, 0xa0, 0x1680, *range(0x2000, 0x200b), 0x2028, 0x2029, 0x202f, 0x205f, 0x3000]
    for cp in spaces:
        ws = chr(cp)
        uncommented = re.sub(r";[^\n]*", "", t)
        yield f"Unicode space U+{cp:04X}", uncommented.replace(" ", ws), g.replace(" ", ws), p.replace(" ", ws), True
    for name in ["증명", "\U0001f600", "x\u200by", "x\ufeffy"]:
        yield "Unicode name " + name, t, g.replace("four-is-even", name), p.replace("four-is-even", name), True
    for bad in [b"\xff", b"\xc0\x80", b"\xed\xa0\x80", b"\xf4\x90\x80\x80", b"\xe2\x82"]:
        yield "invalid UTF-8 theory", t.encode() + b";" + bad, g, p, False
        yield "invalid UTF-8 goal", t, g.encode() + b";" + bad, p, False
        yield "invalid UTF-8 proof", t, g, p.encode() + b";" + bad, False
    for depth in [254, 255, 256, 257]:
        term = "(s " * depth + "z" + ")" * depth
        yield f"depth {depth}", simple, f"(goal g (p {term}))", f"(step 0 any () (?x {term})) (result g 0)", None
    # More than one arena rehash; shared subterms and repeated terms must
    # retain their ids. Each def is shallow even though the DAG is deep.
    proof = ["(def ?n0 z)", "(step 0 any () (?x ?n0))"]
    for n in range(1, 2200):
        proof += [f"(def ?n{n} (s ?n{n - 1}))", f"(step {n} any () (?x ?n{n}))"]
    proof += ["(step 2200 copy (2199))", "(result g 0)"]
    yield "arena growth and shared DAG", simple, "(goal g (p z))", "\n".join(proof), True
    rng = random.Random(20261027)
    for n in range(350):
        source = rng.choice([p, compact])
        # Mutate tokens without imposing an expected verdict: harmless
        # whitespace changes and valid alternate proof forms are allowed.
        for _ in range(rng.randint(1, 4)):
            at = rng.randrange(len(source))
            source = source[:at] + rng.choice(["", "(", ")", "?x", "0", "1", ";", " ", "\n", "\u3000"]) + source[at + 1:]
        yield f"mutation {n}", t, g, source, None
    for n in range(40):
        proof = ["(step 0 zero ())"] + [f"(step {i} plus-two ({i - 1}))" for i in range(1, n + 1)]
        term = "(s " * (2 * n) + "z" + ")" * (2 * n)
        proof.append(f"(result g {n})")
        yield f"generated derivation {n}", t, f"(goal g (even {term}))", "\n".join(proof), True


def main():
    ap = argparse.ArgumentParser(__doc__)
    ap.add_argument("--horn", type=Path, default=ROOT.parent / "horn")
    ap.add_argument("--compiler", type=Path, default=ROOT / "out/jihoo")
    args = ap.parse_args()
    horn = args.horn.resolve()
    out = ROOT / "out/kernel"
    out.mkdir(parents=True, exist_ok=True)
    build(str(args.compiler.resolve()), "build", "experimental/kernel/main.jh", "-o", str(out / "jihoo-kernel"))
    modules = "\n".join(f"#[path = {json.dumps(str(horn / 'src' / (m + '.rs')))}] mod {m};" for m in ["kernel", "lex", "sexp"])
    reference = out / "reference.rs"
    reference.write_text("#![allow(dead_code)]\n" + modules + r'''
fn main() {
    let args: Vec<_> = std::env::args().collect();
    let check = || -> Result<kernel::Report, String> {
        let theory = kernel::Theory::parse(&std::fs::read_to_string(&args[1]).map_err(|e| e.to_string())?)?;
        let goals = std::fs::read_to_string(&args[2]).map_err(|e| e.to_string())?;
        let proof = std::fs::File::open(&args[3]).map_err(|e| e.to_string())?;
        theory.check_reader(&goals, std::io::BufReader::with_capacity(7, proof))
    };
    match check() {
        Ok(r) => println!("ACCEPT: {} goals, {} proof steps, {} bytes, {} distinct terms", r.goals, r.steps, r.bytes, r.terms),
        Err(e) => { eprintln!("REJECT: {e}"); std::process::exit(1); }
    }
}
''')
    build("rustc", "--edition=2024", "-O", str(reference), "-o", str(out / "rust-kernel"))
    count = accepted = 0
    for name, theory, goals, proof, expected in cases(horn):
        paths = [out / "case.horn", out / "case.goals", out / "case.proof"]
        for path, content in zip(paths, [theory, goals, proof]):
            path.write_bytes(content.encode() if isinstance(content, str) else content)
        rust = run(str(out / "rust-kernel"), *map(str, paths))
        jihoo = run(str(out / "jihoo-kernel"), *map(str, paths))
        ok = rust.returncode == 0
        if rust.returncode not in [0, 1] or jihoo.returncode not in [0, 1] or (jihoo.returncode == 0) != ok or (ok and rust.stdout != jihoo.stdout) or (expected is not None and ok != expected):
            raise AssertionError(f"{name}: expected={expected}\nRust ({rust.returncode}): {rust.stdout!r} {rust.stderr!r}\njihoo ({jihoo.returncode}): {jihoo.stdout!r} {jihoo.stderr!r}\nInputs retained in {out}")
        count += 1
        accepted += ok
    build(str(args.compiler.resolve()), "run", "experimental/kernel/comptime.jh")
    invalid = out / "invalid-comptime.jh"
    invalid.write_text((ROOT / "experimental/kernel/comptime.jh").read_text().replace("(step 2 plus-two (1))", "(step 2 plus-two (2))"))
    rejected = run(str(args.compiler.resolve()), "build", str(invalid), "-I", "experimental/kernel", "-o", str(out / "invalid-comptime"))
    if rejected.returncode == 0 or b"compile-time evaluation reached a trap" not in rejected.stderr:
        raise AssertionError(f"invalid compile-time certificate was not rejected by the evaluator: {rejected.stderr!r}")
    print(f"{count} differential cases passed ({accepted} accepted, {count - accepted} rejected); compile-time acceptance/rejection passed")


if __name__ == "__main__":
    main()
