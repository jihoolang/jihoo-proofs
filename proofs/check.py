#!/usr/bin/env python3
"""Check the proof experiment against Horn, including adversarial certificates."""
import argparse
import importlib.util
import json
import random
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
sys.dont_write_bytecode = True


def run(*args):
    return subprocess.run(list(map(str, args)), cwd=ROOT, capture_output=True, timeout=90)


def require(*args):
    result = run(*args)
    if result.returncode:
        raise RuntimeError(f"{args}\n{result.stdout.decode(errors='replace')}\n{result.stderr.decode(errors='replace')}")
    return result


def schematic_cases(theory, goals, proof):
    yield "definition, induction, and lemma reuse", theory, goals, proof, True
    for name, old, new in [
        ("wrong recursive definition", "(add (s ?m) ?n (s ?r))", "(add (s ?m) ?n ?r)"),
        ("wrong base definition", "(add z ?n ?n)", "(add z ?n (s ?n))"),
    ]:
        assert old in theory
        yield name, theory.replace(old, new), goals, proof, False
    for name, old, new in [
        ("missing induction case", "((0) (2 k) )", "((0))"),
        ("wrong base case", "((0) (2 k) )", "((2) (2 k))"),
        ("wrong successor case", "((0) (2 k) )", "((0) (0 k))"),
        ("case variable is in motive", "((0) (2 k) )", "((0) (2 n))"),
        ("missing fresh variable", "((0) (2 k) )", "((0) (2))"),
        ("future case reference", "((0) (2 k) )", "((0) (3 k))"),
        ("wrong hypothesis", "(hyp 1 (add k z k))", "(hyp 1 (add k z (s k)))"),
        ("premise is not the induction hypothesis", "add.s (1 )", "add.s (0 )"),
        ("self reference", "add.s (1 )", "add.s (2 )"),
        ("unproved lemma reuse", "twice.body (3 3 )", "twice.body (1 1 )"),
        ("duplicate result", "(result add_zero 3)", "(result add_zero 3) (result add_zero 3)"),
        ("missing result", "(result add_zero 3)", ""),
        ("index wraps to zero", "(step 0 ", "(step 18446744073709551616 "),
        ("negative zero index", "(step 0 ", "(step -0 "),
    ]:
        assert old in proof, old
        yield name, theory, goals, proof.replace(old, new), False
    yield "changed theorem statement", theory, goals.replace("(goal add_zero (add n z n))", "(goal add_zero (add n z (s n)))"), proof, False
    yield "unchecked extra step", theory, goals, proof + "(step 5 add.z () (add (s z) z z))", False
    yield "proof cannot add an axiom", theory, goals, proof + "(rule injected () (twice z z))", False
    yield "hypothesis cannot be a result", theory, "(var n Nat) (goal g (add n z n))", "(hyp 0 (add n z n)) (result g 0)", False
    yield "hypothesis cannot be instantiated", theory, "(var n Nat) (goal g (add n z n))", "(hyp 0 (add n z n)) (result g (0 (n z)))", False

    prefix = proof[:proof.index("(result add_zero")]
    instance = "(3 (n (s n)))"
    yield "open simultaneous substitution", theory, "(var n Nat) (var k Nat) (goal g (add (s n) z (s n)))", prefix + f"(result g {instance})", True
    yield "ground specialization", theory, "(var n Nat) (var k Nat) (goal g (add (s (s z)) z (s (s z))))", prefix + "(result g (3 (n (s (s z)))))", True
    for name, ref in [
        ("duplicate substitution", "(3 (n z) (n z))"),
        ("unknown substitution variable", "(3 (unknown z))"),
        ("unknown substitution term", "(3 (n missing))"),
        ("wrongly sorted substitution", "(3 (n t))"),
        ("out of range instance", "(99 (n z))"),
    ]:
        yield name, theory + "(sort B) (ctor t () B)", "(var n Nat) (var k Nat) (goal g (add z z z))", prefix + f"(result g {ref})", False
    yield "instance used as a premise", theory, "(var n Nat) (var k Nat) (goal g (add (s (s n)) z (s (s n))))", prefix + f"(step 4 add.s ({instance})) (result g 4)", True

    empty = "(sort E) (pred p (E)) (pred q ()) (rule intro () (p ?x)) (rule elim ((p ?x)) (q))"
    yield "empty sort cannot supply an existential witness", empty, "(goal g (q))", "(var X E) (step 0 intro () (p X)) (step 1 elim (0)) (result g 1)", False
    bound = "(sort E) (pred q ()) (rule bad () (q))"
    yield "unknown explicit binding", bound, "(goal g (q))", "(var X E) (step 0 bad () (?x X)) (result g 0)", False
    uninhabited = "(sort E) (ctor next (E) E) (pred false ())"
    yield "vacuous induction cannot prove unrelated false", uninhabited, "(var X E) (goal g (false))", "(var Y E) (hyp 0 (false)) (induct 1 X (false) ((0 Y))) (result g 1)", False

    tree = "(sort T) (ctor leaf () T) (ctor node (T T) T) (pred p (T)) (rule leaf () (p leaf)) (rule node ((p ?a) (p ?b)) (p (node ?a ?b)))"
    tree_goals = "(var X T) (var A T) (var B T) (goal g (p X))"
    tree_proof = "(step 0 leaf ()) (hyp 1 (p A)) (hyp 2 (p B)) (step 3 node (1 2)) (induct 4 X (p X) ((0) (3 A B))) (result g 4)"
    yield "generic induction on a binary tree", tree, tree_goals, tree_proof, True
    yield "case variables must be distinct", tree, tree_goals, tree_proof.replace("(3 A B)", "(3 A A)"), False
    yield "circular hypothesis is not structural induction", tree, tree_goals, tree_proof.replace("(hyp 1 (p A))", "(hyp 1 (p (node A B)))"), False
    yield "induction on a sort with no constructors is vacuous", "(sort E) (pred p (E))", "(var X E) (goal g (p X))", "(induct 0 X (p X) ()) (result g 0)", True

    # Deterministic edits exercise interactions that hand-picked attacks miss.
    rng = random.Random(20261027)
    for i in range(150):
        mutated = proof
        for _ in range(1 + i % 3):
            at = rng.randrange(len(mutated))
            op = rng.randrange(3)
            char = rng.choice("() 01234nksz?;\n")
            if op == 0:
                mutated = mutated[:at] + char + mutated[at:]
            elif op == 1:
                mutated = mutated[:at] + mutated[at + 1:]
            else:
                mutated = mutated[:at] + char + mutated[at + 1:]
        yield f"schematic mutation {i}", theory, goals, mutated, None


def main():
    ap = argparse.ArgumentParser(__doc__)
    ap.add_argument("--horn", type=Path, default=ROOT.parent / "horn")
    ap.add_argument("--compiler", type=Path, default=ROOT / "out/jihoo")
    args = ap.parse_args()
    horn, compiler = args.horn.resolve(), args.compiler.resolve()
    out = ROOT / "out/proofs"
    out.mkdir(parents=True, exist_ok=True)
    include = ROOT / "experimental/kernel"
    for source, binary in [("main", "schematic-check"), ("export", "export"), ("example", "example")]:
        require(compiler, "build", HERE / f"{source}.jh", "-I", include, "-o", out / binary)
    example = require(out / "example")
    assert example.stdout == (
        b"checked at compile time: 2 theorems, 2 general statements, 1 induction, 5 proof steps\n"
        b"add_zero: for every n, add(n, zero) = n\n"
        b"twice_zero: for every n, add(add(n, zero), zero) = n\n"
    ), example.stdout
    require(compiler, "emit-llvm", HERE / "example.jh", "-I", include, "-o", out / "example.ll")
    require("opt", "-S", "-passes=default<O2>", out / "example.ll", "-o", out / "example.opt.ll")
    definitions = [line for line in (out / "example.opt.ll").read_text().splitlines() if line.startswith("define ")]
    assert not any(any(name in line for name in ["schematic.", "syntax.", "proofs.", "nat.", "main.verify."]) for line in definitions), definitions
    require(out / "export", out)
    require("cargo", "build", "--offline", "--locked", "--release", "--manifest-path", horn / "Cargo.toml", "--target-dir", out / "rust", "--bin", "schematic-kernel")
    rust = out / "rust/release/schematic-kernel"

    spec = importlib.util.spec_from_file_location("ground_cases", ROOT / "experimental/kernel/check.py")
    ground = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(ground)
    theory, goals, proof = [(out / name).read_text() for name in ["theory.horn", "goals", "proof"]]
    cases = [*ground.cases(horn), *schematic_cases(theory, goals, proof)]
    count = accepted = 0
    for name, t, g, p, expected in cases:
        # The experiment uses trees, not the ground kernel's shared DAG.
        # Keep the same shared-definition regression at a bounded tree size.
        if name == "arena growth and shared DAG":
            p = "(def ?n0 z) (step 0 any () (?x ?n0)) " + " ".join(
                f"(def ?n{i} (s ?n{i - 1})) (step {i} any () (?x ?n{i}))" for i in range(1, 96)
            ) + " (step 96 copy (95)) (result g 0)"
        paths = [out / "case.horn", out / "case.goals", out / "case.proof"]
        for path, content in zip(paths, [t, g, p]):
            path.write_bytes(content.encode() if isinstance(content, str) else content)
        reference = run(rust, *paths)
        candidate = run(out / "schematic-check", *paths)
        ok = reference.returncode == 0
        match = re.fullmatch(rb"ACCEPT (\d+) goals \((\d+) open\), (\d+) steps, (\d+) hypotheses, (\d+) inductions, (\d+) instance references\n", reference.stdout)
        same_report = not ok or (match is not None and candidate.stdout == b"ACCEPT " + b" ".join(match.groups()) + b"\n")
        if reference.returncode not in [0, 1] or candidate.returncode not in [0, 1] or (candidate.returncode == 0) != ok or not same_report or (expected is not None and ok != expected):
            raise AssertionError(f"{name}: expected={expected}\nRust ({reference.returncode}): {reference.stdout!r} {reference.stderr!r}\njihoo ({candidate.returncode}): {candidate.stdout!r} {candidate.stderr!r}\nInputs retained in {out}")
        count += 1
        accepted += ok

    # Mutate the actual user-facing development and require compile errors.
    nat = (HERE / "nat.jh").read_text()
    tail = '\nfn verify() -> i64 { match development().check() { Ok(r) => r.goals, Err(_) => trap() } }\nconst CHECKED = verify()\nfn main() { println(CHECKED) }\n'
    changes = [
        ("definition", "(add z ?n ?n)", "(add z ?n (s ?n))"),
        ("proof", 'p.step("add.s", [ih]', 'p.step("add.s", [base]'),
        ("statement", 'p.theorem("add_zero", "(add n z n)"', 'p.theorem("add_zero", "(add n z (s n))"'),
        ("hypothesis", 'p.theorem("add_zero", "(add n z n)", add_zero)', 'p.theorem("add_zero", "(add n z n)", ih)'),
    ]
    for name, old, new in changes:
        assert old in nat
        source = out / f"invalid-{name}.jh"
        source.write_text(nat.replace(old, new) + tail)
        result = run(compiler, "build", source, "-I", HERE, "-I", include, "-o", out / f"invalid-{name}")
        if result.returncode == 0 or b"compile-time evaluation reached a trap" not in result.stderr:
            raise AssertionError(f"changed {name} was not rejected during compile-time checking: {result.stderr!r}")
    report = {"differential_cases": count, "accepted": accepted, "rejected": count - accepted, "compile_time_negative_cases": len(changes), "shared_definition_depth": 95, "optimized_runtime_verifier_functions": 0}
    (out / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(f"{count} differential cases passed ({accepted} accepted, {count - accepted} rejected); compile-time acceptance and {len(changes)} rejection cases passed")


if __name__ == "__main__":
    main()
