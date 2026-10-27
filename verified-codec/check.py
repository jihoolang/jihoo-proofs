#!/usr/bin/env python3
"""Validate the generated codec, proof binding, and the finite table model."""
import argparse
import itertools
import json
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent


def run(*args):
    return subprocess.run(list(map(str, args)), cwd=ROOT, capture_output=True, timeout=90)


def require(*args):
    p = run(*args)
    if p.returncode:
        raise AssertionError(f"{args}\n{p.stdout!r}\n{p.stderr.decode(errors='replace')}")
    return p


def candidate(body="", evidence="", variants="A, B, C", runtime=False):
    evidence = evidence or "let p = Candidate.generate(T)\n        producer.certificate(p, ordinal)"
    construction = "let c = codec.build(E, Candidate)" if runtime else "let c = VERIFIED"
    constant = "" if runtime else "const VERIFIED = codec.build(E, Candidate)"
    return f'''import codec
import producer
import program
enum E {{ {variants} }}
struct Candidate {{}}
impl Candidate {{
    pub fn generate(comptime T: type) -> program.Plan(variant_count(T)) {{
        var p = producer.Reverse.generate(T)
        {body}
        p
    }}
    pub fn certificate(comptime T: type, ordinal: i64) -> String {{
        {evidence}
    }}
}}
{constant}
fn main() {{
    {construction}
    inline for i in 0..variant_count(E) {{
        let value = make_variant(E, i, fn(j) {{ trap() }})
        assert(c.encode(value) == variant_count(E) - 1 - i, "encoding")
        assert(variant_of(c.decode(c.encode(value)).unwrap()) == i, "round trip")
    }}
    assert(c.decode(-1).is_none(), "negative tag")
    assert(c.decode(variant_count(E)).is_none(), "large tag")
    println("ok")
}}
'''


def main():
    ap = argparse.ArgumentParser(__doc__)
    ap.add_argument("--compiler", type=Path, default=ROOT / "out/jihoo")
    args = ap.parse_args()
    compiler = args.compiler.resolve()
    out = ROOT / "out/verified-codec"
    out.mkdir(parents=True, exist_ok=True)
    includes = ["-I", HERE, "-I", ROOT / "experimental/proofs", "-I", ROOT / "experimental/kernel"]

    for source in ["example", "inspect"]:
        require(compiler, "build", HERE / f"{source}.jh", *includes, "-o", out / source)
    runtime_cases = 0
    for tag, value in [(0, "Green"), (1, "Amber"), (2, "Red"), (-1, None), (3, None), (9223372036854775807, None), (-9223372036854775808, None)]:
        expected = "Red encodes to 2\n" + (f"{value}\nround trip: true\n" if value else "invalid tag\n")
        assert require(out / "example", tag).stdout.decode() == expected
        runtime_cases += 1

    positives = [("one", "A", False), ("two", "A, B", False), ("three", "A, B, C", False), ("runtime-construction", "A, B, C", True)]
    for name, variants, runtime in positives:
        path = out / f"valid-{name}.jh"
        path.write_text(candidate(variants=variants, runtime=runtime))
        require(compiler, "build", path, *includes, "-o", out / f"valid-{name}")
        assert require(out / f"valid-{name}").stdout == b"ok\n"

    negatives = [
        ("wrong-decoder", candidate("p.decode[0] = 0")),
        ("duplicate-encoding", candidate("p.encode[1] = p.encode[0]")),
        ("negative-tag", candidate("p.encode[0] = -1")),
        ("decoder-out-of-range", candidate("p.decode[0] = variant_count(T)")),
        ("correct-proof-for-another-correct-plan", candidate(
            "for i in 0..variant_count(T) { p.encode[i] = i; p.decode[i] = i }",
            "producer.Reverse.certificate(T, ordinal)")),
        ("proof-for-another-row", candidate(evidence="producer.Reverse.certificate(T, (ordinal + 1) % variant_count(T))")),
        ("stale-proof-after-adding-a-variant", candidate(evidence="producer.Reverse.certificate(Earlier, ordinal)") + "\nenum Earlier { X, Y }\n"),
        ("axiom-injection", candidate(evidence='"(rule forged () (rt z e e))".to_string()')),
        ("empty-proof", candidate(evidence="String.new()")),
        ("unknown-result", candidate(evidence='"(result roundtrip 0)".to_string()')),
        ("invalid-unused-step", candidate(evidence='producer.Reverse.certificate(T, ordinal) + "(step 5 h () (at (s z) e z))"')),
        ("payload-variant", candidate(variants="A(i64), B, C")),
        ("bad-runtime-construction", candidate("p.decode[0] = 0", runtime=True)),
    ]
    for name, source in negatives:
        path = out / f"invalid-{name}.jh"
        path.write_text(source)
        result = run(compiler, "build", path, *includes, "-o", out / f"invalid-{name}")
        if result.returncode == 0 or b"compile-time evaluation reached a trap" not in result.stderr:
            raise AssertionError(f"{name} was not rejected by compile-time verification: {result.stderr!r}")

    # A safe client cannot replace a checked plan after certification.
    forged = out / "invalid-private-plan.jh"
    forged.write_text(candidate().replace("let c = VERIFIED", "var c = VERIFIED\n    c.plan.encode[0] = 0"))
    result = run(compiler, "build", forged, *includes, "-o", out / "invalid-private-plan")
    assert result.returncode != 0 and b"private" in result.stderr, result.stderr

    # Independent oracle: exhaust every pair of length-three tables whose
    # entries are 0..2, at every ordinal. No proof-producing code is used in
    # the expected result, and no native execution is inferred from a proof.
    table_cases = accepted = 0
    for entries in itertools.product(range(3), repeat=6):
        forward, backward = entries[:3], entries[3:]
        for row in range(3):
            expected = backward[forward[row]] == row
            result = run(out / "inspect", out, row, *entries)
            if result.returncode not in [0, 1] or (result.returncode == 0) != expected:
                raise AssertionError(f"table mismatch E={forward} D={backward} row={row}: {result.stdout!r} {result.stderr!r}")
            table_cases += 1
            accepted += expected

    # LLVM must retain the codec behavior while removing all checking,
    # proof generation, and construction of the table constants.
    require(compiler, "emit-llvm", HERE / "example.jh", *includes, "-o", out / "example.ll")
    require("opt", "-S", "-passes=default<O2>", out / "example.ll", "-o", out / "example.opt.ll")
    definitions = [line for line in (out / "example.opt.ll").read_text().splitlines() if line.startswith("define ")]
    forbidden = ["kernel.", "syntax.", "sexp.", "lex.", "producer.", "model.", "codec.verify", "codec.build"]
    assert not any(any(name in line for name in forbidden) for line in definitions), definitions
    require(compiler, "emit-obj", HERE / "example.jh", *includes, "--target", "aarch64", "-o", out / "example-aarch64.o")
    report = {"runtime_inputs": runtime_cases, "positive_construction_cases": len(positives), "compile_time_rejection_cases": len(negatives), "private_plan_replacement_rejected": True, "exhaustive_table_cases": table_cases, "accepted_table_rows": accepted, "rejected_table_rows": table_cases - accepted, "optimized_runtime_verifier_functions": 0, "aarch64_object_emitted": True}
    (out / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(f"{runtime_cases} runtime inputs, {len(positives)} constructions, {len(negatives)} compile-time rejections, plan privacy, and {table_cases} exhaustive table rows passed; verification erased at O2")


if __name__ == "__main__":
    main()
