# General theorems in a jihoo compile-time development

This experiment defines natural numbers and addition in a proof domain,
proves a statement for **every** natural number by structural induction,
and reuses that derivation in another theorem. Construction and checking
are ordinary jihoo functions. The example invokes the checker in a `const`
initializer; an invalid development fails compilation.

It is a library experiment, with no new jihoo syntax, compiler rules, or
runtime integer semantics. It does not require running Horn separately or
copying a computed answer into the program.

## Try it

From the repository root:

```sh
mkdir -p out
nix develop --command jihoo build -O2 compiler/main.jh -o out/jihoo
nix develop --command out/jihoo run experimental/proofs/example.jh -I experimental/kernel
```

Output:

```text
checked at compile time: 2 theorems, 2 general statements, 1 induction, 5 proof steps
add_zero: for every n, add(n, zero) = n
twice_zero: for every n, add(add(n, zero), zero) = n
```

`nat.jh` is the development; `example.jh` makes its verification a compile-time
obligation. `z` denotes zero and `s` its successor. The printed equations
abbreviate Horn relation judgments: `add m n r` means an addition derivation
with result `r`. The `twice` relation chains two additions of zero.

The interesting part of `nat.jh` is:

```jihoo
let base = p.step("add.z", [], "(add z z z)")
let ih = p.hypothesis("(add k z k)")
let successor = p.step("add.s", [ih], "(add (s k) z (s k))")
let add_zero = p.induction("n", "(add n z n)", [
    proofs.case(base, []), proofs.case(successor, ["k"])
])
p.theorem("add_zero", "(add n z n)", add_zero)

let twice_zero = p.step("twice.body", [add_zero, add_zero], "(twice n n)")
p.theorem("twice_zero", "(twice n n)", twice_zero)
```

`ih` is an assumption during the successor case. The induction checker
discharges it only if it is the motive at a recursive constructor argument.
A hypothesis cannot be exported as an unconditional theorem. The second
theorem refers to the first derivation twice; it does not install the first
statement as a new axiom.

There is no automatic proof search. The jihoo program constructs a certificate
with handles, and a separate checker checks the complete certificate against
the original theory and the statements passed to `theorem`. Handles are local
step numbers, not independently authenticated proof objects. Reuse is within
one development; there is no cross-development theorem import yet.

## What is integrated

Changing the actual definition, proof construction, or expected statement
changes what the compile-time checker receives. Incorrect changes make the
`const` initializer reach `trap`. The definitions, proof steps and goals
live in imported jihoo modules and are rebuilt with the program. The same
development is available at runtime for diagnostics and export.

This connects **proof-domain definitions to their theorems**. It does not
yet connect a theorem to an ordinary jihoo `fn` implementing the same
algorithm. `Nat` here is finite constructor trees, not `u64` or `i64`.
The experiment proves relational derivability; it does not separately
establish coverage, functional uniqueness, or termination of arbitrary
user-written definitions.

The next [generated codec experiment](../verified-codec/README.md) connects
ground certificates to executable enum lookup tables with a small trusted
adapter. It uses the original ground rules rather than this schematic checker.

## Checker and trust boundary

The generic ground inference checks in `experimental/kernel` are unchanged. A ground
certificate cannot by itself express the universal claim checked here.
`schematic.jh` ports a **subset** of Horn's `src/schematic.rs`: typed open
terms, rule steps, plain hypotheses, structural induction without outer
hypotheses, and simultaneous instances of hypothesis-free facts. It uses
owned trees instead of Horn's hash-consed arena. It knows no special rules
for addition, natural numbers, cubical type theory, or equality.
The reference checkout is commit `18caf6d39088e1569beff678bc4461a28b8d2827`.

The supported certificate forms are:

```text
(var NAME SORT)
(def ?NAME TERM)
(step INDEX RULE (REF...) ITEM...)
(hyp INDEX JUDGMENT)
(induct INDEX VARIABLE JUDGMENT ((CASE_STEP ARG_VAR...)...))
(result NAME REF)

REF = INDEX | (INDEX (VARIABLE TERM)...)
```

Theory declarations use the existing Horn format. Goals are `(var NAME SORT)`
and `(goal NAME JUDGMENT)`. Case order is constructor declaration order.
Implication goals, rule hypotheses, `apply`, `invert`, and induction with
outer hypotheses are rejected; this is not a port of the full surface
language, cubical engine, or schematic checker.

Trust includes this additional schematic checker and its parser, the selected
theory and goal specification, and the jihoo compiler and execution environment.
Certificate construction is untrusted. The schema checker validates declared
sorts and arities, consistent assignments, earlier-only references, variable
scope, induction freshness and assumptions, and exact, complete, unique goals.
In particular, it rejects dropping a free variable of an empty sort from a
rule's premises, and induction on a variable absent from its motive.

`syntax.jh` reads whole strings with an ASCII fast path, strict UTF-8 for
non-ASCII text and comments, and the existing nesting limit of 256. This
avoids the buffered file reader's cost during compile-time evaluation. Neither
the interpreter's step, memory and recursion limits nor the original ground
kernel's parser were changed. Larger developments can still exceed those
limits; the tree representation also does not provide the ground kernel's
scalability on shared terms.

Horn's Agda development proves properties of its calculus and checker model.
It does not prove this jihoo implementation or its parser correct.
Acceptance establishes derivability in the selected theory, not the theory's
adequacy for an intended mathematics. See
[Horn's trust boundary](../../../horn/docs/TRUST.md).
The source projects use Apache-2.0.

## Reproduce validation

CI compiles and runs this example and the generated codec example with the
packaged compiler on x86_64 and aarch64 Linux. To run that smoke check locally:

```sh
nix develop --command bash scripts/check-proof-experiments.sh out/jihoo
```

The full differential and negative-certificate suite is separate:

```sh
nix develop --command python3 experimental/proofs/check.py
```

This needs Python, Rust/Cargo, LLVM `opt`, and the sibling Horn checkout.
`--compiler PATH` and `--horn PATH` override their defaults. Rust is used
only for differential validation, not by the compile-time example.
Generated binaries, exported inputs, failing cases, LLVM IR, and
`report.json` go under `out/proofs`; the Horn checkout is read without
modification. The reference is built offline with no crate dependencies.

Validation on 2026-10-27:

- 701 differential cases matched Horn's Rust schematic checker: 99 accepted
  and 602 rejected. Every successful report field was compared.
- The corpus includes the ground experiment's cases, schematic induction and
  reuse cases, binary-tree induction, empty-sort regressions, substitutions,
  Unicode and invalid UTF-8, malformed input, and deterministic mutations.
  The ground corpus's 2,200-step shared-DAG case is reduced to depth 95 for
  this tree-based implementation; no large-DAG performance claim is made.
- The example compiled and ran. Changing its base definition, a proof
  premise, a theorem statement, or exporting an undischarged hypothesis
  caused compilation to fail during evaluation.
- At O2, LLVM removed the verifier, parser and certificate builder functions
  from the example. Proof checking is not deferred to execution.
- The example also emitted an aarch64 object. It was not run on aarch64.

To inspect a rejection at runtime, export the inputs and use the standalone
checker:

```sh
mkdir -p out/proofs
nix develop --command out/jihoo run experimental/proofs/export.jh -I experimental/kernel -- out/proofs
nix develop --command out/jihoo build experimental/proofs/main.jh -I experimental/kernel -o out/proofs/schematic-check
out/proofs/schematic-check out/proofs/theory.horn out/proofs/goals out/proofs/proof
```

Edit those exported files to inspect failed cases. Editing them does not
change the source development or its compile-time obligation.
