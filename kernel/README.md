# Horn kernel experiment

This is a jihoo port of the trusted ground Horn certificate checker in
`../horn`, based on commit `18caf6d39088e1569beff678bc4461a28b8d2827`.
The upstream project and this port use Apache-2.0.

The experiment establishes that the checker can be written in ordinary
jihoo and run both at runtime and during compile-time evaluation. The codec
adapter below connects ground certificates to executable tables; general
jihoo function contracts still require a semantics and generated obligations.

The separate [proof development experiment](../proofs/README.md) adds a
restricted schematic checker for general statements, structural induction,
and derivation reuse at compile time. It leaves this ground checker unchanged
and adds its own trust obligations; it does not establish program contracts.

The [generated codec experiment](../verified-codec/README.md) connects this
ground checker to a bounded executable table representation through a small
trusted adapter. `Theory.from_forms` accepts S-expression trees from
metaprograms, with the same declaration validation used by `Theory.parse`.
The ground certificate rules and checks are unchanged.

## Next work and destination

The first [roadmap milestone](../../docs/internals/roadmap.md#1-bring-the-existing-experiments-into-supported-use)
prioritizes this checker as a reusable library. Extract local acceptance and
rejection cases from differential tests so ordinary CI needs no sibling Horn
checkout, retain a separately pinned differential suite, and stabilize the
checking API and trust boundary. Migrate reusable modules into `lib/` and
the CLI into an example, updating the codec and proof consumers together.
Completion requires packaged imports without `-I experimental/...` and
regression coverage on both supported targets.

## Scope

| jihoo file | upstream source | responsibility |
| --- | --- | --- |
| `kernel.jh` | `src/kernel.rs` | theory validation, sorting, hash-consing, matching, instantiation, steps and exact goal results |
| `lex.jh` | `src/lex.rs` | streaming, Unicode-aware S-expression tokens |
| `sexp.jh` | `src/sexp.rs` | owned theory trees and a nesting limit of 256 |
| `main.jh` | `src/bin/kernel.rs` | file input and an ACCEPT/REJECT command line |
| `comptime.jh` | experiment | compile-time checking of a compact natural-number certificate |
| `borrow_repro.jh` | experiment | the view-method borrow limitation found during the port; now accepted |

The proof input remains incremental. The kernel preserves the ground Horn
format, explicit and inferred conclusions, variable bindings, abbreviations,
earlier-only step references, one consistent assignment per step, and exact,
complete, unique result checks. Every ground node is checked for sorting and
arity before interning. Full-node comparison decides equality even when
hashes collide. The arena retains the upstream flat-node representation,
hash function and linear probing.

Host-sized indices use jihoo's `i64`; ground ids remain `u32`. A parsed
step index above the signed range is guaranteed out of bounds, never wrapped
to a valid index. Goals use a hash map rather than a tree map because ordering
only affects missing-goal diagnostics. Error messages are shorter; verdicts
and successful report counts are compared with Rust. Timing output is omitted.
The cubical engine, schematic checker, certificate producers, oracle and
compression code are outside this port.

## Build and run

From the repository root:

```sh
mkdir -p out
nix develop --command jihoo build -O2 compiler/main.jh -o out/jihoo
nix develop --command out/jihoo build experimental/kernel/main.jh -o out/kernel-check
out/kernel-check ../horn/examples/nat.horn ../horn/examples/nat.goals ../horn/examples/nat.proof
nix develop --command out/jihoo run experimental/kernel/comptime.jh
nix develop --command python3 experimental/kernel/check.py
```

The natural-number example reports one goal, three steps and eight distinct
nodes. `comptime.jh` prints `3`: the certificate is checked in a `const`
initializer. An invalid certificate reaches an explicit `trap` during compilation.
Large certificates remain subject to the interpreter's existing step, memory
and recursion limits; this experiment does not raise those limits.

`check.py` requires Python and Rust, and reads upstream Rust sources directly
without modifying the Horn checkout. `--horn PATH` and `--compiler PATH`
select other locations. All binaries, temporary cases and the Rust harness
go under `out/kernel`. A failed case is retained for inspection. The suite
compares acceptance and every successful report field, with explicit expected
verdicts for the security regressions. It covers mismatched assignments,
unused invalid steps, result completeness, sorts, arities, malformed syntax,
bindings, definitions, Unicode whitespace/names, invalid UTF-8, depth limits,
multiple arena rehashes, generated derivations and deterministic mutations.

Validation on 2026-10-27: all 514 differential cases passed (87 accepted,
427 rejected), including compile-time acceptance and rejection checks.
The compiler's full runner passed 1,004 checks, including native/freestanding
programs, negative borrowing cases, backend checks and self-hosting comparisons
on both targets. Stage 1 and stage 2 emitted identical compiler LLVM IR.
Valgrind at `-O0` found no memory errors or leaks in the buffered-input test,
the natural-number example, a 2,200-step/4,400-node proof and a rejected proof.

## jihoo changes made for the port

Two missing capabilities were discussed and approved before proceeding:

1. **Buffered input and Unicode text.** `std.io.BufRead` has memory and file
   readers with `read_line`; `std.utf8` provides strict decoding, validation,
   scalar iteration and Unicode White_Space. This preserves Horn's streaming
   behavior and Unicode token boundaries, including invalid UTF-8 rejection.
2. **Borrow effects for view methods.** A `Checker` holds a `ref Theory`.
   Previously every call on an `inout` view was assumed to store all argument
   loans. Even a method that only pushed integers into a separate vector kept
   that vector borrowed. The borrow kernel now infers argument-to-result and
   argument-to-view-store relations from MIR, with a fixed point for recursion.
   Unknown calls and raw memory effects stay conservative. Both runtime
   checking and compile-time snapshots use the inferred effects. No lifetime
   annotation, raw-pointer replacement for the theory borrow, or cloned theory
   was introduced to bypass that limitation.

## What acceptance means

For a fixed theory and caller-selected ground goals, acceptance is intended
to mean that each goal has a finite derivation by ground instances of the
theory's rules. The producer of the certificate can be untrusted; the theory,
goals, checker, compiler and execution environment are part of the trust base.
The upstream Agda model is not a proof of either the Rust implementation or
this jihoo port. Differential tests are evidence, not a formal refinement proof.

For contracts, a future design must specify jihoo semantics, generate goals
from actual program behavior, and establish the connection between those
goals and the compiled code. Checking a certificate at compile time alone
does not prove an arbitrary jihoo function correct. This experiment leaves
that design open, as requested.
