# A checked generated enum codec

This experiment connects metaprogramming, Horn certificates, and a small
executable representation. A generator reflects an actual jihoo enum and
builds encoding/decoding tables. An independent adapter asks the existing
ground Horn kernel to check that decoding an encoded value returns the
original value, for every variant of that enum. Runtime operations use the
checked tables.

The generator supplies the candidate and certificate. It does **not** supply
the accepted theory or choose the verification goal. The adapter constructs
each goal from the complete candidate tables. Attaching a correct proof for
a different, even otherwise correct, pair of tables is rejected.

## Next work and destination

The first [roadmap milestone](../../docs/internals/roadmap.md#1-bring-the-existing-experiments-into-supported-use)
has resolved the four-variant evaluator failure without changing its limits.
An explicit exhaustive-checking API now covers 16, 64 and 256 variants. Both
paths have CI regressions; larger unary certificates still exceed the step
budget. Next replace their repeated serialization/parsing, add explicit stable
wire tags, and migrate the reusable codec into `lib/` with a maintained
example. Stable tags and library migration remain unimplemented.

## Run

From the repository root, with the current self-hosted compiler in `out/jihoo`:

```sh
nix develop --command out/jihoo run experimental/verified-codec/example.jh -I experimental/proofs -I experimental/kernel -- 0
```

```text
Red encodes to 2
Green
round trip: true
```

The input tag is read at runtime. Tags `0`, `1`, and `2` decode to `Green`,
`Amber`, and `Red`; tags outside this range produce `invalid tag`.

The user-facing example is:

```jihoo
#[derive(Eq, Show)]
enum Signal { Red, Amber, Green }

const CODEC = codec.build(Signal, producer.Reverse)
```

`producer.Reverse` builds a reverse-order mapping using `variant_count(T)`.
`codec.build` also uses reflection to check that every variant is payload-free
and to create one proof obligation for every ordinal. `decode` uses
`make_variant` to construct the actual enum value. Adding or removing a
variant changes the generated tables and the verification obligations.

`build` checks during compilation even when called from ordinary runtime code.
Its executable tables are frozen with `comptime`; generation is never deferred
to a runtime call that could produce a different unchecked result.

For a finite codec without certificates, use:

```jihoo
const CODEC = codec.build_exhaustive(Signal, producer.Reverse)
```

This API generates one candidate, checks every table entry and every round
trip, and freezes that exact candidate during the same evaluation. It returns
the same private `Codec(T)` and runtime implementation. The generator needs
only `generate`; evidence is not an input to this API. `codec.build` continues
to require and check certificates, including rejection of stale or unrelated
evidence. Both APIs reject payload enums and invalid tables during compilation,
including when construction is written in runtime code.

## The connection between execution and proof

`program.Plan(N)` is the entire generated program:

```text
encode: N signed machine integers
decode: N signed machine integers
```

The adapter first requires every entry to be in `0..N`. This only validates
the representation. It does not compare the composed tables or establish
their round-trip property.

For an actual enum ordinal `i`, the runtime adapter does:

```text
tag = encode[i]
result ordinal = decode[tag]
```

The fixed theory in `model.jh` describes exactly these two positional lookups.
`at(i, xs, x)` is defined by the head and tail rules of list lookup, with
indices represented as natural numbers. The final rule is:

```text
at(i, encode, tag), at(tag, decode, i) => rt(i, encode, decode)
```

The trusted adapter serializes **both complete tables**, along with the
caller-selected ordinal, into the goal `rt(i, encode, decode)`. The certificate
must derive precisely that goal under the fixed lookup rules. A duplicate
encoding or wrong decoder cannot be hidden by a generator claiming a different
result. Proofs cannot introduce new rules.

The resulting `Codec(T)` has a private plan and no mutating methods. A safe
client cannot replace the tables after checking. Normal jihoo type checking
also keeps values of other enum types from being passed to it.

The checks and construction evaluate the same generator on the same type in
the deterministic compile-time evaluator. Correct compile-time evaluation and
constant persistence are part of the compiler trust assumption. Certificate
production is staged separately from checking, with the existing evaluator
budget applying independently to each invocation.

## Trust and scope

Trusted parts are the ground kernel, the fixed lookup theory, serialization
and range checks in `model.jh`, the adapter in `codec.jh`, and the jihoo
compiler and execution environment. The correspondence between the lookup
rules and the runtime table operations is explicit and small, but has **not**
been formally proved. This is a checked representation with a trusted runtime
adapter, not a verified compiler.

The generator and certificate builder in `producer.jh` are untrusted for
acceptance. The accepted property is round-trip preservation; there is no
separately promised protocol numbering or wire compatibility across enum
declaration changes. Payloads, arbitrary generated function bodies, general
source-level contracts, dependent types, and cubical computation are outside
this example.

The experiment uses the original ground certificate rules, not the schematic
checker or its induction rule. `Theory.from_forms` is a small new entry point
that accepts S-expression trees and runs the same declaration validation as
`Theory.parse`. The fixed theory uses the whole-string parser from
`experimental/proofs/syntax.jh`; proof and goal checking use the ground
kernel's existing reader. No inference rule or interpreter limit changed.

There is no new language syntax, general AST reflection, or macro facility.
Existing type reflection, generic specialization, compile-time execution,
and private fields were sufficient for this example. In this finite domain,
exhaustive compile-time evaluation could also establish the property; Horn
is not necessary for enum codecs. Its role here is to demonstrate how a
producer can supply evidence that a fixed, independent checker validates
against the actual generated representation.

The certificate examples cover one through four variants. The four-variant
case previously exceeded one million steps while checking; ASCII token and
UTF-8 fast paths plus a smaller initial arena now keep every obligation within
that original limit. No inference rule, memory validation or limit was relaxed.

## Scaling measurements

```sh
nix develop --command python3 experimental/verified-codec/scale.py --compiler out/jihoo
```

This compares both APIs for 4, 16, 64 and 256 variants, checks native round
trips for every successful construction, and preserves checking/build time,
Linux per-process peak RSS, diagnostics and evaluator profiles under
`out/codec-scaling`. Each timing is one observation, not a controlled runtime
performance claim. Timed compiler invocations have resource reporting enabled,
so their elapsed time includes profiling and report output. Certificate
production and checking have separate resource
summaries. Larger expected certificate limits are recorded as failures, never
as accepted constructions; unexpected compiler failures fail the command.

In the recorded run, the largest four-variant certificate check took 982,275
steps; its separate proof production took at most 37,023. Exhaustive checking
took 1,759, 6,211, 24,019 and 95,251 steps for 4, 16, 64 and 256 variants.
The unary certificate path still reaches the checking limit at 16 variants
and the production limit at 64 and 256. Its next optimization is a shared
term/certificate representation that removes repeated unary serialization
and parsing while preserving the connection to the exact executable tables.

[Recorded measurements](scaling-results.json) retain the compiler fingerprint,
source hashes, host, timings, memory use and stage resource summaries. The
recorded source tree was modified while preparing this change; the individual
source hashes identify the measured inputs.

## Validation

CI runs this exhaustive and negative-case suite on x86_64 and aarch64 Linux
through `scripts/check-experiments.py`. To run just the codec checks:

```sh
nix develop --command python3 experimental/verified-codec/check.py
```

This requires Python, the current jihoo compiler, and LLVM `opt` from the
development shell. It does not require the sibling Horn checkout. All
generated sources, binaries, diagnostic inputs, LLVM IR, and `report.json`
are written under `out/verified-codec`. `--compiler PATH` selects a compiler.

Validation on 2026-10-28:

- The four-variant certificate regression passes with the original limits.
- Exhaustive construction at 4, 16, 64 and 256 variants passes runtime checks
  for every tag; six malformed/payload/runtime-construction cases are rejected.
- Both checking paths match the independent Python oracle on all 2,187 rows.
- O2 removes the certificate checker from the example and the exhaustive
  checker and constructor from the 256-variant program.
- Compiler report tests cover both targets, unchanged IR, JSON source errors,
  nested obligation context and unchanged step/memory/depth rejections.

Validation on 2026-10-27:

- Seven runtime inputs, including all valid tags and signed integer limits.
- Four positive constructions: one-, two-, and three-variant enums, plus a
  constructor call written in runtime code.
- Thirteen compile-time rejection cases: incorrect tables, invalid indices,
  another correct program's proof, another row's proof, a stale proof after
  adding a variant, missing/invalid evidence, an unused invalid step, payloads,
  and invalid construction written in runtime code.
- Replacing a private checked plan is rejected by the compiler.
- All 2,187 rows across all 729 pairs of three-entry tables matched the
  independent Python condition `decode[encode[i]] == i`: 729 accepted and
  1,458 rejected.
- At O2, LLVM removes the kernel, parsers, model, generator, proof producer,
  and constructor functions from the example while preserving codec behavior.
- An aarch64 object was emitted; it was not run on aarch64.
- After the shared declaration-validator refactor, the existing ground suite
  passed all 514 differential cases and compile-time acceptance/rejection;
  the schematic experiment passed all 701 cases and its four rejection cases.

To inspect one candidate at runtime and export its exact theory, goal and
certificate:

```sh
mkdir -p out/verified-codec
nix develop --command out/jihoo run experimental/verified-codec/inspect.jh -I experimental/kernel -- out/verified-codec 0 2 1 0 2 1 0
```

The arguments after the directory are the selected ordinal, three encoding
entries, and three decoding entries. A rejected candidate still leaves the
inputs available for the standalone Horn checker. `inspect.jh` is a diagnostic
tool; it does not construct a `Codec` from unchecked runtime data.
