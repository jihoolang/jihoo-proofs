# jihoo-proofs

Compile-time proof checking for [jihoo](https://github.com/jihoolang/jihoo):
certificates and general theorems checked by ordinary jihoo code during
compile-time evaluation, and executable data bound to that evidence.

These are experiments. They moved here from the compiler's repository
(`experimental/`, with their history) so that the language's stable releases
do not carry unsupported prototypes. Nothing here is part of jihoo's standard
library or its compatibility promises.

| Directory | Contents |
| --- | --- |
| [`kernel`](kernel/README.md) | a jihoo port of Horn's trusted ground certificate checker, run at runtime and at compile time |
| [`proofs`](proofs/README.md) | general theorems by structural induction and derivation reuse, checked at compile time |
| [`verified-codec`](verified-codec/README.md) | generated enum codecs with compile-time certificates bound to the executable tables |

## Use

Everything comes from `flake.nix`: the jihoo compiler pinned in `flake.lock`,
LLVM's `opt` and Python. From the repository root:

```sh
nix develop --command jihoo run proofs/example.jh -I kernel
nix develop --command jihoo run verified-codec/example.jh -I proofs -I kernel -- 0
nix develop --command python3 scripts/check.py           # all local regressions
nix develop --command python3 scripts/check.py --compiler ../jihoo/out/jihoo
```

`scripts/check.py` runs the local ground, schematic and codec suites with
independent expected verdicts, without Horn or Rust. Its report is
`out/report.json`; each suite keeps its own report, generated sources and
failing inputs under `out/`. CI runs it on x86_64 and aarch64 Linux.

Cases without an independent expected verdict, such as randomized certificate
mutations, are compared with a pinned Horn checkout:

```sh
nix develop .#differential --command python3 scripts/check.py --horn ../horn
```

The differential shell adds Rust and Cargo. The scripts require the pinned
Horn commit and unmodified reference sources. The Test workflow runs this job
when started by hand with `horn_differential`.

To test against a newer compiler, run `nix flake update jihoo`.

## Roadmap

The goal is reusable libraries with documented imports, separate
ground/schematic trust boundaries, and examples that work with the packaged
compiler, without `-I` paths into this repository. Work in this order:

1. **Codec scaling.** The unary/text certificate path reaches the evaluator's
   step limit during checking at 16 variants, and during production at 64
   and 256 (`codec.build_exhaustive` covers those sizes). Replace repeated
   unary serialization and parsing with a shared representation, guided by
   `verified-codec/scale.py` and `jihoo build --comptime-report`. Raising the
   evaluator limit alone does not complete this.
2. **Stable wire tags.** Explicit tags, with tests for declaration
   reordering, duplicate tags and unknown tags. Keep the checked tables
   immutable and reject invalid, stale or unrelated evidence.
3. **An executable proof consumer.** Use a finite state-transition table as
   the second checked representation; generate its theory and goals from
   the exact table used at runtime, and prove a safety invariant for every
   reachable state with induction and derivation reuse. State the
   correspondence between runtime transitions and proof-domain steps,
   including bounds and integer behavior, and reject changed transitions,
   missing cases, invalid induction assumptions and evidence for another
   table.
4. **Libraries.** Turn the kernel, proof development and codec into
   importable libraries with a CLI example, and decide which, if any,
   belong in jihoo's standard library.

Translating jihoo functions into theories, and source-level contracts, need
an explicit semantics; step 3 is the first bounded model toward that.

## License

Apache-2.0, like jihoo and Horn.
