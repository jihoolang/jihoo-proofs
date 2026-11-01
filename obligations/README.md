# Proving MIR's own checks

The first experiment toward jihoo 0.5's verification
([design](https://github.com/jihoolang/jihoo/blob/main/docs/internals/verification.md)).
jihoo's MIR already states what must hold for a program to run without
trapping: a bounds check is an `assert` terminator, and `+`/`-` check for
overflow in debug builds. This experiment proves those obligations, plus a
function's `requires`/`ensures`, without new syntax and without trusting the
prover:

1. `vc.jh` (trusted: it is the semantics) models MIR's integer part and walks
   each path between the entry, loop heads and returns, collecting linear
   integer facts from assignments and branches. Each check gives a goal:
   *these facts imply that claim*.
2. `fm.jh` (untrusted) is a Fourier–Motzkin prover that remembers how each
   derived fact was made, so a contradiction yields Farkas weights.
3. `linear.jh` (trusted, the checker) adds up the weighted facts and accepts
   only if they cancel to a negative constant. It is 90 lines and finds
   nothing itself.

`models.jh` holds two functions' MIR exactly as `jihoo emit-mir` printed it
(0.4.2, debug build), written in the model by hand. A compiler with
`emit-obligations` (after 0.4.2) prints the model itself: `load.jh` reads
it, and `emitted.jh` verifies the functions that a contracts file names.
Contracts live in such files (`samples/*.contracts`) until jihoo has syntax
for them, and name MIR's local and block numbers.

## Try it

```sh
jihoo test -I obligations obligations/tests.jh       # rejection cases, at runtime
jihoo run -I obligations obligations/example.jh      # everything at compile time
jihoo emit-obligations obligations/samples/bugs.jh > out/bugs.obligations
jihoo run -I obligations -I kernel obligations/emitted.jh -- \
    out/bugs.obligations obligations/samples/bugs.contracts
python3 obligations/check.py                         # all of these, with a report
```

From the compiler's output, `samples/abs.jh` gets the verdicts of the
hand-written models below, and `samples/bugs.jh` shows what must stay
unproved:

```text
last: 5 of 6 obligations proved
  UNPROVED bb4: index-out-of-bounds: no linear proof     (while i <= xs.len)
after_call: 0 of 1 obligations proved                    (x changed by bump(&x))
scale: 3 of 3 obligations proved                         (x * 4 under 0 <= x <= 1000)
```

With a compiler whose evaluator allows 100 million steps (see below), the
example prints:

```text
clamp: 6 of 6 obligations proved
  proved   bb1: ensures (1 facts)
  ...
sum: 8 of 10 obligations proved
  proved   bb1: invariant of bb1 (1 facts)
  proved   bb1: invariant of bb1 (2 facts)
  proved   bb4: index out of bounds (2 facts)
  proved   bb4: index out of bounds (2 facts)
  UNPROVED bb6: no overflow: no linear proof
  UNPROVED bb6: no overflow: no linear proof
  proved   bb6: no overflow (2 facts)
  proved   bb6: no overflow (3 facts)
  proved   bb1: invariant of bb1 (2 facts)
  proved   bb1: invariant of bb1 (2 facts)
```

`clamp` meets `lo <= result <= hi` under `lo <= hi`. In `sum`, with the loop
invariant `0 <= i <= xs.len`, the bounds check and `i + 1` cannot fail, so
both could be removed; `s + xs[i]` really can overflow, and stays unproved.
`tests.jh` checks that changed or negative weights, false claims, a missing
`requires`, an invariant that fails on entry or is not preserved, an
off-by-one loop condition and a loop without an invariant are all rejected.

## Findings

| | 0.4.2 limit | measured |
| --- | ---: | ---: |
| `clamp` (6 obligations) | 1,000,000 steps | 1,353,493 steps |
| `sum` (10 obligations) | 1,000,000 steps | 3,957,480 steps |

- **The evaluator's budget is the bottleneck.** Neither function fits the
  1,000,000-step limit of one compile-time evaluation. About 60% of the steps
  are `std` code (a `Vec(i128)` push costs about 46 steps), the rest split
  between the checker (`linear`) and the prover (`fm`). The measurement used a
  compiler built from 0.4.2 with `MAX_STEPS` raised to 100 million; the
  wall-clock time of the whole build was 0.65 s.
- **The verifier is erased.** An `-O2` build of the example is 16 KB and has
  no symbol from `fm`, `linear`, `vc` or `verify`; unoptimized IR still
  defines them as dead internal functions.
- **Linear arithmetic covers the checks MIR inserts today**: bounds checks
  under a loop invariant and overflow of counters. A sum of unknown elements
  needs a contract on the input, which is the expected result.
- **The generator is the trust question.** It decides what MIR means (paths,
  `switch` on bools, the reading of `a as u64 < b as u64` as `0 <= a < b`
  when `b` is a length, fresh variables for loads). A wrong rule there proves
  false things, which the checker cannot see.

- **MIR's `unreachable` is trusted.** A path that reaches it ends there,
  as LLVM assumes; reporting the function incomplete instead made 53
  checks unprovable.
- **An opaque operand of `+ - *` is a variable.** MIR gives both operands
  the result's type, so `x.n + 1` with `x.n` opaque still states its
  overflow check, over a value in the field's range.
- **A function is followed everywhere or not at all.** A path that comes
  back to a block it ran, without a loop head with an invariant between,
  stops with an error, and at most 2,000 paths are followed per function
  (sequential branches double them). A function with an error proves
  nothing: a check proved on the paths seen may fail on another.
- **Numbers are bounded.** The checker computes in i128 and accepts only
  facts whose numbers are below 2^65, weights below 2^50 and at most 2,047
  facts, so no product or sum it forms can overflow; past those bounds it
  rejects, which loses a proof. Ranges and constants beyond 64 bits are
  not followed.
- **Casts carry the bounds check.** MIR checks `xs[i]` as
  `i as u64 < xs.len as u64`. The model reads an `i64` cast to `u64` as its
  value modulo 2^64, and `x as u64 < y` as `0 <= x < y` only when `y` is
  known to lie in `[0, 2^63)`; a slice length is, as a view's invariant.

## Testing the generator against the interpreter

The generator is trusted, so `differential.py` tests it against the
compiler's interpreter, which executes the same MIR. Every check in
`emit-obligations` output ends with `(at lo hi)`, the span at which
compile-time evaluation reports it failing. For each function with integer
and `[i64]` parameters, the script makes random inputs (often at a
boundary of the type or of the contract's constants) that meet its
`requires`, evaluates each as a `const` with `jihoo check`, and classifies
what fails:

```sh
python3 obligations/differential.py --compiler jihoo obligations/samples/ints.jh
python3 obligations/differential.py --compiler jihoo obligations/samples/bugs.jh --release
```

```text
ints.jh: 100 probes, 85 passed, 15 unproved check failed
bugs.jh: 60 probes, 39 passed, 20 unproved check failed, 1 ensures failed
```

A failing check the generator proved, or a failing `ensures` it proved, is
a soundness bug: the script prints it and exits with 3. `check.py` runs the
three samples in debug and `--release` builds, then makes the model wrong
on purpose with `--mutate` (reading `i <= xs.len` as `i < xs.len`;
forgetting that `bump(&x)` changes `x`) and requires the bug to be found:

```text
BUG after_call(10,): compile-time evaluation reached a trap at bytes 2817..2823 (ensures was proved)
```

`corpus.py` does the same for real programs: every function of every
file in a jihoo checkout's `tests/run` and `examples` is loaded and
verified without contracts, and `differential.py` runs on each file.
`check.py --corpus ../jihoo` includes it, with inferred invariants. Over
the 98 files of jihoo 0.4.2:

```text
                     364 functions, 317 checks, 270 probes, 0 bugs
without --infer      25 checks proved
with --infer         69 checks proved
```

Most checks are in loops, and a loop without an invariant proves nothing
(see below); inference supplies the simple ones. Every unproved check
says why (`check NAME LO HI unproved WHY` in `--machine` output): where
the values its claim depends on come from, `argument`, `loop` (only the
invariant is known at a loop head), `call`, or the reason
`emit-obligations` gave for an opaque value, such as `load` or `field`;
or `incomplete:paths` when the function was not followed everywhere.
`corpus.py` tallies them (`unproved_because` in its report). With
inference, the largest groups are `load` (about 80, alone or with
others), `loop` (about 70), `call` (about 35), checks the model cannot
state (30) and `argument` (13): contracts on calls and on memory, not
more arithmetic, are what would prove more. The 37 failures outside the model are
the interpreter's limits (printing, statics, intrinsics, call depth), not
checks the model missed. The first runs found three bugs in the tools, none
in what they proved: `emit-obligations` overflowed computing `i128`'s range;
the verifier overflowed on 128-bit ranges; and it followed loops without
invariants by unrolling them, so a few branches in a loop took 30 GB.

Random inputs find a wrong rule only on inputs that reach it: a model that
believed slices hold at most 1,000 elements would pass, since the probes'
slices are short.

## Inferring loop invariants

`infer.jh` proposes invariants for the loop heads that have none (the
targets of back edges), Houdini-style: for each integer that a loop
counts with (assigned in two blocks or more) it proposes `0 <= v`, and
`v <= w` and `w <= v` for every other counter and every value the
function never assigns (arguments, lengths). All of them are assumed at
once; each one that is not proved on entry or after an iteration is
dropped, until the rest are. `emitted.jh --infer`, `differential.py
--infer` and `corpus.py --infer` use it. It is untrusted: `verify` checks
the invariants it returns like written ones, and `tests.jh` checks that
an off-by-one loop stays unproved with inference. For `sum` without its
written invariant, it finds `0 <= i <= xs.len`.

## Next

- Loop invariants written in the source, then inferred by an untrusted pass
  that proposes candidates (`0 <= i`, `i <= n`) and keeps those that check.
- Calls through contracts: `Vec.index` requires `0 <= i < self.len()`.
