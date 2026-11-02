# Proving MIR's own checks

The first experiment toward jihoo 0.5's verification
([design](https://github.com/jihoolang/jihoo/blob/main/docs/internals/verification.md)).
jihoo's MIR already states what must hold for a program to run without
trapping: a bounds check is an `assert` terminator, and `+`/`-` check for
overflow in debug builds. This experiment proves those obligations, plus the
[contracts](https://github.com/jihoolang/jihoo/blob/main/docs/language/contracts.md)
the source states (`requires`, `ensures`, loop `invariant`s), without
trusting the prover:

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
`emit-obligations` (after 0.4.2) prints the model itself, and one with
contracts (after 0.4.2 too) prints each function's contract with it, over
MIR's locals: `load.jh` reads both, and `emitted.jh` verifies the program's
functions. A call to a function with a contract proves its `requires` and
assumes its `ensures`.

## Try it

```sh
jihoo test -I obligations obligations/tests.jh       # rejection cases, at runtime
jihoo run -I obligations obligations/example.jh      # everything at compile time
jihoo emit-obligations obligations/samples/bugs.jh > out/bugs.obligations
jihoo run -I obligations -I kernel obligations/emitted.jh -- out/bugs.obligations
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

`samples/calls.jh` proves through calls: `bump(inout x)` promises
`x == old(x) + 1` under `x < 100`, and `inc(x)` promises `result == x + 1`:

```text
after_bump: 3 of 3 obligations proved     (bump's requires; result == n + 1)
unchecked_bump: 0 of 1 obligations proved
  UNPROVED bb0: requires of main.bump.1: no linear proof   (n may be 100)
twice: 6 of 6 obligations proved          (inc(x) + inc(x) cannot overflow)
count: 13 of 13 obligations proved        (a loop of inc, invariant c == i)
down: 8 of 8 obligations proved           (recursion assumes its ensures)
```

A local lent to one call (`bump(&x)`) stays a variable, which the call
gives a new value, and the integer an `inout` parameter points to is a
variable when the pointer only reaches it. At a loop head, a variable the
function never assigns keeps its value on entry, so the facts `requires`
states of such variables still hold there.

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
a soundness bug: the script prints it and exits with 3. Proofs are modular,
so a failure in a function whose proof assumed a contract that is not
proved (a callee's `ensures`, or its own `requires` where some call left
it unproved, and so on along the calls) is counted as `failed under an
unproved contract` instead. `check.py` runs the
three samples in debug and `--release` builds, then makes the model wrong
on purpose with `--mutate` (reading `i <= xs.len` as `i < xs.len`;
forgetting that `bump(&x)` changes `x`; a call that forgets its callee, so
its `requires` is never proved) and requires the bug to be found:

```text
BUG after_call(10,): compile-time evaluation reached a trap at bytes 2817..2823 (ensures was proved)
```

`corpus.py` does the same for real programs: every function of every
file in a jihoo checkout's `tests/run` and `examples` is loaded and
verified with the contracts its source states (almost none), and
`differential.py` runs on each file.
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

The compiler now has its own verifier
([`jihoo verify`](https://github.com/jihoolang/jihoo/blob/main/docs/reference/command-line.md#verification)),
built from this experiment, which removes the checks it proves.
`--verdicts compiler` makes `differential.py` and `corpus.py` test its
verdicts (`jihoo verify --machine`) instead of `emitted.jh`'s; they are not
modular, since the compiler already counts a proof that rests on an
unproved contract as unproved. Over the samples and the corpus it finds no
bug:

```sh
python3 obligations/differential.py --compiler jihoo obligations/samples/calls.jh --verdicts compiler
python3 obligations/corpus.py --compiler jihoo --checkout ../jihoo --infer --verdicts compiler
```

`check.py` runs the compiler's verdicts on every sample, in debug and
`--release` builds, when the compiler has `verify --machine`, so CI tests
the compiler's generator against the interpreter on x86_64 and aarch64.
Since the compiler makes an unproved contract an error, `verify` exits
with status 1 on the samples that have one on purpose, after its
verdicts. The model's newer parts (the type invariants a call assumes and
a writer proves, `add-wrap` and `sub-wrap`) are read and left out by
`emitted.jh`, which loses proofs only.

Random inputs find a wrong rule only on inputs that reach it: a model that
believed slices hold at most 1,000 elements would pass, since the probes'
slices are short.

The compiler also follows integer fields of locals and borrowed
parameters, counts a call that never returns (`panic`) as a check, and
proves a small callee's panic away at each call (`v[i]` calling
`Vec.index`). A panic fails at compile time with the callee's message, so
`differential.py` reads the calls that led there from the diagnostic's
notes: the call to the function that never returns is that check, and
the call into the function that panicked is the caller's. `samples/fields.jh`
has a struct changed through `inout` methods with contracts over its
field, a call that proves `at`'s panic away and one that cannot, and a
`!=` it cannot rule out. A compiler changed to prove every such call is
caught there. `load.jh` reads the new parts of the model (`fields`, and a
call's `changes`, `fields` and `never`); this experiment gives the
variables in `changes` new values and otherwise ignores them, which only
loses proofs.

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

- Contracts for `std` (`Vec.index` requires `0 <= i < self.len()`), which
  need clauses over `Vec` lengths and fields.
- `||` and `!=` in clauses and conditions: case splits.
- The checker in the compiler, so that an unproved contract is an error.
