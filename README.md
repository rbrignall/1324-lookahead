# Three-step lookahead certificate — Lean source

**Status: the Lean source has NOT been compiled in this environment.**
There is no local Lean/Lake installation, and network access needed to install it
was unavailable. This is therefore an uncompiled formalisation candidate, not a
completed machine-checked result. The source has no `sorry`, `admit`, added axioms,
or native-evaluation proof steps. The exact data and the arithmetic implemented
in it have been cross-checked with Python, but that does not establish that Lean
will elaborate these proof scripts. In particular, build time and resource use
have not been measured.

## Scope

This is only the finite certificate from the ordinary, two-statistic,
three-letter-lookahead argument. It does not formalise permutation avoidance,
the weighted-transfer proposition, the domino generating function, the growth
bound, or optimality of the parameters. It does not use the witness-depth refinement.

The central theorem in `ThreeStep/Certificate.lean` is:

```lean
theorem three_step_certificate (t : ℝ) (ht : m t = 0)
    (hlo : (lo : ℝ) < t) (hhi : t < (hi : ℝ)) :
    PositiveWeighting (kappa t) ∧ LambdaGood t (1+t) (kappa t)
```

Here:

- `m(t) = 3t^5 + 10t^4 - t^3 - 11t^2 - 6t - 1`;
- `lo = 1158423/1000000` and `hi = 1158424/1000000`, exactly;
- `PositiveWeighting κ` means that all 384 weights are strictly positive;
- `LambdaGood t (1+t) κ` is the conjunction, expressed by finite universal
  quantification, of all 384 × 4 local inequalities. The edge costs are
  `1`, `t`, and `t^2`, corresponding to `x = y = 1/t`.

A separate short theorem, `parameter_exists`, supplies a real root in the open
interval using mathlib's intermediate value theorem. Uniqueness is unnecessary
here: the certificate theorem holds for every real root in that interval.

## Build and inspect

The project targets **Lean 4.24.0 and mathlib v4.24.0**. These are deliberate fixed
release targets, not a claim about the newest available versions. With `elan`
installed, run from this directory:

```sh
lake update
lake exe cache get
bash check.sh
```

`check.sh` regenerates the expected data in memory, checks it against the saved
Lean table, runs `lake build`, and invokes `Audit.lean`. It rejects an axiom report
containing anything other than `propext`, `Classical.choice`, and `Quot.sound`.
In particular, `sorryAx` or a native-computation axiom is not accepted.
The script creates `checks/lean_build_passed.txt` only after these commands succeed;
that file is intentionally absent from this delivery.

After the first successful dependency resolution, retain `lake-manifest.json`
with a release of this project to lock all resolved dependency revisions.
A GitHub Actions workflow is included to perform the same build when these files
are placed at the root of a repository. No repository has been created or CI run
as part of this delivery.

## Small source layout

| File | Role |
|---|---|
| `ThreeStep/Arithmetic.lean` | Five rational coefficients, evaluation, one reduction identity, and the elementary termwise lower-bound lemma. |
| `ThreeStep/Data.lean` | Generated dictionary of 139 weight polynomials and the six 8×8 lookup tables. |
| `ThreeStep/Certificate.lean` | State and transition definitions, finite rational checks, the real inequality theorem, and root existence. |
| `ThreeStep.lean` | Library entry point. |
| `Audit.lean` | Prints the theorem axiom dependencies and checks the two case-count lemmas. |
| `data/three_step_weights.csv` | The unchanged canonical appendix data. |
| `tools/generate_data.py` | Recreates the Lean data file; `--check` makes no changes. |
| `tools/audit_data.py` | An independent exact **Python** data/arithmetic audit, not a Lean checker. |

There are 186 lines of mathematical Lean definitions/proof scripts in Arithmetic
and Certificate combined, and 216 lines in the generated data file, including
comments and blank lines.

## Correspondence with the paper

`State` is `Fin 6 × Fin 8 × Fin 8`. The six histories, in order, are

```
0: (N,Bo,Ro)   1: (N,Bo,R)   2: (N,B,Ro)
3: (N,B,R)     4: (B,B,Ro)    5: (B,B,R).
```

A three-letter window is its binary index from 0 to 7: 0 is circled, 1 is internal,
and the head is the most significant bit. Thus `head w = w/4`, and revealing a bit
`c` after consuming the head updates the window to `(2*w+c) mod 8`.
The four newly revealed pairs are `Fin 2 × Fin 2`.

The transitions are *defined*, not provided in a precomputed list:

- A blue move sets the output history and last blue letter to the current blue
  head, retains the red history, and shifts only the blue window.
- A red move sets output history to `N`, retains the blue history, updates the red
  history, and shifts only the red window.
- The red term is absent exactly when the previous output and current red head
  are both internal (the forbidden `BR` factor).

`weightIndex` uses zero-based polynomial indices: index `j` is the printed
polynomial `w_(j+1)`. Comments on every polynomial row give its printed name.
The CSV is byte-for-byte unchanged, with SHA-256:

```
3526ec0d545c3c5c55b4021de177f257e57f0dd18ffdd3c6e9be53cc0e502887
```

## Why the finite computation implies the real inequalities

`timesT` maps the coefficients of `p` to those of `t*p`, reduced modulo `m`.
`eval_timesT` proves this is sound at every real root of `m` by a polynomial
identity. Applying it twice accounts for the `t^2` transition cost. Addition and
subtraction of coefficients then construct each slack from the transition rules.

`lower p` uses the lower interval endpoint for every nonnegative coefficient and
the upper endpoint for every negative coefficient. `lower_le_eval` proves over
`ℝ` that this rational number is a lower bound for `p(t)` throughout the interval.
No endpoint sampling or floating-point estimates occur.

The private finite theorem `checked` asks Lean to establish that every state-weight
lower bound is positive and every reduced-slack lower bound is nonnegative.
It splits the check into six histories and uses `decide +kernel`, not
`native_decide`. An exactly zero remainder has lower bound exactly zero and needs
no special branch. The public theorem combines these finite checks with the two
soundness lemmas. It does not accept precomputed assertions of the inequalities.

## Checks actually run for this delivery

```sh
python tools/generate_data.py --check
python tools/audit_data.py
```

These exact Python checks passed. The audit reads the literal polynomial and index
tables back from the generated Lean file and reconstructs all 384 weights. It
reconstructs all 1536 transitions and slacks with the numerical state coding,
compares reduction by `timesT` against ordinary polynomial division, and compares
the results against the existing verifier's output:

```
384 positive state-weight lower bounds
1536 nonnegative reduced-slack lower bounds
514 zero slacks, 1022 strictly positive slacks
139 distinct weight polynomials, 258 distinct reduced slacks
```

Results are recorded in `checks/python_arithmetic_audit.json`. The original exact
Python verifier was also rerun, with its output in `checks/python-verification/`.
Neither check is a substitute for the **still outstanding Lean build**.

Until `bash check.sh` completes successfully, the paper should not describe this
artifact as a Lean-verified certificate.
