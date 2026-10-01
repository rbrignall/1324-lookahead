# Three-step lookahead inequalities — Lean source

This repository contains a Lean formalisation of Proposition 5.3 in "Shuffle automata and 
the growth of 1324-avoiding permutations". It proves that the state weights in Appendix B are
strictly positive, and that the resulting 1536 λ-good inequalities hold.

**Important** This is not a formalisation of the proof that gr(Av(1324)) ≤ 13.167248. 
This repository only verifies the part of the argument that would be 
time-consuming to check by hand.

The central theorem in `ThreeStep/Certificate.lean` is:

```lean
theorem three_step_certificate (t : ℝ) (ht : m t = 0)
    (hlo : (lo : ℝ) < t) (hhi : t < (hi : ℝ)) :
    PositiveWeighting (kappa t) ∧ LambdaGood t (1+t) (kappa t)
```

Here:

- `m(t) = 3t^5 + 10t^4 - t^3 - 11t^2 - 6t - 1`;
- `lo = 1158423/1000000` and `hi = 1158424/1000000`; 
   the theorem assumes `lo < t < hi`. The paper establishes
  that `m(t)` has a unique real root in this interval (see footnote 3).
  `PositiveWeighting κ` means that all 384 weights are strictly positive;
- `LambdaGood t (1+t) κ` is the conjunction, expressed by finite universal
  quantification, of all 384 × 4 local inequalities. The edge costs are
  `1`, `t`, and `t^2`, corresponding to `x = y = 1/t`.


## Build

Uses **Lean 4.24.0 and mathlib v4.24.0**. With `elan`
installed, run from this directory:

```sh
lake exe cache get
bash check.sh
```

`check.sh` regenerates the expected data in memory, checks it against the saved
Lean table, runs `lake build`, and invokes `Audit.lean`. It does not accept any axiom reports
that contain anything other than `propext`, `Classical.choice`, and `Quot.sound`.
The script creates `checks/lean_build_passed.txt` after these commands succeed.

A GitHub Actions workflow is included to perform the same build when these files are placed at the root of a repository. 

## Files

| File | Role |
|---|---|
| `ThreeStep/Arithmetic.lean` | Five rational coefficients, evaluation, one reduction identity, and the elementary termwise lower-bound lemma. |
| `ThreeStep/Data.lean` | Generated dictionary of 139 weight polynomials and the six 8×8 lookup tables. |
| `ThreeStep/Certificate.lean` | State and transition definitions, finite rational checks, and the real inequality theorem. |
| `ThreeStep.lean` | Library entry point. |
| `Audit.lean` | Prints the theorem axiom dependencies and checks the two case-count lemmas. |
| `data/three_step_weights.csv` | Weights for the 384 states, as given in Appendix B. |
| `tools/generate_data.py` | Auxiliary python script to recreate `Data.lean` from the `.csv` file; option `--check` makes no changes but verifies `Data.lean` matches the data in `data/three_step_weights.csv`. Note: this script is not required for the Lean verification process. |



## Correspondence with the paper

`State` is `Fin 6 × Fin 8 × Fin 8`. The six underlying states correspond to set H in the paper, and in order are

```
0: (N,Bo,Ro)   1: (N,Bo,R)   2: (N,B,Ro)
3: (N,B,R)     4: (B,B,Ro)    5: (B,B,R).
```

The first component is the _output history_, and the second and third components are the _last blue letter_  and _last red letter_, respectively.

For each of the lookahead components, the three letters are encoded using a binary index from 0 to 7: 0 for circled letters, 1 for internal letters,
and the first letter (the _head_ of the corresponding input tape) is the leftmost bit. See Appendix B of the accompanying paper for a complete mapping. Thus `head w = w/4`, and revealing a bit `c` after reading the head updates the window to `(2*w+c) mod 8`.
The four newly revealed pairs are `Fin 2 × Fin 2`.

The transitions are defined as follows:

- A blue move sets the output history to `B` if the current blue head is `B` and `N` otherwise, updates the last blue letter, and retains the last red letter; the blue lookahead component is updated to reveal the next letter.
- A red move sets the output history to `N`, retains the last blue letter, updates the last red
  letter, and updates the red lookahead component.
- Red moves are forbidden exactly when the output history is `B` and the current red head is `R`.

`weightIndex` uses zero-based polynomial indices: index `j` is the printed
polynomial `w_(j+1)`. Comments on every polynomial row give its printed name.
The CSV has SHA-256:

```
3526ec0d545c3c5c55b4021de177f257e57f0dd18ffdd3c6e9be53cc0e502887
```

## Finite computational tools for the inequalities

`timesT` maps the coefficients of `p` to those of `t*p`, reduced modulo `m`.
`eval_timesT` proves this is sound at every real root of `m` by a polynomial
identity. Applying it twice accounts for the `t^2` transition cost. Addition and
subtraction of coefficients then construct each inequality from the transition rules.

`lower p` uses the lower interval endpoint for every nonnegative coefficient and
the upper endpoint for every negative coefficient. `lower_le_eval` proves over
`ℝ` that this rational number is a lower bound for `p(t)` throughout the interval.

The private finite theorem `checked` asks Lean to establish that every state-weight
lower bound is positive and every reduced-slack lower bound is nonnegative.
It splits the check into six histories and uses `decide +kernel`. 
The public theorem combines these finite checks with the two
soundness lemmas above. 
