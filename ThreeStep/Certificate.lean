import ThreeStep.Data
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Omega

set_option autoImplicit false

/-! The ordinary three-letter-lookahead certificate.
The six histories are (N,Bo,Ro), (N,Bo,R), (N,B,Ro), (N,B,R), (B,B,Ro), (B,B,R).
A bit is 0 for circled and 1 for internal. 
First letter on the tape is the most significant bit.
All finite checks below use kernel reduction. -/
namespace ThreeStep

abbrev Bit := Fin 2
abbrev Window := Fin 8
abbrev State := Fin 6 × Window × Window

set_option maxRecDepth 100000 in
lemma number_of_states : Fintype.card State = 384 := by decide
set_option maxRecDepth 100000 in
lemma number_of_local_cases : Fintype.card (State × Bit × Bit) = 1536 := by decide

def head (w : Window) : Bit := ⟨w.val / 4, by omega⟩
def shift (w : Window) (c : Bit) : Window :=
  ⟨(2*w.val + c.val) % 8, Nat.mod_lt _ (by decide)⟩
def previousBlue (h : Fin 6) : Bit := if h.val < 2 then 0 else 1
def previousRed (h : Fin 6) : Bit := ⟨h.val % 2, Nat.mod_lt _ (by decide)⟩
def redAllowed (q : State) : Bool := decide (q.1.val < 4 ∨ head q.2.2 = 0)

/-- Write the blue head, then reveal `c`. -/
def blueNext (q : State) (c : Bit) : State :=
  (⟨4*(head q.2.1).val + (previousRed q.1).val, by
      have hu := (head q.2.1).isLt
      have hr := (previousRed q.1).isLt
      omega⟩,
   shift q.2.1 c, q.2.2)

/-- Write the red head, then reveal `c`; used only when `redAllowed q`. -/
def redNext (q : State) (c : Bit) : State :=
  (⟨2*(previousBlue q.1).val + (head q.2.2).val, by
      have hb := (previousBlue q.1).isLt
      have hl := (head q.2.2).isLt
      omega⟩,
   q.2.1, shift q.2.2 c)

/-- These are precisely the appendix's coefficients. -/
def weight (q : State) : Coeffs :=
  weightPolynomials (weightIndex q.1 q.2.1 q.2.2)
noncomputable def kappa (t : ℝ) (q : State) : ℝ := eval (weight q) t

/-- At x=y=1/t: circled letters cost 1, continuations t, and run starts t². -/
noncomputable def cost (t : ℝ) (previous current : Bit) : ℝ :=
  if current = 0 then 1 else if previous = 0 then t^2 else t

def charge (previous current : Bit) (p : Coeffs) : Coeffs :=
  if current = 0 then p else if previous = 0 then timesT (timesT p) else timesT p

lemma eval_charge {t : ℝ} (ht : m t = 0) (previous current : Bit) (p : Coeffs) :
    eval (charge previous current p) t = cost t previous current * eval p t := by
  by_cases hc : current = 0
  · simp [charge, cost, hc]
  · by_cases hp : previous = 0
    · simp [charge, cost, hc, hp, eval_timesT ht, pow_two, mul_assoc]
    · simp [charge, cost, hc, hp, eval_timesT ht]

noncomputable def outgoing (t : ℝ) (κ : State → ℝ) (q : State) (b r : Bit) : ℝ :=
  cost t (previousBlue q.1) (head q.2.1) * κ (blueNext q b) +
  if redAllowed q then cost t (previousRed q.1) (head q.2.2) * κ (redNext q r) else 0

def PositiveWeighting (κ : State → ℝ) : Prop := ∀ q, 0 < κ q

def LambdaGood (t lambda : ℝ) (κ : State → ℝ) : Prop :=
  ∀ (q : State) (b r : Bit), outgoing t κ q b r ≤ lambda * κ q

/-- Reduced coefficients of (1+t)κ(q) minus the outgoing weighted sum.
Successors and exponents are computed from the transition rules, not supplied as data. -/
def slack (q : State) (b r : Bit) : Coeffs :=
  weight q + timesT (weight q) -
  charge (previousBlue q.1) (head q.2.1) (weight (blueNext q b)) -
  if redAllowed q then
    charge (previousRed q.1) (head q.2.2) (weight (redNext q r)) else 0

lemma eval_slack {t : ℝ} (ht : m t = 0) (q : State) (b r : Bit) :
    eval (slack q b r) t = (1+t) * kappa t q - outgoing t (kappa t) q b r := by
  unfold slack outgoing kappa
  split_ifs <;> simp [eval_timesT ht, eval_charge ht] <;> ring

-- Split by history to keep each closed kernel computation small.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checked (h : Fin 6) :
    (∀ U L : Window, 0 < lower (weight (h,U,L))) ∧
    (∀ (U L : Window) (b r : Bit), 0 ≤ lower (slack (h,U,L) b r)) := by
  fin_cases h <;> decide +kernel

/-- Assertion needed by the paper: 384 positive weights and
all 1536 local λ-good inequalities. -/
theorem three_step_certificate (t : ℝ) (ht : m t = 0)
    (hlo : (lo : ℝ) < t) (hhi : t < (hi : ℝ)) :
    PositiveWeighting (kappa t) ∧ LambdaGood t (1+t) (kappa t) := by
  constructor
  · intro q
    have hp : (0 : ℝ) < (lower (weight q) : ℝ) := by
      exact_mod_cast (checked q.1).1 q.2.1 q.2.2
    exact hp.trans_le (lower_le_eval (weight q) hlo.le hhi.le)
  · intro q b r
    have hp : (0 : ℝ) ≤ (lower (slack q b r) : ℝ) := by
      exact_mod_cast (checked q.1).2 q.2.1 q.2.2 b r
    have hs := hp.trans (lower_le_eval (slack q b r) hlo.le hhi.le)
    rw [eval_slack ht] at hs
    exact sub_nonneg.mp hs

end ThreeStep
