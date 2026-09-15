import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormCast
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-! Elementary arithmetic for the certificate. 
Note: `t` is real and belongs to the interval (hi,lo). -/
namespace ThreeStep

abbrev Coeffs := Fin 5 → ℚ

def lo : ℚ := 1158423 / 1000000
def hi : ℚ := 1158424 / 1000000
noncomputable def m (t : ℝ) : ℝ :=
  3*t^5 + 10*t^4 - t^3 - 11*t^2 - 6*t - 1

noncomputable def eval (p : Coeffs) (t : ℝ) : ℝ :=
  ∑ i : Fin 5, (p i : ℝ) * t^i.val

@[simp] lemma eval_zero (t : ℝ) : eval 0 t = 0 := by simp [eval]
@[simp] lemma eval_add (p q : Coeffs) (t : ℝ) :
    eval (p + q) t = eval p t + eval q t := by
  simp [eval, add_mul, Finset.sum_add_distrib]
@[simp] lemma eval_sub (p q : Coeffs) (t : ℝ) :
    eval (p - q) t = eval p t - eval q t := by
  simp [eval, sub_mul, Finset.sum_sub_distrib]

/-- Multiplication by `t`, reduced using `3t⁵ = -10t⁴+t³+11t²+6t+1`. -/
def timesT (p : Coeffs) : Coeffs :=
  ![p 4 / 3, p 0 + 2*p 4, p 1 + 11*p 4/3,
    p 2 + p 4/3, p 3 - 10*p 4/3]

lemma eval_timesT {t : ℝ} (ht : m t = 0) (p : Coeffs) :
    eval (timesT p) t = t * eval p t := by
  have h3 : (Fin.succ 2 : Fin 5) = 3 := by decide
  have h4 : (Fin.succ (Fin.succ 2) : Fin 5) = 4 := by decide
  calc
    eval (timesT p) t = t * eval p t - (p 4 : ℝ)/3 * m t := by
      norm_num [eval, timesT, Fin.sum_univ_succ, h3, h4, m]; ring
    _ = t * eval p t := by rw [ht]; ring

/-- A termwise lower bound, as specified in the proof of Proposition 4.3. -/
def lower (p : Coeffs) : ℚ :=
  ∑ i : Fin 5, p i * (if 0 ≤ p i then lo else hi)^i.val

lemma lower_le_eval (p : Coeffs) {t : ℝ}
    (ha : (lo : ℝ) ≤ t) (hb : t ≤ (hi : ℝ)) :
    (lower p : ℝ) ≤ eval p t := by
  have h0 : (0 : ℝ) ≤ (lo : ℝ) := by norm_num [lo]
  have ht0 : 0 ≤ t := h0.trans ha
  simp only [lower, eval, Rat.cast_sum, Rat.cast_mul, Rat.cast_pow]
  apply Finset.sum_le_sum
  intro i _
  by_cases hc : 0 ≤ p i
  · simp only [if_pos hc]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 ha i.val)
      (by exact_mod_cast hc)
  · simp only [if_neg hc]
    exact mul_le_mul_of_nonpos_left (pow_le_pow_left₀ ht0 hb i.val)
      (by exact_mod_cast (le_of_lt (lt_of_not_ge hc)))

end ThreeStep
