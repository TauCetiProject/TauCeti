/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import Mathlib.Basic.ENNReal.Operations
import Mathlib.Basic.ENNReal.Inv

/-!
# Bounds by products in `ℝ≥0∞`

A bound `L ≤ a * b` in `ℝ≥0∞` holds trivially when one factor is infinite and none vanishes.
So when `L` vanishes whenever a factor does, it suffices to prove the bound for finite factors.
This is the shape of estimates such as `‖B(f, g)‖ ≤ C ‖B‖ ‖f‖ ‖g‖` with extended norms.

## Main declarations

* `ENNReal.le_mul_of_ne_top_imp_le`: the reduction of `L ≤ a * b` to finite `a` and `b`.
* `ENNReal.le_mul_mul_of_ne_top_imp_le`: the reduction of `L ≤ c * a * b` to finite `c`, `a`
  and `b`.
* `ENNReal.mul_mul_pow_le_mul_div_pow_mul`: a coefficient bound absorbs division by a finite
  positive factor in a natural power.
* `ENNReal.eq_zero_of_forall_le_mul`: a quantity bounded by a fixed finite multiple of every
  positive `ε` vanishes.

## References

* https://github.com/frenzymath/lean-eval-submissions
* https://github.com/frenzymath/PoincareConjecture
-/

public section

open scoped ENNReal NNReal

namespace ENNReal

/-- To bound `L` by `a * b`, it suffices to treat finite `a` and `b`, provided `L` vanishes when
`a` or `b` does: otherwise the right side is infinite. -/
theorem le_mul_of_ne_top_imp_le {L a b : ℝ≥0∞} (ha : a = 0 → L = 0) (hb : b = 0 → L = 0)
    (hfin : a ≠ ∞ → b ≠ ∞ → L ≤ a * b) : L ≤ a * b := by
  by_cases ha0 : a = 0
  · exact (ha ha0).le.trans zero_le
  by_cases hb0 : b = 0
  · exact (hb hb0).le.trans zero_le
  by_cases hat : a = ∞
  · rw [hat, top_mul hb0]
    exact le_top
  by_cases hbt : b = ∞
  · rw [hbt, mul_top ha0]
    exact le_top
  exact hfin hat hbt

/-- To bound `L` by `c * a * b`, it suffices to treat finite `c`, `a` and `b`, provided `L`
vanishes when `c`, `a` or `b` does: otherwise the right side is infinite. -/
theorem le_mul_mul_of_ne_top_imp_le {L c a b : ℝ≥0∞} (hc : c = 0 → L = 0) (ha : a = 0 → L = 0)
    (hb : b = 0 → L = 0) (hfin : c ≠ ∞ → a ≠ ∞ → b ≠ ∞ → L ≤ c * a * b) : L ≤ c * a * b := by
  refine le_mul_of_ne_top_imp_le (fun h => (mul_eq_zero.1 h).elim hc ha) hb fun hca hbt => ?_
  by_cases ha0 : a = 0
  · exact (ha ha0).le.trans zero_le
  by_cases hc0 : c = 0
  · exact (hc hc0).le.trans zero_le
  exact hfin (fun h => hca (by rw [h, top_mul ha0])) (fun h => hca (by rw [h, mul_top hc0])) hbt

/-- If `c * C ^ n ≤ a`, dividing the power's base by a finite positive `C` absorbs the
coefficient `c` into `a`, even when the base or an additional factor is infinite. -/
theorem mul_mul_pow_le_mul_div_pow_mul (V : ℝ≥0∞) {c a r : ℝ≥0∞} {C : ℝ≥0} {n : ℕ}
    (hC : C ≠ 0) (hca : c * (C : ℝ≥0∞) ^ n ≤ a) :
    c * V * r ^ n ≤ a * ((r / (C : ℝ≥0∞)) ^ n * V) := by
  have hcancel : (C : ℝ≥0∞) ^ n * (r / (C : ℝ≥0∞)) ^ n = r ^ n := by
    rw [← mul_pow, ENNReal.mul_div_cancel (coe_ne_zero.2 hC) coe_ne_top]
  calc
    c * V * r ^ n = c * ((C : ℝ≥0∞) ^ n * (r / (C : ℝ≥0∞)) ^ n) * V := by
      rw [hcancel]
      ac_rfl
    _ = (c * (C : ℝ≥0∞) ^ n) * ((r / (C : ℝ≥0∞)) ^ n * V) := by ac_rfl
    _ ≤ _ := mul_le_mul_left hca _

/-- If `x ≤ C * ε` for every nonzero `ε` and a finite constant `C`, then `x = 0`. -/
theorem eq_zero_of_forall_le_mul {x C : ℝ≥0∞} (hC : C ≠ ∞) (h : ∀ ε ≠ 0, x ≤ C * ε) :
    x = 0 := by
  refine le_antisymm (le_of_forall_pos_le_add fun δ hδ _ ↦ ?_) zero_le
  rw [zero_add]
  rcases eq_or_ne C 0 with rfl | hC0
  · exact (h 1 one_ne_zero).trans (by rw [zero_mul]; exact zero_le)
  · calc x ≤ C * (δ / C) := h _ (ENNReal.div_ne_zero.2 ⟨by exact_mod_cast hδ.ne', hC⟩)
      _ = δ := ENNReal.mul_div_cancel hC0 hC

end ENNReal
