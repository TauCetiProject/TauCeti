/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex, The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Power asymptotics: rescaling and comparison with `exp ‖s‖ ^ b`

If `x ^ α * f x` tends to `C` at positive infinity, then `x ^ α * f (c * x)` tends to
`C / c ^ α` for `c > 0`. This transfers power-law asymptotics between proportional thresholds.

On a seminormed group, as `‖s‖ → ∞`:

* `exp (c * ‖s‖ ^ a)` is `O(exp ‖s‖ ^ b)` whenever `a < b`, for every real `c`;
* every power `‖s‖ ^ n` is `O(exp ‖s‖ ^ b)` whenever `0 < b`.

These are the comparisons behind the order of growth of an entire function.
-/

public section

open Filter Real
open scoped Topology

/-- Rescaling the argument by a positive constant divides a power-weighted limit by the
corresponding power of that constant. The exponent may be any real number. -/
theorem Filter.Tendsto.rpow_mul_comp_const_mul {f : ℝ → ℝ} {α C c : ℝ}
    (hf : Tendsto (fun x : ℝ ↦ x ^ α * f x) atTop (𝓝 C)) (hc : 0 < c) :
    Tendsto (fun x : ℝ ↦ x ^ α * f (c * x)) atTop (𝓝 (C / c ^ α)) := by
  have ht := hf.comp (tendsto_id.const_mul_atTop hc)
  apply (ht.div_const (c ^ α)).congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  dsimp only [Function.comp_apply, id_eq]
  rw [mul_rpow hc.le hx]
  field_simp [(rpow_pos_of_pos hc α).ne']

section ExpComparison

open Asymptotics Bornology

namespace TauCeti

variable {E : Type*} [SeminormedAddCommGroup E]

/-- For `a < b` and any real `c`, `exp (c * ‖s‖ ^ a)` is `O(exp ‖s‖ ^ b)` as `‖s‖ → ∞`. -/
theorem isBigO_exp_mul_norm_rpow (c : ℝ) {a b : ℝ} (hab : a < b) :
    (fun s : E ↦ Real.exp (c * ‖s‖ ^ a)) =O[cobounded E] fun s ↦ Real.exp (‖s‖ ^ b) := by
  have h : ∀ᶠ x : ℝ in atTop, c * x ^ a ≤ x ^ b := by
    filter_upwards [(tendsto_rpow_atTop (sub_pos.2 hab)).eventually_ge_atTop c,
      eventually_gt_atTop 0] with x hx hx0
    calc c * x ^ a ≤ x ^ (b - a) * x ^ a :=
          mul_le_mul_of_nonneg_right hx (Real.rpow_nonneg hx0.le _)
      _ = x ^ b := by rw [← Real.rpow_add hx0, sub_add_cancel]
  refine Real.isBigO_exp_comp_exp_comp.2 (isBoundedUnder_of_eventually_le (a := 0) ?_)
  filter_upwards [tendsto_norm_cobounded_atTop.eventually h] with s hs
  simpa using hs

/-- For `b > 0`, every power `‖s‖ ^ n` is `O(exp ‖s‖ ^ b)` as `‖s‖ → ∞`. -/
theorem isBigO_norm_pow_exp_norm_rpow (n : ℕ) {b : ℝ} (hb : 0 < b) :
    (fun s : E ↦ ‖s‖ ^ n) =O[cobounded E] fun s ↦ Real.exp (‖s‖ ^ b) := by
  have h : (fun x : ℝ ↦ x ^ n) =O[atTop] fun x ↦ Real.exp (x ^ b) := by
    refine ((isLittleO_rpow_exp_atTop (n / b)).comp_tendsto
      (tendsto_rpow_atTop hb)).isBigO.congr' ?_ .rfl
    filter_upwards [eventually_ge_atTop 0] with x hx
    rw [Function.comp_apply, ← Real.rpow_mul hx, mul_div_cancel₀ _ hb.ne', Real.rpow_natCast]
  exact h.comp_tendsto tendsto_norm_cobounded_atTop

end TauCeti

end ExpComparison
