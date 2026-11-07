/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Power-law asymptotics

## Rescaling power-weighted limits

If `x ^ α * f x` tends to `C` at positive infinity, then `x ^ α * f (c * x)` tends to
`C / c ^ α` for `c > 0`. This transfers power-law asymptotics between proportional thresholds.

## Comparison with `exp ‖s‖ ^ b` at infinity

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

namespace Real

/-- The Mellin growth scale `(1+r) log (2+r)` is negligible compared with every power above one. -/
theorem isLittleO_add_one_mul_log_add_two_rpow {p : ℝ} (hp : 1 < p) :
    (fun r : ℝ ↦ (1 + r) * log (2 + r)) =o[atTop] fun r ↦ r ^ p := by
  have hlin : (fun r : ℝ ↦ 1 + r) =O[atTop] fun r ↦ r := by
    apply IsBigO.of_bound 2
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith),
      abs_of_nonneg (by linarith)]
    linarith
  have hlog : (fun r : ℝ ↦ log (2 + r)) =O[atTop] log := by
    apply IsBigO.of_bound 2
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with r hr
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (log_nonneg (by linarith)),
      abs_of_nonneg (log_nonneg (by linarith))]
    calc
      log (2 + r) ≤ log (r * r) := log_le_log (by linarith) (by nlinarith)
      _ = 2 * log r := by rw [log_mul (by linarith) (by linarith)]; ring
  refine (hlin.mul_isLittleO (hlog.trans_isLittleO
    (isLittleO_log_rpow_atTop (sub_pos.mpr hp)))).congr' .rfl ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  calc
    r * r ^ (p - 1) = r ^ (1 + (p - 1)) := by rw [rpow_add hr, rpow_one]
    _ = r ^ p := by congr 1; ring
/-- The logarithmic growth scale is stable under nonnegative affine majorants. -/
theorem add_one_mul_log_add_two_le {r t A : ℝ} (hr : 0 ≤ r) (ht : 0 ≤ t)
    (hA : 0 ≤ A) (htA : t ≤ A * (1 + r)) :
    (1 + t) * log (2 + t) ≤ (A + 2) * (2 * (A + 2) + 1) * (1 + r) * log (2 + r) := by
  let M := A + 2
  have hM : 0 < M := by dsimp [M]; positivity
  have hL : (1 / 2 : ℝ) ≤ log (2 + r) := by
    have h2 : (1 / 2 : ℝ) ≤ log 2 := by
      convert one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2) using 1; norm_num
    exact h2.trans (log_le_log (by norm_num) (by linarith))
  have h1 : 1 + t ≤ M * (1 + r) := by dsimp [M]; nlinarith
  have h2 : 2 + t ≤ M * (2 + r) := by dsimp [M]; nlinarith
  have hlog : log (2 + t) ≤ log M + log (2 + r) := by
    rw [← log_mul hM.ne' (by positivity : 2 + r ≠ 0)]
    exact log_le_log (by positivity) h2
  have hlogM : log M ≤ M := (log_le_sub_one_of_pos hM).trans (by linarith)
  have hlog' : log (2 + t) ≤ (2 * M + 1) * log (2 + r) := by
    nlinarith [mul_le_mul_of_nonneg_left hL (by positivity : 0 ≤ 2 * M)]
  calc
    _ ≤ (M * (1 + r)) * ((2 * M + 1) * log (2 + r)) :=
      mul_le_mul h1 hlog' (log_nonneg (by linarith)) (by positivity)
    _ = _ := by dsimp [M]; ring

end Real
