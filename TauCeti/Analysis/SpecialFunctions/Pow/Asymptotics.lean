/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import TauCeti.Analysis.Asymptotics.Lemmas

/-!
# Power-law asymptotics

## Rescaling power-weighted limits

If `x ^ α * f x` tends to `C` at positive infinity, then `x ^ α * f (c * x)` tends to
`C / c ^ α` for `c > 0`, and a fixed translation of `f` preserves the constant `C`.
For a positive exponent, a finite power-law limit also implies that `f` tends to zero.
These facts transfer power-law tail constants between proportional or translated thresholds.

## Comparison with `exp ‖s‖ ^ b` at infinity

On a seminormed group, as `‖s‖ → ∞`:

* `exp (c * ‖s‖ ^ a)` is `O(exp ‖s‖ ^ b)` whenever `a < b`, for every real `c`;
* every power `‖s‖ ^ n` is `O(exp ‖s‖ ^ b)` whenever `0 < b`.

These are the comparisons behind the order of growth of an entire function.

## Comparing exponents

If `(n + 1) ^ a ≤ C (n + 1) ^ b` for every natural number `n`, then `a ≤ b`: a power with a
larger exponent outgrows every constant multiple of a smaller one.
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

/-- A real function with a finite power-law limit of positive exponent tends to zero. -/
theorem Filter.Tendsto.tendsto_zero_of_rpow_mul {f : ℝ → ℝ} {α C : ℝ}
    (h : Tendsto (fun x : ℝ ↦ x ^ α * f x) atTop (𝓝 C)) (hα : 0 < α) :
    Tendsto f atTop (𝓝 0) := by
  have hlim := h.mul (tendsto_rpow_neg_atTop hα)
  simp only [mul_zero] at hlim
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [Real.rpow_neg hx.le]
  field_simp [(Real.rpow_pos_of_pos hx α).ne']

/-- A fixed translation of a real function preserves its finite power-law constant at infinity,
for any real exponent. -/
theorem Filter.Tendsto.rpow_mul_comp_add {f : ℝ → ℝ} {α C : ℝ}
    (h : Tendsto (fun x : ℝ ↦ x ^ α * f x) atTop (𝓝 C)) (c : ℝ) :
    Tendsto (fun x : ℝ ↦ x ^ α * f (x + c)) atTop (𝓝 C) := by
  have hshift : Tendsto (fun x : ℝ ↦ x + c) atTop atTop :=
    tendsto_atTop_add_const_right atTop c tendsto_id
  have hratio : Tendsto (fun x : ℝ ↦ x / (x + c)) atTop (𝓝 1) := by
    simpa using TauCeti.tendsto_add_div_add_atTop (0 : ℝ) c
  have hlim := (hratio.rpow_const (p := α) (Or.inl one_ne_zero)).mul (h.comp hshift)
  simp only [Real.one_rpow, one_mul] at hlim
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop 0, eventually_gt_atTop (-c)] with x hx hxc
  have hx' : 0 < x + c := by linarith
  simp only [Function.comp_apply]
  rw [Real.div_rpow hx.le hx'.le]
  field_simp [(Real.rpow_pos_of_pos hx' α).ne']

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

/-- If `(n + 1) ^ a ≤ C (n + 1) ^ b` for every natural number `n`, then `a ≤ b`. -/
theorem le_of_forall_rpow_le_mul_rpow {a b C : ℝ}
    (h : ∀ n : ℕ, ((n : ℝ) + 1) ^ a ≤ C * ((n : ℝ) + 1) ^ b) : a ≤ b := by
  by_contra hab
  push Not at hab
  have ht : Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1) ^ (a - b)) atTop atTop :=
    (tendsto_rpow_atTop (sub_pos.2 hab)).comp
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  obtain ⟨n, hn⟩ := (ht.eventually_gt_atTop C).exists
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have := h n
  rw [Real.rpow_sub hpos, lt_div_iff₀ (Real.rpow_pos_of_pos hpos _)] at hn
  linarith

end TauCeti
