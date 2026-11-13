/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import TauCeti.Analysis.Asymptotics.Lemmas
public import TauCeti.Analysis.SpecialFunctions.Log.TwoAdd

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

## Positive powers near zero

As `h → 0⁺`, every multiple `A * h ^ θ` of a positive power falls below any positive constant.
This is how polynomial rates in a small scale `h` become inequalities for all small `h`.

## Families bounded by integer powers

A family whose norms are bounded by `r ^ g a`, with `1 < r` and integer exponents `g a → -∞`,
tends to zero. This is how valuation bounds on coefficients give convergence of series.

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

/-- Near `0⁺`, a positive power of `h` with any coefficient is below any positive constant. -/
theorem eventually_mul_rpow_lt_nhdsGT_zero {θ : ℝ} (hθ : 0 < θ) (A : ℝ) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ h in 𝓝[>] (0 : ℝ), A * h ^ θ < c := by
  have ht := (Real.continuousAt_rpow_const 0 θ (Or.inr hθ.le)).tendsto.const_mul A
  rw [Real.zero_rpow hθ.ne', mul_zero] at ht
  exact (ht.mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds hc)

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

/-- A family whose norms are bounded by `r ^ g a`, with `1 < r` and integer exponents `g a`
tending to `-∞`, tends to zero. -/
theorem tendsto_zero_of_norm_le_zpow {α F : Type*} [SeminormedAddGroup F] {l : Filter α}
    {f : α → F} {r : ℝ} (hr : 1 < r) {g : α → ℤ} (hf : ∀ a, ‖f a‖ ≤ r ^ g a)
    (hg : Tendsto g l atBot) : Tendsto f l (𝓝 0) := by
  refine squeeze_zero_norm hf ?_
  have h := (tendsto_rpow_atBot_of_base_gt_one r hr).comp
    ((tendsto_intCast_atBot_iff (R := ℝ)).2 hg)
  simpa [Function.comp_def, Real.rpow_intCast] using h

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
  have hL := one_half_le_log_two_add hr
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
