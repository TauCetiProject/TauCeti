/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Complex.RealDeriv

/-!
# Real digamma and its bounds on the positive real axis

This file defines the real digamma function `Real.digamma := logDeriv Real.Gamma`, the logarithmic
derivative of real Gamma, and relates it to Mathlib's `Complex.digamma`.

## Main declarations

* `Real.digamma`: the logarithmic derivative of `Real.Gamma`, with the total value `0` at the
  poles `0, -1, -2, ...`.
* `Complex.digamma_ofReal`: at every real point, complex digamma is the coercion of real digamma.
* `Real.hasDerivAt_log_Gamma`, `Real.digamma_eq_deriv_log_Gamma`: at every regular real point,
  real digamma is the derivative of `log ∘ Gamma`.
* `Real.digamma_one`, `Real.digamma_apply_add_one`, `Real.digamma_apply_add_nat`: the value
  `ψ(1) = -γ` and the recurrence `ψ(x + 1) = ψ(x) + 1 / x` with its iterates.
* `Real.digamma_le_log_le`: for `x > 0`, `ψ(x) ≤ log x ≤ ψ(x + 1)`.
* `Real.abs_digamma_sub_log_le`, `Complex.norm_digamma_ofReal_sub_log_le`,
  `Complex.isBigO_digamma_ofReal_sub_log`: for `x > 0`, `|ψ(x) - log x| ≤ 1 / x`, so complex
  digamma differs from the logarithm by `O(1 / x)` on the positive real axis.

The positive-axis bounds come from the log-convexity of Gamma (Bohr–Mollerup): `ψ(x)` and
`ψ(x + 1)` are the derivatives of the convex function `log ∘ Gamma` at the endpoints of
`[x, x + 1]`, and its secant slope over that interval is `log x`.

## References

* T. Tao, [Mathlib PR #43556](https://github.com/leanprover-community/mathlib4/pull/43556),
  for the real digamma definition, recurrence, coercion and bound statements.
-/

public section

open Complex Filter Set Topology

namespace Real

/-- The real digamma function is the logarithmic derivative of real Gamma. -/
noncomputable def digamma : ℝ → ℝ := logDeriv Gamma

/-- The defining logarithmic-derivative formula for real digamma. -/
theorem digamma_def : digamma = logDeriv Gamma := (rfl)

end Real

namespace Complex

private theorem real_ne_neg_nat_of_pos {x : ℝ} (hx : 0 < x) :
    ∀ m : ℕ, x ≠ -(m : ℝ) := by
  intro m
  linarith

private theorem ofReal_ne_neg_nat {x : ℝ} (hx : ∀ m : ℕ, x ≠ -(m : ℝ)) :
    ∀ m : ℕ, (x : ℂ) ≠ -(m : ℂ) := by
  intro m hm
  exact hx m (by exact_mod_cast hm)

/-- At every regular real point, the complex Gamma derivative is the complex coercion
of the derivative of real Gamma. -/
theorem deriv_Gamma_ofReal {x : ℝ} (hx : ∀ m : ℕ, x ≠ -(m : ℝ)) :
    deriv Gamma (x : ℂ) = ((deriv Real.Gamma x : ℝ) : ℂ) := by
  have hpoles := ofReal_ne_neg_nat hx
  have hc := (differentiableAt_Gamma _ hpoles).hasDerivAt.comp_ofReal
  have hr := (Real.differentiableAt_Gamma hx).hasDerivAt.ofReal_comp
  have heq : (fun y : ℝ ↦ Gamma (y : ℂ)) = fun y ↦ (Real.Gamma y : ℂ) :=
    funext Gamma_ofReal
  rw [heq] at hc
  exact hc.unique hr

/-- At every real point, including the total zero values at poles, complex digamma
is the coercion of the real Gamma logarithmic derivative. -/
@[simp]
theorem digamma_ofReal {x : ℝ} :
    digamma (x : ℂ) = (Real.digamma x : ℂ) := by
  rw [Real.digamma_def]
  by_cases hx : ∀ m : ℕ, x ≠ -(m : ℝ)
  · rw [digamma_def, logDeriv_apply, deriv_Gamma_ofReal hx, Gamma_ofReal, logDeriv_apply,
      ofReal_div]
  · push Not at hx
    obtain ⟨m, rfl⟩ := hx
    simp [digamma_def, logDeriv_apply, Gamma_neg_nat_eq_zero, Real.Gamma_neg_nat_eq_zero]

end Complex

namespace Real

/-- At every regular real point, the derivative of the real logarithm of Gamma is digamma. -/
theorem hasDerivAt_log_Gamma {x : ℝ} (hx : ∀ m : ℕ, x ≠ -(m : ℝ)) :
    HasDerivAt (log ∘ Gamma) (digamma x) x := by
  simpa only [digamma_def, Function.comp_def, logDeriv_apply] using
    (differentiableAt_Gamma hx).hasDerivAt.log (Gamma_ne_zero hx)

/-- The real logarithm of Gamma is differentiable at every regular real point. -/
theorem differentiableAt_log_Gamma {x : ℝ} (hx : ∀ m : ℕ, x ≠ -(m : ℝ)) :
    DifferentiableAt ℝ (log ∘ Gamma) x := (hasDerivAt_log_Gamma hx).differentiableAt

/-- Real digamma equals the derivative of the logarithm of Gamma at each regular point. -/
theorem digamma_eq_deriv_log_Gamma {x : ℝ} (hx : ∀ m : ℕ, x ≠ -(m : ℝ)) :
    digamma x = deriv (log ∘ Gamma) x := (hasDerivAt_log_Gamma hx).deriv.symm

/-- The value of real digamma at one is minus Euler's constant. -/
theorem digamma_one : digamma 1 = -eulerMascheroniConstant := by
  apply Complex.ofReal_injective
  push_cast
  simpa [← Complex.digamma_ofReal] using Complex.digamma_one

/-- Real digamma satisfies the Gamma recurrence at every regular real point. -/
theorem digamma_apply_add_one {x : ℝ} (hx : ∀ m : ℕ, x ≠ -(m : ℝ)) :
    digamma (x + 1) = digamma x + 1 / x := by
  apply Complex.ofReal_injective
  push_cast
  simpa [← Complex.digamma_ofReal, one_div] using
    Complex.digamma_apply_add_one (x : ℂ) (Complex.ofReal_ne_neg_nat hx)

/-- The real digamma recurrence iterates over every natural shift. -/
theorem digamma_apply_add_nat {x : ℝ} (hx : ∀ m : ℕ, x ≠ -(m : ℝ)) (n : ℕ) :
    digamma (x + n) = digamma x + ∑ k ∈ Finset.range n, (x + k)⁻¹ := by
  apply Complex.ofReal_injective
  push_cast
  simpa [← Complex.digamma_ofReal] using
    Complex.digamma_apply_add_nat (Complex.ofReal_ne_neg_nat hx) n

private theorem log_Gamma_slope {x : ℝ} (hx : 0 < x) :
    slope (log ∘ Gamma) x (x + 1) = log x := by
  rw [slope_def_field, Function.comp_apply, Function.comp_apply,
    show x + 1 - x = 1 by ring, div_one,
    Gamma_add_one hx.ne', log_mul hx.ne' (Gamma_pos_of_pos hx).ne']
  ring

/-- Positive real digamma lies below the logarithm, and its next shift lies above it. -/
theorem digamma_le_log_le {x : ℝ} (hx : 0 < x) :
    digamma x ≤ log x ∧ log x ≤ digamma (x + 1) := by
  have hu := convexOn_log_Gamma.le_slope_of_hasDerivAt (Set.mem_Ioi.mpr hx)
    (Set.mem_Ioi.mpr (by linarith : 0 < x + 1)) (by linarith)
    (hasDerivAt_log_Gamma (Complex.real_ne_neg_nat_of_pos hx))
  have hl := convexOn_log_Gamma.slope_le_of_hasDerivAt (Set.mem_Ioi.mpr hx)
    (Set.mem_Ioi.mpr (by linarith : 0 < x + 1)) (by linarith)
    (hasDerivAt_log_Gamma (Complex.real_ne_neg_nat_of_pos (by linarith : 0 < x + 1)))
  rw [log_Gamma_slope hx] at hu hl
  exact ⟨hu, hl⟩

/-- The explicit digamma error bound holds on the whole positive real axis. -/
theorem abs_digamma_sub_log_le {x : ℝ} (hx : 0 < x) : |digamma x - log x| ≤ 1 / x := by
  obtain ⟨hu, hl⟩ := digamma_le_log_le hx
  rw [digamma_apply_add_one (Complex.real_ne_neg_nat_of_pos hx)] at hl
  rw [abs_le]
  constructor <;> linarith

end Real

namespace Complex

/-- An explicit error bound for complex digamma on the positive real axis. -/
theorem norm_digamma_ofReal_sub_log_le {x : ℝ} (hx : 0 < x) :
    ‖digamma (x : ℂ) - log (x : ℂ)‖ ≤ x⁻¹ := by
  rw [digamma_ofReal, ← ofReal_log hx.le, ← ofReal_sub, norm_real, Real.norm_eq_abs]
  simpa only [one_div] using Real.abs_digamma_sub_log_le hx

/-- Complex digamma differs from the principal logarithm by `O(1 / x)` on the positive axis. -/
theorem isBigO_digamma_ofReal_sub_log :
    (fun x : ℝ ↦ digamma (x : ℂ) - log (x : ℂ)) =O[atTop] (fun x : ℝ ↦ x⁻¹) := by
  apply Asymptotics.IsBigO.of_bound 1
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  simpa only [one_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hx)] using
    norm_digamma_ofReal_sub_log_le hx

end Complex
