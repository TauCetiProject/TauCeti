/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import TauCeti.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Derivatives of trigonometric expressions

The derivative of `t ↦ sin (c t)` is `c cos (c t)` (`TauCeti.deriv_sin_mul`). The first and
second derivatives of `t ↦ cos (c t)` are `-c sin (c t)` and `-c² cos (c t)`
(`TauCeti.deriv_cos_mul`, `TauCeti.deriv_deriv_cos_mul`). For a `C²` function `ζ`, the second
derivative of `t ↦ ζ(t) cos(k t + θ)` is
`ζ'' cos(k t + θ) - 2 k ζ' sin(k t + θ) - k² ζ cos(k t + θ)` (`TauCeti.iteratedDeriv_two_mul_cos`).
The shifted waves `t ↦ sin (c (t - a))` and `t ↦ cos (c (t - a))` have derivatives
`c cos (c (t - a))` and `-c sin (c (t - a))` (`TauCeti.hasDerivAt_sin_mul_sub`,
`TauCeti.hasDerivAt_cos_mul_sub`).
Where `cos t ≠ 0`, the first and second derivatives of `log (cos t)` are `-tan t` and
`-(1 / cos t ^ 2)` (`TauCeti.deriv_log_cos`, `TauCeti.iteratedDeriv_two_log_cos`).

For every real exponent `p`, the map `(k, θ) ↦ (1 - k² sin² θ) ^ p` is smooth on the open set
`{(k, θ) | k ^ 2 < 1}`, where its base is positive, and its partial derivative in `k` there is
`-2 p k sin² θ (1 - k² sin² θ) ^ (p - 1)`. The exponents `p = -1/2` and `p = 1/2` give the
integrands of Legendre's elliptic integrals of the first and second kind.

Every iterated derivative of `sin` is `±sin` or `±cos`. Hence it is bounded by `1`
(`TauCeti.nnnorm_iteratedDeriv_sin_le_one`, `TauCeti.norm_iteratedFDeriv_sin_le_one`), `1`-Lipschitz
(`TauCeti.lipschitzWith_iteratedDeriv_sin`), changes sign under the shift by `π`
(`TauCeti.iteratedDeriv_sin_add_pi`) and attains the absolute value `1`
(`TauCeti.exists_abs_iteratedDeriv_sin_eq_one`).

Away from `f x = ±1`, the chain rule for `Real.arccos` gives the derivative
`-(1 / √(1 - f x ^ 2)) * f'` of `y ↦ arccos (f y)` (`HasDerivAt.arccos`), the counterpart of
Mathlib's `HasDerivAt.arctan`.

On `(0, π)`, the cosecant `x ↦ (sin x)⁻¹` is continuous (`TauCeti.continuousOn_inv_sin_Ioo`) and
convex (`TauCeti.convexOn_inv_sin_Ioo`), with antiderivative `log (tan (x / 2))`
(`TauCeti.hasDerivAt_log_tan_div_two`).
-/

public section

open Real
open scoped Topology

namespace TauCeti

/-- For every real exponent `p`, the map `(k, θ) ↦ (1 - k² sin² θ) ^ p` is smooth on
`{(k, θ) | k ^ 2 < 1}`. -/
theorem contDiffOn_one_sub_sq_mul_sin_sq_rpow {n : WithTop ℕ∞} (p : ℝ) :
    ContDiffOn ℝ n (fun z : ℝ × ℝ ↦ (1 - z.1 ^ 2 * sin z.2 ^ 2) ^ p)
      {z : ℝ × ℝ | z.1 ^ 2 < 1} :=
  (by fun_prop : ContDiff ℝ n fun z : ℝ × ℝ ↦ 1 - z.1 ^ 2 * sin z.2 ^ 2).contDiffOn
    |>.rpow_const_of_ne fun z hz ↦ (one_sub_mul_sin_sq_pos hz z.2).ne'

/-- The derivative of `t ↦ sin (c t)` is `c cos (c t)`. -/
theorem deriv_sin_mul (c t : ℝ) : deriv (fun s ↦ sin (c * s)) t = c * cos (c * t) := by
  rw [deriv_comp_mul_left (f := sin), Real.deriv_sin, smul_eq_mul]

/-- The derivative of `t ↦ cos (c t)` is `-c sin (c t)`. -/
theorem deriv_cos_mul (c t : ℝ) : deriv (fun s ↦ cos (c * s)) t = -(c * sin (c * t)) := by
  rw [deriv_comp_mul_left (f := cos), Real.deriv_cos, smul_eq_mul, mul_neg]

/-- `t ↦ sin (c (t - a))` has derivative `c cos (c (t - a))`. -/
theorem hasDerivAt_sin_mul_sub (c a t : ℝ) :
    HasDerivAt (fun s ↦ sin (c * (s - a))) (c * cos (c * (t - a))) t := by
  convert (((hasDerivAt_id' t).sub_const a).const_mul c).sin using 1
  ring

/-- `t ↦ cos (c (t - a))` has derivative `-c sin (c (t - a))`. -/
theorem hasDerivAt_cos_mul_sub (c a t : ℝ) :
    HasDerivAt (fun s ↦ cos (c * (s - a))) (-c * sin (c * (t - a))) t := by
  convert (((hasDerivAt_id' t).sub_const a).const_mul c).cos using 1
  ring

/-- The second derivative of `t ↦ cos (c t)` is `-c² cos (c t)`. -/
theorem deriv_deriv_cos_mul (c t : ℝ) :
    deriv (deriv fun s ↦ cos (c * s)) t = -(c ^ 2 * cos (c * t)) := by
  have hderiv : (deriv fun s ↦ cos (c * s)) = fun s ↦ -(c * sin (c * s)) :=
    funext (deriv_cos_mul c)
  rw [hderiv, deriv.fun_neg, deriv_const_mul _ (by fun_prop), deriv_comp_mul_left (f := sin),
    Real.deriv_sin, smul_eq_mul]
  ring

/-- The second derivative of a `C²` function modulated by a cosine, `t ↦ ζ(t) cos(k t + θ)`, is
`ζ'' cos(k t + θ) - 2 k ζ' sin(k t + θ) - k² ζ cos(k t + θ)`. -/
theorem iteratedDeriv_two_mul_cos {ζ : ℝ → ℝ} (hζ : ContDiff ℝ 2 ζ) (k θ t : ℝ) :
    iteratedDeriv 2 (fun t => ζ t * cos (k * t + θ)) t =
      iteratedDeriv 2 ζ t * cos (k * t + θ) -
        2 * k * (deriv ζ t * sin (k * t + θ)) - k ^ 2 * (ζ t * cos (k * t + θ)) := by
  have hζ1 : Differentiable ℝ ζ := hζ.differentiable two_ne_zero
  have hζ2 : Differentiable ℝ (deriv ζ) :=
    (hζ.iterate_deriv' 1 1).differentiable one_ne_zero
  have hc (t : ℝ) : HasDerivAt (fun t => k * t + θ) k t := by
    simpa using ((hasDerivAt_id' t).const_mul k).add_const θ
  have hd : deriv (fun t => ζ t * cos (k * t + θ)) =
      fun t => deriv ζ t * cos (k * t + θ) - k * (ζ t * sin (k * t + θ)) := by
    ext t
    refine ((hζ1 t).hasDerivAt.mul (hc t).cos).deriv.trans ?_
    ring
  have hd2 := ((hζ2 t).hasDerivAt.mul (hc t).cos).sub
    (((hζ1 t).hasDerivAt.mul (hc t).sin).const_mul k)
  rw [iteratedDeriv_succ, iteratedDeriv_one, hd, iteratedDeriv_succ, iteratedDeriv_one]
  refine hd2.deriv.trans ?_
  ring

/-- For `k ^ 2 < 1` and every real exponent `p`, the derivative in `k` of
`(1 - k² sin² θ) ^ p` is `-2 p k sin² θ (1 - k² sin² θ) ^ (p - 1)`. -/
theorem hasDerivAt_one_sub_sq_mul_sin_sq_rpow {k : ℝ} (hk : k ^ 2 < 1) (p θ : ℝ) :
    HasDerivAt (fun k ↦ (1 - k ^ 2 * sin θ ^ 2) ^ p)
      (-(2 * p * k * sin θ ^ 2 * (1 - k ^ 2 * sin θ ^ 2) ^ (p - 1))) k := by
  have h := (((hasDerivAt_pow 2 k).mul_const (sin θ ^ 2)).const_sub 1).rpow_const
    (p := p) (Or.inl (one_sub_mul_sin_sq_pos hk θ).ne')
  exact h.congr_deriv (by push_cast; ring)

/-- The derivative of `log (cos t)` is `-tan t` wherever the cosine is nonzero. -/
theorem deriv_log_cos {t : ℝ} (hc : cos t ≠ 0) :
    deriv (fun s : ℝ ↦ log (cos s)) t = -tan t := by
  simpa [Real.tan_eq_sin_div_cos, neg_div] using ((Real.hasDerivAt_cos t).log hc).deriv

/-- The second derivative of `log (cos t)` is `-(1 / cos t ^ 2)` wherever the cosine is nonzero. -/
theorem iteratedDeriv_two_log_cos {t : ℝ} (hc : cos t ≠ 0) :
    iteratedDeriv 2 (fun s : ℝ ↦ log (cos s)) t = -(1 / cos t ^ 2) := by
  rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_zero]
  have hne : ∀ᶠ s in 𝓝 t, cos s ≠ 0 :=
    Real.continuous_cos.continuousAt.eventually_ne hc
  have heq : deriv (fun s : ℝ ↦ log (cos s)) =ᶠ[𝓝 t] fun s ↦ -tan s :=
    hne.mono fun s hs ↦ deriv_log_cos hs
  rw [heq.deriv_eq]
  exact (Real.hasDerivAt_tan hc).neg.deriv

/-- Every iterated derivative of `sin` has `‖·‖₊` at most `1`. -/
theorem nnnorm_iteratedDeriv_sin_le_one (n : ℕ) (x : ℝ) : ‖iteratedDeriv n sin x‖₊ ≤ 1 := by
  simpa [← NNReal.coe_le_coe] using abs_iteratedDeriv_sin_le_one n x

/-- Every iterated Fréchet derivative of `sin` has norm at most `1`. -/
theorem norm_iteratedFDeriv_sin_le_one (n : ℕ) (x : ℝ) : ‖iteratedFDeriv ℝ n sin x‖ ≤ 1 := by
  simpa [norm_iteratedFDeriv_eq_norm_iteratedDeriv] using abs_iteratedDeriv_sin_le_one n x

/-- Every iterated derivative of `sin` is `1`-Lipschitz. -/
theorem lipschitzWith_iteratedDeriv_sin (n : ℕ) : LipschitzWith 1 (iteratedDeriv n sin) :=
  lipschitzWith_of_nnNorm_deriv_le (differentiable_iteratedDeriv_sin n) fun x ↦ by
    simpa [iteratedDeriv_succ] using nnnorm_iteratedDeriv_sin_le_one (n + 1) x

/-- Every iterated derivative of `sin` changes sign under the shift by `π`. -/
theorem iteratedDeriv_sin_add_pi (n : ℕ) (x : ℝ) :
    iteratedDeriv n sin (x + π) = -iteratedDeriv n sin x := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n <;> simp [sin_add_pi, cos_add_pi]

/-- Every iterated derivative of `sin` attains the absolute value `1`. -/
theorem exists_abs_iteratedDeriv_sin_eq_one (n : ℕ) : ∃ x, |iteratedDeriv n sin x| = 1 := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · exact ⟨π / 2, by simp⟩
  · exact ⟨0, by simp⟩

/-- The function `x ↦ (sin x)⁻¹` is continuous on `(0, π)`. -/
theorem continuousOn_inv_sin_Ioo : ContinuousOn (fun x : ℝ ↦ (sin x)⁻¹) (Set.Ioo 0 π) :=
  continuousOn_sin.inv₀ fun _ hx ↦ (sin_pos_of_pos_of_lt_pi hx.1 hx.2).ne'

/-- The function `x ↦ (sin x)⁻¹` is convex on `(0, π)`. -/
theorem convexOn_inv_sin_Ioo : ConvexOn ℝ (Set.Ioo 0 π) (fun x : ℝ ↦ (sin x)⁻¹) := by
  have hinv : ConvexOn ℝ (Set.Ioi 0) (fun y : ℝ ↦ y⁻¹) := by
    simpa only [zpow_neg, zpow_one] using convexOn_zpow (𝕜 := ℝ) (-1)
  refine ⟨convex_Ioo 0 π, fun x hx y hy a b ha hb hab ↦ ?_⟩
  have hsinx : 0 < sin x := sin_pos_of_pos_of_lt_pi hx.1 hx.2
  have hsiny : 0 < sin y := sin_pos_of_pos_of_lt_pi hy.1 hy.2
  have hxy : a • x + b • y ∈ Set.Ioo 0 π := convex_Ioo 0 π hx hy ha hb hab
  have hcomb : 0 < a • sin x + b • sin y := by
    rcases eq_or_lt_of_le ha with rfl | ha'
    · rw [zero_add] at hab
      rw [zero_smul, zero_add, hab, one_smul]
      exact hsiny
    · exact add_pos_of_pos_of_nonneg (smul_pos ha' hsinx) (smul_nonneg hb hsiny.le)
  have hsin : a • sin x + b • sin y ≤ sin (a • x + b • y) :=
    strictConcaveOn_sin_Icc.concaveOn.2 (Set.Ioo_subset_Icc_self hx)
      (Set.Ioo_subset_Icc_self hy) ha hb hab
  have hanti : (sin (a • x + b • y))⁻¹ ≤ (a • sin x + b • sin y)⁻¹ :=
    antitoneOn_inv_pos hcomb (sin_pos_of_pos_of_lt_pi hxy.1 hxy.2) hsin
  exact hanti.trans (hinv.2 hsinx hsiny ha hb hab)

/-- The antiderivative of `(sin x)⁻¹` on `(0, π)` is `log (tan (x / 2))`. -/
theorem hasDerivAt_log_tan_div_two {x : ℝ} (hx₀ : 0 < x) (hxπ : x < π) :
    HasDerivAt (fun t : ℝ ↦ log (tan (t / 2))) (sin x)⁻¹ x := by
  have hx₂ : x / 2 ∈ Set.Ioo 0 (π / 2) := ⟨by linarith, by linarith⟩
  have hsin : 0 < sin (x / 2) := sin_pos_of_pos_of_lt_pi hx₂.1 (by linarith [hx₂.2, pi_pos])
  have hcos : 0 < cos (x / 2) := cos_pos_of_mem_Ioo ⟨by linarith [hx₂.1, pi_pos], hx₂.2⟩
  have htan : 0 < tan (x / 2) := by
    rw [tan_eq_sin_div_cos]
    exact div_pos hsin hcos
  have hhalf : HasDerivAt (fun t : ℝ ↦ t / 2) (1 / 2) x := (hasDerivAt_id' x).div_const 2
  have htan_d := (Real.hasDerivAt_tan hcos.ne').comp x hhalf
  have hlog_d := htan_d.log htan.ne'
  convert hlog_d using 1
  · rfl
  · simp only [Function.comp_apply, tan_eq_sin_div_cos]
    have hx_eq : x = 2 * (x / 2) := by ring
    rw [hx_eq, sin_two_mul]
    field_simp [hsin.ne', hcos.ne']

end TauCeti

/-- **The chain rule for `Real.arccos`.** If `f` has derivative `f'` at `x` and `f x ≠ ±1`, then
`y ↦ arccos (f y)` has derivative `-(1 / √(1 - f x ^ 2)) * f'` at `x`. The `Real.arccos`
counterpart of Mathlib's `HasDerivAt.arctan`. -/
theorem HasDerivAt.arccos {f : ℝ → ℝ} {f' x : ℝ} (hf : HasDerivAt f f' x) (h₁ : f x ≠ -1)
    (h₂ : f x ≠ 1) : HasDerivAt (fun y ↦ Real.arccos (f y)) (-(1 / √(1 - f x ^ 2)) * f') x :=
  (Real.hasDerivAt_arccos h₁ h₂).comp x hf
