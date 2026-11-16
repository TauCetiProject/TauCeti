/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.LogDeriv
public import TauCeti.Analysis.Calculus.ContDiff.PiecewiseC1On
public import TauCeti.Analysis.Contour.Winding.Number.Basic
import TauCeti.Analysis.Contour.Argument.Lift
import TauCeti.Analysis.Contour.LogDerivFTC
import TauCeti.Analysis.Contour.Winding.SegmentSum

/-!
# The variation of a continuous argument along a curve

A curve `c : ℝ → ℂ`, continuous and nowhere zero on `[a, b]`, has a *continuous argument*: a
function `θ`, continuous on `[a, b]`, with `c t = ‖c t‖ · exp (i θ t)` there
(`TauCeti.Contour.exists_continuousOn_eq_norm_mul_exp`). Two such arguments differ by a constant
multiple of `2π`, so the *variation* `θ b - θ a` does not depend on the choice
(`TauCeti.Contour.sub_eq_sub_of_eq_norm_mul_exp`); both facts are proved in
`TauCeti.Analysis.Contour.Argument.Lift`.

The variation is the imaginary part of the logarithmic integral: if `c` is differentiable off a
countable set with `c' / c` integrable,

`∫_a^b c' / c = (log ‖c b‖ - log ‖c a‖) + i (θ b - θ a)`

(`TauCeti.Contour.integral_deriv_div_eq_log_norm_add_I_mul_sub`), with no condition on how `θ` was
built. Applied to `c = h ∘ γ` for `h` analytic and zero-free along a piecewise `C¹` curve `γ`, the
left side is the contour integral of the logarithmic derivative `h' / h` along `γ`
(`TauCeti.Contour.integral_deriv_smul_logDeriv_eq_log_norm_add_I_mul_sub`). For a closed curve the
modulus term vanishes, and the winding number about `w` is the variation of a continuous argument
of `γ - w` divided by `2π` (`TauCeti.Contour.windingNumber_eq_sub_div_two_pi_of_avoidance`, and
`TauCeti.Contour.windingNumber_eq_sub_div_two_pi` for piecewise `C¹` curves). These identities hold
for either order of the endpoints, with the hypotheses stated on `[[a, b]] = uIcc a b`.

These are the forms in which the argument principle is used to count zeros by following the
argument of a function along a contour, as in the classical proof of the Riemann–von Mangoldt
formula, where only the difference of the argument at two points of a path enters.

## References

* L. Ahlfors, *Complex Analysis*, Chapter 4, §5.2.
* E. C. Titchmarsh, *The Theory of the Riemann Zeta-Function*, §9.3.
-/

public section

open Complex MeasureTheory Set
open scoped Real Interval

namespace TauCeti.Contour

variable {c : ℝ → ℂ} {a b : ℝ} {θ : ℝ → ℝ}

/-- **The logarithmic integral is the change of the logarithm of the modulus plus `i` times the
variation of a continuous argument.** For `c` continuous and nowhere zero on `[[a, b]]`, with
derivative `c'` off a countable set and `c' / c` integrable, and any continuous argument `θ` of
`c` on `[[a, b]]`,

`∫_a^b c' / c = (log ‖c b‖ - log ‖c a‖) + i (θ b - θ a)`. -/
theorem integral_deriv_div_eq_log_norm_add_I_mul_sub {c' : ℝ → ℂ} {P : Set ℝ}
    (hP : P.Countable) (hc : ContinuousOn c (uIcc a b))
    (hd : ∀ t ∈ Ioo (min a b) (max a b) \ P, HasDerivAt c (c' t) t)
    (hint : IntervalIntegrable (fun t ↦ c' t / c t) volume a b)
    (hne : ∀ t ∈ uIcc a b, c t ≠ 0) (hθ : ContinuousOn θ (uIcc a b))
    (hlift : ∀ t ∈ uIcc a b, c t = ‖c t‖ * exp (I * θ t)) :
    ∫ t in a..b, c' t / c t = (Real.log ‖c b‖ - Real.log ‖c a‖ : ℝ) + I * (θ b - θ a : ℝ) := by
  -- Both sides change sign when `a` and `b` are swapped, so it suffices to treat `a ≤ b`.
  wlog hab : a ≤ b generalizing a b
  · have h := this (by rwa [uIcc_comm]) (by rwa [min_comm, max_comm]) hint.symm
      (by rwa [uIcc_comm]) (by rwa [uIcc_comm]) (by rwa [uIcc_comm]) (not_le.mp hab).le
    rw [intervalIntegral.integral_symm, h]
    push_cast
    ring
  rw [uIcc_of_le hab] at hc hne hθ hlift
  rw [min_eq_left hab, max_eq_right hab] at hd
  -- Compare with the argument assembled along a partition, whose variation is a segment sum.
  obtain ⟨N, s, -, hs0, hsN, hsmono, -, hsne, hslit, hθ₀, hlift₀⟩ :=
    exists_continuousOn_arg_lift_with_partition (w := 0) hab hc hne
  simp only [sub_zero] at hslit hsne hθ₀ hlift₀
  have hsum := integral_deriv_div_sub_eq_log_norm_add_I_mul_sum_log_im (w := 0) hP hs0 hsN hsmono
    hc hd (by simpa only [sub_zero] using hslit) (by simpa only [sub_zero] using hint)
  simp only [sub_zero] at hsum
  rw [hsum, sub_eq_sub_of_eq_norm_mul_exp isPreconnected_Icc (left_mem_Icc.mpr hab)
      (right_mem_Icc.mpr hab) hne hθ hθ₀ hlift hlift₀,
    sum_im_log_segRatio_eq_sum_of_le hsmono hsN.le,
    sum_im_log_segRatio_eq_zero_of_le hsmono (fun j hj ↦ by simpa using hsne j hj.le) hs0.ge]
  simp

/-- **The contour integral of a logarithmic derivative in terms of a continuous argument.** If `h`
is analytic and zero-free along a piecewise `C¹` curve `γ` on `[[a, b]]`, and `θ` is a continuous
argument of `h ∘ γ` there, then

`∫_a^b γ' · (h' / h) ∘ γ = (log ‖h (γ b)‖ - log ‖h (γ a)‖) + i (θ b - θ a)`. -/
theorem integral_deriv_smul_logDeriv_eq_log_norm_add_I_mul_sub {γ : ℝ → ℂ} {h : ℂ → ℂ}
    (hγ : IsPiecewiseC1On γ a b) (hh : ∀ t ∈ uIcc a b, AnalyticAt ℂ h (γ t))
    (hne : ∀ t ∈ uIcc a b, h (γ t) ≠ 0) (hθ : ContinuousOn θ (uIcc a b))
    (hlift : ∀ t ∈ uIcc a b, h (γ t) = ‖h (γ t)‖ * exp (I * θ t)) :
    ∫ t in a..b, deriv γ t • logDeriv h (γ t) =
      (Real.log ‖h (γ b)‖ - Real.log ‖h (γ a)‖ : ℝ) + I * (θ b - θ a : ℝ) := by
  obtain ⟨p, hp⟩ := hγ.exists_finset_differentiableAt
  have heq : (fun t ↦ deriv γ t • logDeriv h (γ t)) =
      fun t ↦ (deriv γ t • deriv h (γ t)) / h (γ t) := by
    funext t
    rw [logDeriv_apply, smul_eq_mul, smul_eq_mul, mul_div_assoc]
  have hint := intervalIntegrable_deriv_smul_logDeriv hγ hh hne
  rw [heq] at hint ⊢
  exact integral_deriv_div_eq_log_norm_add_I_mul_sub (c := fun t ↦ h (γ t))
    p.countable_toSet (fun t ht ↦ (hh t ht).continuousAt.comp_continuousWithinAt
      (hγ.continuousOn t ht))
    (fun t ht ↦ ((hh t (Ioo_subset_Icc_self ht.1)).differentiableAt.hasDerivAt).scomp t
      (hp t ht).hasDerivAt) hint hne hθ hlift

/-- **The winding number is the variation of a continuous argument divided by `2π`.** For a
closed curve `γ`, continuous on `[[a, b]]` and avoiding `w` there, differentiable off a countable
set with `(γ - w)⁻¹ γ'` integrable, and any continuous argument `θ` of `γ - w` on `[[a, b]]`, the
winding number of `γ` about `w` is `(θ b - θ a) / (2π)`. -/
theorem windingNumber_eq_sub_div_two_pi_of_avoidance {γ : ℝ → ℂ} {w : ℂ} {P : Set ℝ}
    (hP : P.Countable) (hγ : ContinuousOn γ (uIcc a b))
    (hd : ∀ t ∈ Ioo (min a b) (max a b) \ P, DifferentiableAt ℝ γ t)
    (hint : IntervalIntegrable (fun t ↦ (γ t - w)⁻¹ * deriv γ t) volume a b)
    (hclosed : γ a = γ b) (hne : ∀ t ∈ uIcc a b, γ t ≠ w) (hθ : ContinuousOn θ (uIcc a b))
    (hlift : ∀ t ∈ uIcc a b, γ t - w = ‖γ t - w‖ * exp (I * θ t)) :
    windingNumber γ a b w = ((θ b - θ a) / (2 * π) : ℝ) := by
  have heq : (fun t ↦ (γ t - w)⁻¹ * deriv γ t) = fun t ↦ deriv γ t / (γ t - w) := by
    funext t
    rw [inv_mul_eq_div]
  rw [windingNumber_eq_integral_of_avoidance hγ hne hint, heq,
    integral_deriv_div_eq_log_norm_add_I_mul_sub (c := fun t ↦ γ t - w) hP
      (hγ.sub continuousOn_const) (fun t ht ↦ (hd t ht).hasDerivAt.sub_const w) (heq ▸ hint)
      (fun t ht ↦ sub_ne_zero.mpr (hne t ht)) hθ hlift, hclosed]
  push_cast
  field_simp
  ring

/-- **The winding number of a piecewise `C¹` curve is the variation of a continuous argument
divided by `2π`.** For a closed piecewise `C¹` curve `γ` on `[[a, b]]` avoiding `w`, and any
continuous argument `θ` of `γ - w` on `[[a, b]]`, the winding number of `γ` about `w` is
`(θ b - θ a) / (2π)`. -/
theorem windingNumber_eq_sub_div_two_pi {γ : ℝ → ℂ} {w : ℂ}
    (hγ : IsPiecewiseC1On γ a b) (hclosed : γ a = γ b) (hne : ∀ t ∈ uIcc a b, γ t ≠ w)
    (hθ : ContinuousOn θ (uIcc a b))
    (hlift : ∀ t ∈ uIcc a b, γ t - w = ‖γ t - w‖ * exp (I * θ t)) :
    windingNumber γ a b w = ((θ b - θ a) / (2 * π) : ℝ) := by
  obtain ⟨p, hp⟩ := hγ.exists_finset_differentiableAt
  exact windingNumber_eq_sub_div_two_pi_of_avoidance p.countable_toSet hγ.continuousOn hp
    (intervalIntegrable_inv_sub_mul_deriv hγ.continuousOn hne hγ.intervalIntegrable_deriv)
    hclosed hne hθ hlift

end TauCeti.Contour
