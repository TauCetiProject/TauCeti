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
import TauCeti.Topology.Circle.Degree

/-!
# The variation of a continuous argument along a curve

A curve `c : ℝ → ℂ`, continuous and nowhere zero on `[a, b]`, has a *continuous argument*: a
function `θ`, continuous on `[a, b]`, with `c t = ‖c t‖ · exp (i θ t)` there
(`TauCeti.Contour.exists_continuousOn_eq_norm_mul_exp`). Two such arguments differ by a constant
multiple of `2π`, so the *variation* `θ b - θ a` does not depend on the choice
(`TauCeti.Contour.sub_eq_sub_of_eq_norm_mul_exp`).

The variation is the imaginary part of the logarithmic integral: if `c` is differentiable off a
countable set with `c' / c` integrable,

`∫_a^b c' / c = (log ‖c b‖ - log ‖c a‖) + i (θ b - θ a)`

(`TauCeti.Contour.integral_deriv_div_eq_log_norm_add_I_mul_sub`), with no condition on how `θ` was
built. Applied to `c = h ∘ γ` for `h` analytic and zero-free along a piecewise `C¹` curve `γ`, the
left side is the contour integral of the logarithmic derivative `h' / h` along `γ`
(`TauCeti.Contour.integral_deriv_smul_logDeriv_eq_log_norm_add_I_mul_sub`). For a closed curve the
modulus term vanishes, and the winding number about `w` is the variation of a continuous argument
of `γ - w` divided by `2π` (`TauCeti.Contour.windingNumber_eq_sub_div_two_pi`).

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

variable {c : ℝ → ℂ} {a b : ℝ} {θ θ' : ℝ → ℝ}

/-- **Continuous arguments exist.** A curve continuous and nowhere zero on `[a, b]` has an
argument `θ` continuous on `[a, b]`: `c t = ‖c t‖ · exp (i θ t)` for every `t ∈ [a, b]`. -/
theorem exists_continuousOn_eq_norm_mul_exp (hc : ContinuousOn c (Icc a b))
    (hne : ∀ t ∈ Icc a b, c t ≠ 0) :
    ∃ θ : ℝ → ℝ, ContinuousOn θ (Icc a b) ∧ ∀ t ∈ Icc a b, c t = ‖c t‖ * exp (I * θ t) := by
  rcases le_or_gt a b with hab | hab
  · obtain ⟨N, s, -, -, -, -, -, -, -, hθ, hlift⟩ :=
      exists_continuousOn_arg_lift_with_partition (w := 0) hab hc (by simpa using hne)
    exact ⟨_, hθ, fun t ht ↦ by simpa only [sub_zero] using hlift t ht⟩
  · exact ⟨0, continuousOn_const, fun t ht ↦ absurd ht (by simp [Icc_eq_empty_of_lt hab])⟩

/-- **The variation of a continuous argument is well defined.** Two continuous arguments `θ` and
`θ'` of a curve nowhere zero on `[a, b]` change by the same amount from `a` to `b`. -/
theorem sub_eq_sub_of_eq_norm_mul_exp (hab : a ≤ b) (hne : ∀ t ∈ Icc a b, c t ≠ 0)
    (hθ : ContinuousOn θ (Icc a b)) (hθ' : ContinuousOn θ' (Icc a b))
    (hcθ : ∀ t ∈ Icc a b, c t = ‖c t‖ * exp (I * θ t))
    (hcθ' : ∀ t ∈ Icc a b, c t = ‖c t‖ * exp (I * θ' t)) :
    θ b - θ a = θ' b - θ' a := by
  have : PreconnectedSpace (Icc a b) := Subtype.preconnectedSpace isPreconnected_Icc
  -- Both arguments lift the same map `[a, b] → Circle`, so they differ by a constant.
  obtain ⟨k, hk⟩ := Circle.exists_forall_eq_add_of_exp_eq (A := Icc a b)
    hθ.domRestrict hθ'.domRestrict fun t ↦ by
      apply Subtype.ext
      have hn : (‖c t‖ : ℂ) ≠ 0 := ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (hne t t.2))
      rw [Circle.coe_exp, Circle.coe_exp, mul_comm _ I, mul_comm _ I]
      exact mul_left_cancel₀ hn ((hcθ t t.2).symm.trans (hcθ' t t.2))
  have ha := hk ⟨a, left_mem_Icc.mpr hab⟩
  have hb := hk ⟨b, right_mem_Icc.mpr hab⟩
  simp only [domRestrict_apply] at ha hb
  linarith

/-- **The logarithmic integral is the change of the logarithm of the modulus plus `i` times the
variation of a continuous argument.** For `c` continuous and nowhere zero on `[a, b]`, with
derivative `c'` off a countable set and `c' / c` integrable, and any continuous argument `θ` of
`c` on `[a, b]`,

`∫_a^b c' / c = (log ‖c b‖ - log ‖c a‖) + i (θ b - θ a)`. -/
theorem integral_deriv_div_eq_log_norm_add_I_mul_sub {c' : ℝ → ℂ} {P : Set ℝ} (hab : a ≤ b)
    (hP : P.Countable) (hc : ContinuousOn c (Icc a b))
    (hd : ∀ t ∈ Ioo a b \ P, HasDerivAt c (c' t) t)
    (hint : IntervalIntegrable (fun t ↦ c' t / c t) volume a b)
    (hne : ∀ t ∈ Icc a b, c t ≠ 0) (hθ : ContinuousOn θ (Icc a b))
    (hlift : ∀ t ∈ Icc a b, c t = ‖c t‖ * exp (I * θ t)) :
    ∫ t in a..b, c' t / c t = (Real.log ‖c b‖ - Real.log ‖c a‖ : ℝ) + I * (θ b - θ a : ℝ) := by
  -- Compare with the argument assembled along a partition, whose variation is a segment sum.
  obtain ⟨N, s, -, hs0, hsN, hsmono, -, hsne, hslit, hθ₀, hlift₀⟩ :=
    exists_continuousOn_arg_lift_with_partition (w := 0) hab hc hne
  simp only [sub_zero] at hslit hsne hθ₀ hlift₀
  have hsum := integral_deriv_div_sub_eq_log_norm_add_I_mul_sum_log_im (w := 0) hP hs0 hsN hsmono
    hc hd (by simpa only [sub_zero] using hslit) (by simpa only [sub_zero] using hint)
  simp only [sub_zero] at hsum
  rw [hsum, sub_eq_sub_of_eq_norm_mul_exp hab hne hθ hθ₀ hlift hlift₀,
    sum_im_log_segRatio_eq_sum_of_le hsmono hsN.le,
    sum_im_log_segRatio_eq_zero_of_le hsmono (fun j hj ↦ by simpa using hsne j hj.le) hs0.ge]
  simp

/-- **The contour integral of a logarithmic derivative in terms of a continuous argument.** If `h`
is analytic and zero-free along a piecewise `C¹` curve `γ` on `[a, b]`, and `θ` is a continuous
argument of `h ∘ γ` there, then

`∫_a^b γ' · (h' / h) ∘ γ = (log ‖h (γ b)‖ - log ‖h (γ a)‖) + i (θ b - θ a)`. -/
theorem integral_deriv_smul_logDeriv_eq_log_norm_add_I_mul_sub {γ : ℝ → ℂ} {h : ℂ → ℂ}
    (hab : a ≤ b) (hγ : IsPiecewiseC1On γ a b) (hh : ∀ t ∈ Icc a b, AnalyticAt ℂ h (γ t))
    (hne : ∀ t ∈ Icc a b, h (γ t) ≠ 0) (hθ : ContinuousOn θ (Icc a b))
    (hlift : ∀ t ∈ Icc a b, h (γ t) = ‖h (γ t)‖ * exp (I * θ t)) :
    ∫ t in a..b, deriv γ t • logDeriv h (γ t) =
      (Real.log ‖h (γ b)‖ - Real.log ‖h (γ a)‖ : ℝ) + I * (θ b - θ a : ℝ) := by
  have hu : uIcc a b = Icc a b := uIcc_of_le hab
  obtain ⟨p, hp⟩ := hγ.exists_finset_differentiableAt
  rw [min_eq_left hab, max_eq_right hab] at hp
  have heq : (fun t ↦ deriv γ t • logDeriv h (γ t)) =
      fun t ↦ (deriv γ t • deriv h (γ t)) / h (γ t) := by
    funext t
    rw [logDeriv_apply, smul_eq_mul, smul_eq_mul, mul_div_assoc]
  have hint := intervalIntegrable_deriv_smul_logDeriv hγ (hu ▸ hh) (hu ▸ hne)
  rw [heq] at hint ⊢
  exact integral_deriv_div_eq_log_norm_add_I_mul_sub (c := fun t ↦ h (γ t)) hab
    p.countable_toSet (fun t ht ↦ (hh t ht).continuousAt.comp_continuousWithinAt
      (hγ.continuousOn.mono hu.ge t ht))
    (fun t ht ↦ ((hh t (Ioo_subset_Icc_self ht.1)).differentiableAt.hasDerivAt).scomp t
      (hp t ht).hasDerivAt) hint hne hθ hlift

/-- **The winding number is the variation of a continuous argument divided by `2π`.** For a
closed piecewise `C¹` curve `γ` on `[a, b]` avoiding `w`, and any continuous argument `θ` of
`γ - w` on `[a, b]`, the winding number of `γ` about `w` is `(θ b - θ a) / (2π)`. -/
theorem windingNumber_eq_sub_div_two_pi {γ : ℝ → ℂ} {w : ℂ} (hab : a ≤ b)
    (hγ : IsPiecewiseC1On γ a b) (hclosed : γ a = γ b) (hne : ∀ t ∈ Icc a b, γ t ≠ w)
    (hθ : ContinuousOn θ (Icc a b))
    (hlift : ∀ t ∈ Icc a b, γ t - w = ‖γ t - w‖ * exp (I * θ t)) :
    windingNumber γ a b w = ((θ b - θ a) / (2 * π) : ℝ) := by
  have hu : uIcc a b = Icc a b := uIcc_of_le hab
  have hint := intervalIntegrable_inv_sub_mul_deriv hγ.continuousOn (hu ▸ hne)
    hγ.intervalIntegrable_deriv
  obtain ⟨p, hp⟩ := hγ.exists_finset_differentiableAt
  rw [min_eq_left hab, max_eq_right hab] at hp
  have heq : (fun t ↦ (γ t - w)⁻¹ * deriv γ t) = fun t ↦ deriv γ t / (γ t - w) := by
    funext t
    rw [inv_mul_eq_div]
  rw [windingNumber_eq_integral_of_avoidance hγ.continuousOn (hu ▸ hne) hint, heq,
    integral_deriv_div_eq_log_norm_add_I_mul_sub (c := fun t ↦ γ t - w) hab p.countable_toSet
      ((hγ.continuousOn.mono hu.ge).sub continuousOn_const)
      (fun t ht ↦ (hp t ht).hasDerivAt.sub_const w) (heq ▸ hint)
      (fun t ht ↦ sub_ne_zero.mpr (hne t ht)) hθ hlift, hclosed]
  push_cast
  field_simp
  ring

end TauCeti.Contour
