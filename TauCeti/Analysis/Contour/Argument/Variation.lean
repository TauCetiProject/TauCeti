/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
public import TauCeti.Analysis.Contour.Winding.Number.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import TauCeti.Analysis.Contour.Argument.Lift
import TauCeti.Analysis.Contour.LogDerivFTC
import TauCeti.Analysis.Contour.Winding.Number.AbsolutelyContinuous
import TauCeti.Analysis.Contour.Winding.SegmentSum
import TauCeti.MeasureTheory.Function.AbsolutelyContinuous.Comp

/-!
# The variation of a continuous argument along a curve

A curve `c : ℝ → ℂ`, continuous and nowhere zero on `[a, b]`, has a *continuous argument*: a
function `θ`, continuous on `[a, b]`, with `c t = ‖c t‖ · exp (i θ t)` there
(`TauCeti.Contour.exists_continuousOn_eq_norm_mul_exp`). Two such arguments differ by a constant
multiple of `2π`, so the *variation* `θ b - θ a` does not depend on the choice
(`TauCeti.Contour.sub_eq_sub_of_eq_norm_mul_exp`); both facts are proved in
`TauCeti.Analysis.Contour.Argument.Lift`.

The variation is the imaginary part of the logarithmic integral: if `c` is absolutely continuous,

`∫_a^b c' / c = (log ‖c b‖ - log ‖c a‖) + i (θ b - θ a)`

(`AbsolutelyContinuousOnInterval.integral_deriv_div_eq_log_norm_add_I_mul_sub`), with no condition
on how `θ` was built. Applied to `c = h ∘ γ` for `h` analytic and zero-free along an absolutely
continuous curve `γ`, the left side is the contour integral of the logarithmic derivative `h' / h`
along `γ` (`AbsolutelyContinuousOnInterval.integral_deriv_smul_logDeriv_eq_log_norm_add_I_mul_sub`).
For a closed curve the modulus term vanishes, and the winding number about `w` is the variation of
a continuous argument of `γ - w` divided by `2π`
(`AbsolutelyContinuousOnInterval.windingNumber_eq_sub_div_two_pi`). These identities hold for
either order of the endpoints, with the hypotheses stated on `[[a, b]] = uIcc a b`.

These are the forms in which the argument principle is used to count zeros by following the
argument of a function along a contour, as in the classical proof of the Riemann–von Mangoldt
formula, where only the difference of the argument at two points of a path enters.

## References

* L. Ahlfors, *Complex Analysis*, Chapter 4, §5.2.
* E. C. Titchmarsh, *The Theory of the Riemann Zeta-Function*, §9.3.
-/

public section

open Complex MeasureTheory Set TauCeti.Contour

open scoped Real Interval

namespace AbsolutelyContinuousOnInterval

variable {c : ℝ → ℂ} {a b : ℝ} {θ : ℝ → ℝ}

/-- **The logarithmic integral is the change of the logarithm of the modulus plus `i` times the
variation of a continuous argument.** For `c` absolutely continuous and nowhere zero on
`[[a, b]]`, and any continuous argument `θ` of `c` on `[[a, b]]`,

`∫_a^b c' / c = (log ‖c b‖ - log ‖c a‖) + i (θ b - θ a)`. -/
theorem integral_deriv_div_eq_log_norm_add_I_mul_sub (hc : AbsolutelyContinuousOnInterval c a b)
    (hne : ∀ t ∈ uIcc a b, c t ≠ 0) (hθ : ContinuousOn θ (uIcc a b))
    (hlift : ∀ t ∈ uIcc a b, c t = ‖c t‖ * exp (I * θ t)) :
    ∫ t in a..b, deriv c t / c t = (Real.log ‖c b‖ - Real.log ‖c a‖ : ℝ) + I * (θ b - θ a : ℝ) := by
  -- Both sides change sign when `a` and `b` are swapped, so it suffices to treat `a ≤ b`.
  wlog hab : a ≤ b generalizing a b
  · have h := this hc.symm (by rwa [uIcc_comm]) (by rwa [uIcc_comm]) (by rwa [uIcc_comm])
      (not_le.mp hab).le
    rw [intervalIntegral.integral_symm, h]
    push_cast
    ring
  have hcont : ContinuousOn c (Icc a b) := uIcc_of_le hab ▸ hc.continuousOn
  rw [uIcc_of_le hab] at hne hθ hlift
  -- Compare with the argument assembled along a partition, whose variation is a segment sum.
  obtain ⟨N, s, -, hs0, hsN, hsmono, -, hsne, hslit, hθ₀, hlift₀⟩ :=
    exists_continuousOn_arg_lift_with_partition (w := 0) hab hcont hne
  simp only [sub_zero] at hslit hsne hθ₀ hlift₀
  have hsum := hc.integral_inv_sub_mul_deriv_eq_log_norm_add_I_mul_sum_log_im (w := 0) hs0 hsN
    hsmono (by simpa only [sub_zero] using hslit)
  simp only [sub_zero, inv_mul_eq_div] at hsum
  rw [hsum, sub_eq_sub_of_eq_norm_mul_exp isPreconnected_Icc (left_mem_Icc.mpr hab)
      (right_mem_Icc.mpr hab) hne hθ hθ₀ hlift hlift₀,
    sum_im_log_segRatio_eq_sum_of_le hsmono hsN.le,
    sum_im_log_segRatio_eq_zero_of_le hsmono (fun j hj ↦ by simpa using hsne j hj.le) hs0.ge]
  simp

/-- **The contour integral of a logarithmic derivative in terms of a continuous argument.** If `h`
is analytic and zero-free along an absolutely continuous curve `γ` on `[[a, b]]`, and `θ` is a
continuous argument of `h ∘ γ` there, then

`∫_a^b γ' · (h' / h) ∘ γ = (log ‖h (γ b)‖ - log ‖h (γ a)‖) + i (θ b - θ a)`. -/
theorem integral_deriv_smul_logDeriv_eq_log_norm_add_I_mul_sub {γ : ℝ → ℂ} {h : ℂ → ℂ}
    (hγ : AbsolutelyContinuousOnInterval γ a b) (hh : ∀ t ∈ uIcc a b, AnalyticAt ℂ h (γ t))
    (hne : ∀ t ∈ uIcc a b, h (γ t) ≠ 0) (hθ : ContinuousOn θ (uIcc a b))
    (hlift : ∀ t ∈ uIcc a b, h (γ t) = ‖h (γ t)‖ * exp (I * θ t)) :
    ∫ t in a..b, deriv γ t • logDeriv h (γ t) =
      (Real.log ‖h (γ b)‖ - Real.log ‖h (γ a)‖ : ℝ) + I * (θ b - θ a : ℝ) := by
  -- `h ∘ γ` is absolutely continuous and misses `0`, and its winding number about `0` is computed
  -- by both integrals.
  have hhγ : AbsolutelyContinuousOnInterval (h ∘ γ) a b := by
    refine hγ.comp_of_contDiffAt ?_
    rintro _ ⟨t, ht, rfl⟩
    exact ((hh t ht).contDiffAt (n := 1)).restrict_scalars ℝ
  have key := (hγ.windingNumber_comp_eq_integral_logDeriv hh hne).symm.trans
    (hhγ.windingNumber_eq_integral fun ⟨t, ht, e⟩ ↦ hne t ht e)
  rw [mul_right_inj' (inv_ne_zero two_pi_I_ne_zero)] at key
  rw [key]
  simpa only [Function.comp_apply, sub_zero, inv_mul_eq_div] using
    hhγ.integral_deriv_div_eq_log_norm_add_I_mul_sub hne hθ hlift

/-- **The winding number is the variation of a continuous argument divided by `2π`.** For a
closed absolutely continuous curve `γ` on `[[a, b]]` avoiding `w`, and any continuous argument `θ`
of `γ - w` on `[[a, b]]`, the winding number of `γ` about `w` is `(θ b - θ a) / (2π)`. -/
theorem windingNumber_eq_sub_div_two_pi {γ : ℝ → ℂ} {w : ℂ}
    (hγ : AbsolutelyContinuousOnInterval γ a b) (hclosed : γ a = γ b)
    (hne : ∀ t ∈ uIcc a b, γ t ≠ w) (hθ : ContinuousOn θ (uIcc a b))
    (hlift : ∀ t ∈ uIcc a b, γ t - w = ‖γ t - w‖ * exp (I * θ t)) :
    windingNumber γ a b w = ((θ b - θ a) / (2 * π) : ℝ) := by
  have hc : AbsolutelyContinuousOnInterval (fun t ↦ γ t - w) a b :=
    hγ.sub (LipschitzWith.const w).lipschitzOnWith.absolutelyContinuousOnInterval
  have h := hc.integral_deriv_div_eq_log_norm_add_I_mul_sub
    (fun t ht ↦ sub_ne_zero.mpr (hne t ht)) hθ hlift
  simp only [deriv_sub_const] at h
  rw [hγ.windingNumber_eq_integral fun ⟨t, ht, e⟩ ↦ hne t ht e]
  simp only [inv_mul_eq_div]
  rw [h, hclosed]
  push_cast
  field_simp
  ring

end AbsolutelyContinuousOnInterval
