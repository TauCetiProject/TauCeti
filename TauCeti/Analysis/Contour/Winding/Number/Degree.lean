/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.ContDiff.PiecewiseC1On
public import TauCeti.Topology.Circle.Degree
public import TauCeti.Analysis.Contour.Winding.RealIntegral.Basic
public import TauCeti.Topology.Circle.Loop
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
import TauCeti.Analysis.Contour.Argument.Lift
import TauCeti.Analysis.Contour.Winding.SegmentSum
import TauCeti.Analysis.Contour.Winding.Number.Periodic
import TauCeti.Analysis.Contour.Winding.Number.Reparam
import TauCeti.Topology.Circle.Normalize
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import TauCeti.Analysis.Calculus.ContDiff.PiecewiseC1On.AbsolutelyContinuous

/-!
# Winding numbers as degrees of direction loops

Let `γ` be a closed piecewise `C¹` path in `ℂ` avoiding a point `w`. Its direction loop
`t ↦ (γ t - w) / ‖γ t - w‖` is a loop in the unit circle, and the winding number of `γ` about `w`
is the degree `Circle.degree` of this loop
(`TauCeti.Contour.windingNumber_eq_degree_of_eq_div_norm`). Both are read off from one continuous
argument of `γ t - w`: its total change is the imaginary part of the logarithmic contour integral,
and it is also `2π` times the degree. The argument need not be differentiable.

Combined with the real integral formula for the winding number, this identifies the turning
integral `∫ (x y' - y x') / (x² + y²)` of `γ - w = x + i y` with `2π` times the degree of the
direction loop (`TauCeti.Contour.integral_realWindingIntegrand_eq_two_pi_mul_degree`). Applied to
the velocity of a regular closed curve, it identifies the total signed curvature with `2π` times
the degree of the tangent loop.

For a curve that runs once around a circle, `f ∘ circleMap c r` with `f` nonzero on the circle,
the direction loop is read through the boundary direction map `u : S¹ → S¹`,
`u ζ = f (c + r ζ) / ‖f (c + r ζ)‖`, and the winding number of `f` around `0` along the circle is
the degree of `u` (`TauCeti.Contour.windingNumber_comp_circleMap_eq_degree_toBasedLoop`).

## References

* L. Ahlfors, *Complex Analysis*, Chapter 4.
-/

public section

open MeasureTheory Set
open scoped unitInterval Interval

noncomputable section

namespace TauCeti.Contour

/-- **The winding number is the degree of the direction loop.** For a closed piecewise `C¹` path
`γ` avoiding `w`, the winding number of `γ` about `w` is the degree of the loop
`p t = (γ t - w) / ‖γ t - w‖` in the unit circle. Only `γ` is assumed piecewise `C¹`; the loop `p`
is specified pointwise. -/
theorem windingNumber_eq_degree_of_eq_div_norm {x w : ℂ} {u : Circle}
    (γ : Path x x) (p : Path u u) (hγ : IsPiecewiseC1On γ.extend 0 1)
    (havoid : ∀ t : I, γ t ≠ w)
    (hp : ∀ t : I, (p t : ℂ) = (γ t - w) / (‖γ t - w‖ : ℂ)) :
    windingNumber γ.extend 0 1 w = (Circle.degree p : ℂ) := by
  have hc : ContinuousOn γ.extend (Icc 0 1) := γ.continuous_extend.continuousOn
  have hn : ∀ t ∈ Icc (0 : ℝ) 1, γ.extend t ≠ w := by
    intro t ht
    simpa only [Path.extend_apply γ ht] using havoid ⟨t, ht⟩
  -- A continuous argument `θ` of `γ t - w` on `[0, 1]`, built on a partition `s`.
  obtain ⟨N, s, -, hs0, hs1, hsmono, -, hsavoid, hslit, hθ, hlift⟩ :=
    exists_continuousOn_arg_lift_with_partition (by norm_num : (0 : ℝ) ≤ 1) hc hn
  let θ : ℝ → ℝ := fun t ↦ Complex.arg (γ.extend 0 - w) +
    ∑ j ∈ Finset.range N, (Complex.log (segRatio γ.extend w (s j) (s (j + 1)) t)).im
  have hθ_apply (t : ℝ) : θ t = Complex.arg (γ.extend 0 - w) +
      ∑ j ∈ Finset.range N, (Complex.log (segRatio γ.extend w (s j) (s (j + 1)) t)).im := rfl
  simp only [← hθ_apply] at hlift
  -- `θ` lifts the direction loop `p` through `Circle.exp`.
  have hθp : ∀ t : I, Circle.exp (θ t) = p t := by
    intro t
    apply Subtype.ext
    rw [Circle.coe_exp, hp]
    have ht := hlift t t.property
    simp only [Path.extend_apply γ t.property] at ht
    apply (eq_div_iff (Complex.ofReal_ne_zero.mpr
      (norm_ne_zero_iff.mpr (sub_ne_zero.mpr (havoid t))))).2
    rw [mul_comm Complex.I] at ht
    rw [mul_comm]
    exact ht.symm
  -- The total change of the lift is `2π` times the degree of `p` ...
  have hdeg := Circle.sub_eq_degree_mul p hθ.domRestrict hθp
  simp only [Set.domRestrict_apply, Set.Icc.coe_one, Set.Icc.coe_zero,
    sum_im_log_segRatio_eq_zero_of_le hsmono (fun j hj ↦ hsavoid j hj.le) hs0.ge,
    sum_im_log_segRatio_eq_sum_of_le hsmono hs1.le, add_zero, add_sub_cancel_left] at hdeg
  -- ... and the imaginary part of the logarithmic integral of `γ` about `w`.
  have hc' : ContinuousOn γ.extend (uIcc 0 1) := hγ.continuousOn
  have hn' : ∀ t ∈ uIcc (0 : ℝ) 1, γ.extend t ≠ w := by simpa using hn
  have hi := intervalIntegrable_inv_sub_mul_deriv hc' hn' hγ.intervalIntegrable_deriv
  have hac := hγ.absolutelyContinuousOnInterval
  have hsum := hac.integral_inv_sub_mul_deriv_eq_log_norm_add_I_mul_sum_log_im hs0 hs1 hsmono hslit
  rw [windingNumber_eq_integral_of_avoidance hc' hn' hi, hsum, hdeg]
  simp only [Path.extend_zero, Path.extend_one, sub_self, Complex.ofReal_zero, zero_add,
    Complex.ofReal_mul, Complex.ofReal_intCast, Complex.ofReal_ofNat]
  field_simp

/-- **The turning integral is `2π` times the degree of the direction loop.** For a piecewise `C¹`
curve `γ` with `γ 0 = γ 1` avoiding `w` on `[0, 1]`, the real winding integral of `γ - w`, that is
`∫ (x y' - y x') / (x² + y²)` where `γ - w = x + i y`, is `2π` times the degree of the loop
`p t = (γ t - w) / ‖γ t - w‖` in the unit circle. -/
theorem integral_realWindingIntegrand_eq_two_pi_mul_degree {γ : ℝ → ℂ} {w : ℂ} {u : Circle}
    (hγ : IsPiecewiseC1On γ 0 1) (hclosed : γ 0 = γ 1) (havoid : ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ w)
    (p : Path u u) (hp : ∀ t : I, (p t : ℂ) = (γ t - w) / (‖γ t - w‖ : ℂ)) :
    ∫ t in (0 : ℝ)..1, realWindingIntegrand (γ t - w) (deriv γ t) =
      2 * Real.pi * Circle.degree p := by
  have hc : ContinuousOn γ (Icc 0 1) := by
    simpa only [uIcc_of_le zero_le_one] using hγ.continuousOn
  have hn : ∀ t ∈ uIcc (0 : ℝ) 1, γ t ≠ w := by simpa only [uIcc_of_le zero_le_one] using havoid
  have hreal := hγ.absolutelyContinuousOnInterval.windingNumber_eq_real_integral hclosed
    fun ⟨t, ht, h⟩ ↦ hn t ht h
  let Γ : Path (γ 0) (γ 0) :=
    { toFun t := γ t
      continuous_toFun := hc.domRestrict
      source' := rfl
      target' := hclosed.symm }
  have hΓ : EqOn Γ.extend γ (Icc 0 1) := fun t ht ↦ Path.extend_apply Γ ht
  have hdeg := windingNumber_eq_degree_of_eq_div_norm Γ p
    (hγ.congr (by simpa only [uIcc_of_le zero_le_one] using hΓ)) (fun t ↦ havoid t t.property) hp
  rw [windingNumber_congr_curve (hΓ.mono (by simpa using Ioo_subset_Icc_self)), hreal] at hdeg
  have hdeg' : 1 / (2 * Real.pi) *
      ∫ t in (0 : ℝ)..1, realWindingIntegrand (γ t - w) (deriv γ t) = Circle.degree p := by
    exact_mod_cast hdeg
  field_simp at hdeg'
  linarith

/-- **The winding number along a circle is the degree of the boundary direction map.** Let
`f ∘ circleMap c r` be `C¹`, and let `u : S¹ → S¹` be the boundary direction map
`u ζ = f (c + r ζ) / ‖f (c + r ζ)‖` of `f` on the circle of radius `r` about `c`. Then the
winding number of `f` around `0` along that circle, traversed once from `-π` to `π`, is the degree
of `u`. The equation for `u` forces `f` to have no zero on the circle. -/
theorem windingNumber_comp_circleMap_eq_degree_toBasedLoop {f : ℂ → ℂ} {c : ℂ} {r : ℝ}
    (hf : ContDiff ℝ 1 (f ∘ circleMap c r)) (u : C(Circle, Circle))
    (hu : ∀ ζ : Circle, (u ζ : ℂ) = f (c + r * ζ) / ‖f (c + r * ζ)‖) :
    windingNumber (f ∘ circleMap c r) (-Real.pi) Real.pi 0 = Circle.degree u.toBasedLoop := by
  set γ := f ∘ circleMap c r with hγdef
  have hcirc (θ : ℝ) : circleMap c r θ = c + r * (Circle.exp θ : ℂ) := by
    rw [circleMap, Circle.coe_exp]
  -- The norm of `u ζ` is one, so `f` has no zero on the circle.
  have hne (θ : ℝ) : γ θ ≠ 0 :=
    Circle.ne_zero_of_coe_eq_div_norm (z := u (Circle.exp θ)) <| by
      simpa only [hγdef, Function.comp_apply, hcirc] using hu (Circle.exp θ)
  have hper : Function.Periodic γ (2 * Real.pi) := fun θ ↦ by
    simp only [hγdef, Function.comp_apply, periodic_circleMap c r θ]
  -- Shift the parameter interval to `[0, 2π]`, then rescale it to `[0, 1]`.
  have hshift := windingNumber_add_mul_eq_of_periodic hf hper hne 1 (-Real.pi) 0
  simp only [Int.cast_one, one_mul, zero_add] at hshift
  rw [show -Real.pi + 2 * Real.pi = Real.pi by ring] at hshift
  have hdiff : Differentiable ℝ γ := hf.differentiable one_ne_zero
  have hrescale := windingNumber_comp_mul_add (γ := γ) (z₀ := 0) (a := 0) (b := 1)
    (r := 2 * Real.pi) (s := 0) (fun t _ ↦ hdiff t)
    hf.continuous_deriv_one.continuousOn (fun t _ ↦ hne t)
  simp only [mul_zero, add_zero, mul_one] at hrescale
  rw [hshift, ← hrescale]
  -- The rescaled curve is a closed path whose direction loop is `u.toBasedLoop`.
  have hclosed : γ (2 * Real.pi * (0 : ℝ)) = γ (2 * Real.pi * (1 : ℝ)) := by
    simpa using (hper 0).symm
  let Γ : Path (γ (2 * Real.pi * (0 : ℝ))) (γ (2 * Real.pi * (0 : ℝ))) :=
    { toFun t := γ (2 * Real.pi * t)
      continuous_toFun := hf.continuous.comp (continuous_const.mul continuous_subtypeVal)
      source' := rfl
      target' := hclosed.symm }
  have hΓ_apply (t : I) : Γ t = γ (2 * Real.pi * t) := rfl
  have hΓ : EqOn Γ.extend (γ ∘ fun t ↦ 2 * Real.pi * t) (uIoo 0 1) := fun t ht ↦ by
    rw [Path.extend_apply Γ (Ioo_subset_Icc_self (by simpa using ht)), hΓ_apply,
      Function.comp_apply]
  rw [← windingNumber_congr_curve hΓ]
  refine windingNumber_eq_degree_of_eq_div_norm Γ u.toBasedLoop ?_ (fun t ↦ hne _) fun t ↦ ?_
  · refine (IsPiecewiseC1On.of_contDiffOn (γ := γ ∘ fun t ↦ 2 * Real.pi * t)
      (hf.comp (contDiff_const.mul contDiff_id)).contDiffOn).congr fun t ht ↦ ?_
    rw [Path.extend_apply Γ (by simpa [uIcc_of_le zero_le_one] using ht), hΓ_apply,
      Function.comp_apply]
  · simp [hu, hΓ_apply, hγdef, hcirc, TauCeti.unitToCircle_apply]

end TauCeti.Contour
