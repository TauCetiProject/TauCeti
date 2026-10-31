/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.Flow
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.ODE.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
-- Private: monotonicity, constant-curve recognition, and the fundamental theorem of calculus are
-- used only in proofs; no declaration below exposes their APIs.
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.ODE.Transform
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Negative gradient trajectories

This file develops the first dynamical facts about negative gradient trajectories in a real
Hilbert space.  A curve `γ` is read through Mathlib's existing `IsIntegralCurveOn` predicate for
the autonomous vector field `fun _ x ↦ -∇ f x`; no parallel notion of trajectory is introduced.

The basic calculation is

`d/dt f(γ(t)) = -‖∇f(γ(t))‖²`.

It makes `f` a Lyapunov function: `f ∘ γ` is antitone, and strictly antitone on any interval on
which the trajectory contains no critical point.  Integrating the calculation gives the energy
identity

`∫ t in a..b, ‖∇f(γ(t))‖² = f(γ(a)) - f(γ(b))`,

with no integrability hypothesis: the squared gradient is the nonnegative derivative of `-f ∘ γ`,
hence automatically integrable on compact time intervals.

In particular a periodic negative gradient trajectory is stationary in the dynamical sense that
its gradient vanishes at every point of the curve.  These statements are the entry point to the
gradient-flow, stable/unstable-manifold, and broken-trajectory constructions in the dynamical
route to Morse homology.

## Main results

* `TauCeti.isIntegralCurve_const_neg_gradient_iff`: the constant curves are precisely those at
  critical points of `f`.
* `IsIntegralCurveOn.hasDerivWithinAt_comp_neg_gradient`: derivative of `f` along a
  negative gradient trajectory.
* `IsIntegralCurveOn.antitoneOn_comp_neg_gradient` and
  `IsIntegralCurveOn.strictAntiOn_comp_neg_gradient`: Lyapunov monotonicity and strict
  descent away from critical points.
* `IsIntegralCurveOn.intervalIntegrable_norm_gradient_sq`: finite energy on compact time
  intervals.
* `IsIntegralCurveOn.integral_norm_gradient_sq_eq_sub` and
  `IsIntegralCurve.integral_norm_gradient_sq_eq_sub`: the energy identity.
* `IsIntegralCurve.gradient_eq_zero_of_eventually_const_value`: a trajectory on which
  `f` is eventually constant passes through critical points.
* `IsIntegralCurve.gradient_eq_zero_of_periodic` and
  `IsIntegralCurve.eq_of_periodic_neg_gradient`: a periodic negative gradient trajectory
  consists entirely of critical points and is constant.
* `Flow.IsNegativeGradient`: every orbit of a flow solves the negative gradient equation.
* `Flow.isNegativeGradient_iff`: the introduction and elimination rule for that predicate.
* `Flow.IsNegativeGradient.isIntegralCurve`: the orbit curve through a point, as an integral
  curve of the negative gradient field.
* `Flow.IsNegativeGradient.orbit_antitone`: the defining function is antitone along every orbit
  of its negative gradient flow.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 2.
-/

public section

open Filter Function InnerProductSpace MeasureTheory Set
open scoped Gradient Interval Topology

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {f : E → ℝ} {γ : ℝ → E} {s : Set ℝ} {t a b : ℝ}

namespace TauCeti

/-- A constant curve is an integral curve of the negative gradient field exactly when its value
is a critical point of `f`. -/
@[simp]
theorem isIntegralCurve_const_neg_gradient_iff {x : E} :
    IsIntegralCurve (fun _ : ℝ ↦ x) (fun _ y ↦ -∇ f y) ↔ ∇ f x = 0 := by
  constructor
  · intro h
    have hderiv := (h 0).deriv
    simpa only [deriv_const, neg_eq_zero] using hderiv.symm
  · intro hx
    exact isIntegralCurve_const fun _ ↦ by simp [hx]

end TauCeti

namespace IsIntegralCurveOn

/-- Along a negative gradient trajectory, the derivative of `f` is the negative squared norm of
its gradient.  This within-set form is the one used for trajectories on their maximal interval of
definition. -/
theorem hasDerivWithinAt_comp_neg_gradient
    (hγ : IsIntegralCurveOn γ (fun _ x ↦ -∇ f x) s) (ht : t ∈ s)
    (hf : DifferentiableAt ℝ f (γ t)) :
    HasDerivWithinAt (f ∘ γ) (-‖∇ f (γ t)‖ ^ 2) s t := by
  have hcomp := hf.hasFDerivAt.comp_hasDerivWithinAt t (hγ t ht)
  apply hcomp.congr_deriv
  rw [map_neg, ← inner_gradient_left, real_inner_self_eq_norm_sq]

/-- The value of `f` is antitone along a negative gradient trajectory on a convex time domain. -/
theorem antitoneOn_comp_neg_gradient
    (hγ : IsIntegralCurveOn γ (fun _ x ↦ -∇ f x) s) (hs : Convex ℝ s)
    (hf : ∀ t ∈ s, DifferentiableAt ℝ f (γ t)) :
    AntitoneOn (f ∘ γ) s := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos hs
  · exact fun t ht ↦ (hf t ht).continuousAt.comp_continuousWithinAt
      (hγ.continuousWithinAt ht)
  · intro t ht
    exact (hasDerivWithinAt_comp_neg_gradient hγ (interior_subset ht)
      (hf t (interior_subset ht))).mono interior_subset
  · intro t _
    exact neg_nonpos.mpr (sq_nonneg _)

/-- Away from critical points, the value of `f` is strictly decreasing along a negative gradient
trajectory on a convex time domain. -/
theorem strictAntiOn_comp_neg_gradient
    (hγ : IsIntegralCurveOn γ (fun _ x ↦ -∇ f x) s) (hs : Convex ℝ s)
    (hf : ∀ t ∈ s, DifferentiableAt ℝ f (γ t))
    (hcrit : ∀ t ∈ interior s, ∇ f (γ t) ≠ 0) :
    StrictAntiOn (f ∘ γ) s := by
  apply strictAntiOn_of_hasDerivWithinAt_neg hs
  · exact fun t ht ↦ (hf t ht).continuousAt.comp_continuousWithinAt
      (hγ.continuousWithinAt ht)
  · intro t ht
    exact (hasDerivWithinAt_comp_neg_gradient hγ (interior_subset ht)
      (hf t (interior_subset ht))).mono interior_subset
  · intro t ht
    exact neg_lt_zero.mpr (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr (hcrit t ht)))

/-- The squared gradient along a negative gradient trajectory is integrable on every compact
time interval, assuming only differentiability of the defining function along that interval: it
is the nonnegative derivative of `-f ∘ γ`. -/
theorem intervalIntegrable_norm_gradient_sq
    (a b : ℝ) (hγ : IsIntegralCurveOn γ (fun _ x ↦ -∇ f x) [[a, b]])
    (hf : ∀ t ∈ [[a, b]], DifferentiableAt ℝ f (γ t)) :
    IntervalIntegrable (fun t ↦ ‖∇ f (γ t)‖ ^ 2) volume a b := by
  have hd : ∀ t ∈ [[a, b]],
      HasDerivWithinAt (fun t ↦ -f (γ t)) (‖∇ f (γ t)‖ ^ 2) [[a, b]] t := fun t ht ↦ by
    simpa only [neg_neg, Function.comp_def] using
      (hasDerivWithinAt_comp_neg_gradient hγ ht (hf t ht)).fun_neg
  exact intervalIntegral.intervalIntegrable_deriv_of_nonneg
    (fun t ht ↦ (hd t ht).continuousWithinAt)
    (fun t ht ↦ (hd t ⟨ht.1.le, ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2))
    (fun t _ ↦ sq_nonneg _)

/-- **Energy identity for a negative gradient trajectory.**  Between two times of the trajectory's
time domain, the drop in `f` equals the integral of the squared norm of its gradient along the
trajectory.  No integrability hypothesis is needed: see `intervalIntegrable_norm_gradient_sq`. -/
theorem integral_norm_gradient_sq_eq_sub
    (hγ : IsIntegralCurveOn γ (fun _ x ↦ -∇ f x) s) (hsub : [[a, b]] ⊆ s)
    (hf : ∀ t ∈ [[a, b]], DifferentiableAt ℝ f (γ t)) :
    ∫ t in a..b, ‖∇ f (γ t)‖ ^ 2 = f (γ a) - f (γ b) := by
  have hd : ∀ t ∈ [[a, b]],
      HasDerivWithinAt (fun t ↦ -f (γ t)) (‖∇ f (γ t)‖ ^ 2) [[a, b]] t := fun t ht ↦ by
    simpa only [neg_neg, Function.comp_def] using
      (hasDerivWithinAt_comp_neg_gradient (hγ.mono hsub) ht (hf t ht)).fun_neg
  rw [intervalIntegral.integral_eq_sub_of_hasDeriv_right
    (fun t ht ↦ (hd t ht).continuousWithinAt)
    (fun t ht ↦ ((hd t ⟨ht.1.le, ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2)).hasDerivWithinAt)
    (intervalIntegrable_norm_gradient_sq a b (hγ.mono hsub) hf), neg_sub_neg]

end IsIntegralCurveOn

namespace IsIntegralCurve

/-- Along a global negative gradient trajectory, the derivative of `f` is the negative squared
norm of its gradient. -/
theorem hasDerivAt_comp_neg_gradient
    (hγ : IsIntegralCurve γ (fun _ x ↦ -∇ f x)) (hf : DifferentiableAt ℝ f (γ t)) :
    HasDerivAt (f ∘ γ) (-‖∇ f (γ t)‖ ^ 2) t :=
  ((hγ.isIntegralCurveOn univ).hasDerivWithinAt_comp_neg_gradient (mem_univ t) hf).hasDerivAt
    univ_mem

/-- The value of `f` is antitone along a global negative gradient trajectory. -/
theorem antitone_comp_neg_gradient
    (hγ : IsIntegralCurve γ (fun _ x ↦ -∇ f x)) (hf : ∀ t, DifferentiableAt ℝ f (γ t)) :
    Antitone (f ∘ γ) :=
  antitone_of_hasDerivAt_nonpos
    (fun t ↦ hasDerivAt_comp_neg_gradient hγ (hf t)) fun _ ↦ neg_nonpos.mpr (sq_nonneg _)

/-- If a global negative gradient trajectory contains no critical point, then the value of `f` is
strictly decreasing along it. -/
theorem strictAnti_comp_neg_gradient
    (hγ : IsIntegralCurve γ (fun _ x ↦ -∇ f x)) (hf : ∀ t, DifferentiableAt ℝ f (γ t))
    (hcrit : ∀ t, ∇ f (γ t) ≠ 0) :
    StrictAnti (f ∘ γ) :=
  strictAnti_of_hasDerivAt_neg (fun t ↦ hasDerivAt_comp_neg_gradient hγ (hf t))
    fun t ↦ neg_lt_zero.mpr (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr (hcrit t)))

/-- **Energy identity for a global negative gradient trajectory.**  The drop in `f` between two
times equals the integral of the squared norm of its gradient along the trajectory. -/
theorem integral_norm_gradient_sq_eq_sub
    (hγ : IsIntegralCurve γ (fun _ x ↦ -∇ f x)) (hf : ∀ t, DifferentiableAt ℝ f (γ t)) :
    ∫ t in a..b, ‖∇ f (γ t)‖ ^ 2 = f (γ a) - f (γ b) :=
  (hγ.isIntegralCurveOn univ).integral_norm_gradient_sq_eq_sub (subset_univ _) fun t _ ↦ hf t

/-- If the value of `f` is eventually constant along a global negative gradient trajectory, then
the gradient of `f` vanishes at the corresponding point. -/
theorem gradient_eq_zero_of_eventually_const_value
    (hγ : IsIntegralCurve γ (fun _ x ↦ -∇ f x)) (hf : DifferentiableAt ℝ f (γ t))
    {c : ℝ} (hval : ∀ᶠ u in 𝓝 t, f (γ u) = c) :
    ∇ f (γ t) = 0 := by
  have hzero : deriv (f ∘ γ) t = 0 := by
    have heq : (f ∘ γ) =ᶠ[𝓝 t] fun _ ↦ c := hval
    rw [heq.deriv_eq, deriv_const]
  rw [(hasDerivAt_comp_neg_gradient hγ hf).deriv] at hzero
  simpa only [neg_eq_zero, sq_eq_zero_iff, norm_eq_zero] using hzero

/-- A periodic negative gradient trajectory consists entirely of critical points.  Thus negative
gradient dynamics has no nonconstant periodic orbit. -/
theorem gradient_eq_zero_of_periodic
    (hγ : IsIntegralCurve γ (fun _ x ↦ -∇ f x)) (hf : ∀ t, DifferentiableAt ℝ f (γ t))
    {T : ℝ} (hT : 0 < T) (hper : Periodic γ T) (t : ℝ) :
    ∇ f (γ t) = 0 := by
  have hanti := antitone_comp_neg_gradient hγ hf
  refine gradient_eq_zero_of_eventually_const_value hγ (hf t) (c := f (γ t)) ?_
  filter_upwards [Icc_mem_nhds (sub_lt_self t hT) (lt_add_of_pos_right t hT)] with u hu
  apply le_antisymm
  · simpa only [Function.comp_apply, hper.sub_eq] using hanti hu.1
  · simpa only [Function.comp_apply, hper t] using hanti hu.2

/-- A periodic negative gradient trajectory is constant. -/
theorem eq_of_periodic_neg_gradient
    (hγ : IsIntegralCurve γ (fun _ x ↦ -∇ f x)) (hf : ∀ t, DifferentiableAt ℝ f (γ t))
    {T : ℝ} (hT : 0 < T) (hper : Periodic γ T) (t u : ℝ) :
    γ t = γ u := by
  apply is_const_of_deriv_eq_zero (fun v ↦ (hγ v).differentiableAt) _ t u
  intro v
  rw [(hγ v).deriv]
  exact neg_eq_zero.mpr (gradient_eq_zero_of_periodic hγ hf hT hper v)

end IsIntegralCurve

end

namespace Flow

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {φ : _root_.Flow ℝ E}

/-- A real flow is the **negative gradient flow** of `f` when each of its orbit curves solves
`γ' = -∇f(γ)`.  Regularity and uniqueness assumptions used to construct the flow remain
separate; this predicate records precisely the differential equation needed by its dynamical
consequences. -/
def IsNegativeGradient (φ : _root_.Flow ℝ E) (f : E → ℝ) : Prop :=
  ∀ x, IsIntegralCurve (fun t ↦ φ t x) (fun _ y ↦ -∇ f y)

/-- The introduction and elimination rule for a negative-gradient flow. -/
theorem isNegativeGradient_iff : IsNegativeGradient φ f ↔
    ∀ x, IsIntegralCurve (fun t ↦ φ t x) (fun _ y ↦ -∇ f y) :=
  Iff.rfl

/-- Each orbit curve of a negative gradient flow solves the negative gradient equation. -/
theorem IsNegativeGradient.isIntegralCurve (hφ : IsNegativeGradient φ f) (x : E) :
    IsIntegralCurve (fun t ↦ φ t x) (fun _ y ↦ -∇ f y) :=
  hφ x

/-- The defining function is antitone along every orbit of its negative gradient flow. -/
theorem IsNegativeGradient.orbit_antitone (hφ : IsNegativeGradient φ f) (x : E)
    (hf : ∀ t, DifferentiableAt ℝ f (φ t x)) :
    Antitone (fun t ↦ f (φ t x)) := by
  simpa only [Function.comp_def] using
    (hφ x).antitone_comp_neg_gradient hf

end Flow
