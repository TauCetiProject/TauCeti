/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.GradientFlow
public import TauCeti.Dynamics.Flow.OfLipschitz
import TauCeti.Analysis.Calculus.Gradient

/-!
# Existence of the negative gradient flow

The dynamical description of Morse theory reads its trajectory spaces off a *flow*: stable and
unstable sets, and the Lyapunov theory of a decreasing function along trajectories, are statements
about a `Flow.IsNegativeGradient` flow. This file produces such a flow for every function whose
gradient is globally Lipschitz, by feeding `-∇ f` to `TauCeti.flowOfLipschitz`.

Global Lipschitz continuity of `∇ f` is a sufficient hypothesis for the trajectories to exist for
all time; it holds for instance whenever `f` is `C²` with a bounded second derivative, and in
particular for the split quadratic model.

Throughout, `∇ f` is Mathlib's gradient: a function defined for every `f`, taking the value `0`
wherever `f` is not differentiable.  What is constructed below is therefore the flow of the vector
field `-∇ f`, and no differentiability of `f` is assumed for it, exactly as the predicate
`Flow.IsNegativeGradient` it witnesses assumes none.  Differentiability of `f` is what makes that
field the gradient field of `f`, and it enters where the flow is used as a *gradient* flow rather
than as the flow of a Lipschitz field: `TauCeti.negativeGradientFlow_orbit_antitone` records
Lyapunov descent along any orbit on which `f` is differentiable.

## Main declarations

* `TauCeti.negativeGradientFlow`: the negative gradient flow of a function with globally Lipschitz
  gradient.
* `TauCeti.contDiff_negativeGradientFlow` and `TauCeti.contDiff_negativeGradientFlow_apply`: for a
  globally `C²` function, this flow is `C¹` jointly and at each fixed time.
* `TauCeti.isNegativeGradient_negativeGradientFlow`: it is a negative gradient flow of `f`.
* `TauCeti.eq_negativeGradientFlow`: every global negative gradient trajectory is one of its
  orbits.
* `TauCeti.isIntegralCurve_centeredNegativeGradientFlow`: an orbit written in displacement
  coordinates solves the centred negative-gradient equation.
* `TauCeti.flowOfLipschitz_centeredNegativeGradient_apply`: identifies the flow of the centred
  field with the translated negative-gradient flow.
* `TauCeti.eq_centeredNegativeGradientFlow_of_isIntegralCurveOn`: uniqueness in displacement
  coordinates on a time set containing the interval from zero to the chosen time.
* `TauCeti.negativeGradientFlow_congr`: it does not depend on the chosen Lipschitz bound.
* `TauCeti.forall_negativeGradientFlow_eq_self_iff`: its rest points are the zeros of `∇ f`.
* `TauCeti.negativeGradientFlow_orbit_antitone`: `f` decreases along an orbit on which it is
  differentiable.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 2.
-/

public section

open InnerProductSpace Set
open scoped Gradient NNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {f : E → ℝ} {K : ℝ≥0}

/-- **The negative gradient flow** of a function whose gradient is globally Lipschitz.

This is the flow of the vector field `-∇ f`.  For a differentiable `f` that field is the negative
gradient field and this is the negative gradient flow in the usual sense; for an `f` that is not
differentiable everywhere it is the flow of Mathlib's totalized gradient field, which is the
object the hypothesis `LipschitzWith K (∇ f)` speaks about. -/
noncomputable def negativeGradientFlow (f : E → ℝ) {K : ℝ≥0} (hf : LipschitzWith K (∇ f)) :
    _root_.Flow ℝ E :=
  flowOfLipschitz (fun x ↦ -∇ f x) hf.neg

/-- **The negative-gradient flow of a globally `C²` function is `C¹`**, jointly in time and
the initial condition. The global Lipschitz hypothesis supplies completeness of every orbit, while
the two derivatives of `f` make its negative-gradient field `C¹`. -/
theorem contDiff_negativeGradientFlow (f : E → ℝ) (hf : LipschitzWith K (∇ f))
    (hfs : ContDiff ℝ 2 f) :
    ContDiff ℝ 1 (Function.uncurry (negativeGradientFlow f hf)) := by
  apply contDiff_flowOfLipschitz 0 (fun x ↦ -∇ f x) hf.neg
  exact (hfs.gradient_right (m := 1) (by norm_num)).neg

/-- At every fixed time, the negative-gradient flow of a globally `C²` function is `C¹` in its
initial condition. -/
theorem contDiff_negativeGradientFlow_apply (f : E → ℝ) (hf : LipschitzWith K (∇ f))
    (hfs : ContDiff ℝ 2 f) (t : ℝ) :
    ContDiff ℝ 1 (negativeGradientFlow f hf t) := by
  apply contDiff_flowOfLipschitz_apply 0 (fun x ↦ -∇ f x) hf.neg
  exact (hfs.gradient_right (m := 1) (by norm_num)).neg

/-- **The negative gradient flow is a negative gradient flow**: each of its orbits solves
`γ' = -∇f(γ)`. -/
theorem isNegativeGradient_negativeGradientFlow (f : E → ℝ) (hf : LipschitzWith K (∇ f)) :
    Flow.IsNegativeGradient (negativeGradientFlow f hf) f :=
  Flow.isNegativeGradient_iff.2 fun x ↦ isIntegralCurve_flowOfLipschitz hf.neg x

/-- **Every global negative gradient trajectory is an orbit** of the negative gradient flow. -/
theorem eq_negativeGradientFlow (f : E → ℝ) (hf : LipschitzWith K (∇ f)) {γ : ℝ → E}
    (hγ : IsIntegralCurve γ fun _ y ↦ -∇ f y) (t : ℝ) :
    γ t = negativeGradientFlow f hf t (γ 0) :=
  eq_flowOfLipschitz hf.neg hγ t

/-- Translating the negative-gradient field to displacement coordinates preserves its Lipschitz
constant. -/
theorem lipschitzWith_centeredNegativeGradient (hf : LipschitzWith K (∇ f)) (x : E) :
    LipschitzWith K (fun z ↦ (-∇ f) (x + z)) := by
  intro z w
  simpa only [edist_dist, dist_add_left] using hf.neg (x + z) (x + w)

/-- A negative-gradient orbit, written in displacement coordinates about `x`, solves the centred
negative-gradient equation. -/
theorem isIntegralCurve_centeredNegativeGradientFlow (hf : LipschitzWith K (∇ f)) (x z : E) :
    IsIntegralCurve
      (fun t ↦ negativeGradientFlow f hf t (x + z) - x)
      (fun _ w ↦ (-∇ f) (x + w)) := by
  intro t
  have ht := (isNegativeGradient_negativeGradientFlow f hf).isIntegralCurve (x + z) t
  have harg : x + (negativeGradientFlow f hf t (x + z) - x) =
      negativeGradientFlow f hf t (x + z) := by abel
  simpa only [harg, Pi.neg_apply] using ht.sub_const x

/-- The flow of the centred negative-gradient field is the negative-gradient flow translated to
displacement coordinates. -/
theorem flowOfLipschitz_centeredNegativeGradient_apply (hf : LipschitzWith K (∇ f))
    (x z : E) (t : ℝ) :
    flowOfLipschitz (fun w ↦ (-∇ f) (x + w))
        (lipschitzWith_centeredNegativeGradient hf x) t z =
      negativeGradientFlow f hf t (x + z) - x := by
  simpa only [_root_.Flow.map_zero_apply, add_sub_cancel_left] using
    (eq_flowOfLipschitz (lipschitzWith_centeredNegativeGradient hf x)
      (isIntegralCurve_centeredNegativeGradientFlow hf x z) t).symm

/-- A centred negative-gradient trajectory on a time set containing the interval between zero and
`t` is the corresponding translated orbit of the global negative-gradient flow at `t`. -/
theorem eq_centeredNegativeGradientFlow_of_isIntegralCurveOn
    (hf : LipschitzWith K (∇ f)) {x z : E} {y : ℝ → E} {s : Set ℝ}
    (hy : IsIntegralCurveOn y (fun _ w ↦ (-∇ f) (x + w)) s)
    (hy0 : y 0 = z) {t : ℝ} (hst : uIcc 0 t ⊆ s) :
    y t = negativeGradientFlow f hf t (x + z) - x := by
  have hv := lipschitzWith_centeredNegativeGradient hf x
  rw [eq_flowOfLipschitz_of_isIntegralCurveOn hv hy hst, hy0,
    flowOfLipschitz_centeredNegativeGradient_apply]

/-- **Independence of the Lipschitz bound.** Two Lipschitz witnesses for `∇ f`, with possibly
different constants, produce the same negative gradient flow. -/
theorem negativeGradientFlow_congr (f : E → ℝ) {K' : ℝ≥0} (hf : LipschitzWith K (∇ f))
    (hf' : LipschitzWith K' (∇ f)) : negativeGradientFlow f hf = negativeGradientFlow f hf' :=
  flowOfLipschitz_congr hf.neg hf'.neg

/-- **The rest points of the negative gradient flow are the zeros of `∇ f`**, that is, the
critical points of a differentiable `f`. -/
theorem forall_negativeGradientFlow_eq_self_iff (f : E → ℝ) (hf : LipschitzWith K (∇ f)) (x : E) :
    (∀ t, negativeGradientFlow f hf t x = x) ↔ ∇ f x = 0 := by
  rw [negativeGradientFlow, forall_flowOfLipschitz_eq_self_iff, neg_eq_zero]

/-- **Lyapunov descent along the negative gradient flow**: a function decreases along any orbit
on which it is differentiable.  This is the point at which differentiability of `f` is needed, the
construction of the flow itself only seeing the vector field `-∇ f`. -/
theorem negativeGradientFlow_orbit_antitone (f : E → ℝ) (hf : LipschitzWith K (∇ f))
    (x : E) (hf' : ∀ t, DifferentiableAt ℝ f (negativeGradientFlow f hf t x)) :
    Antitone fun t ↦ f (negativeGradientFlow f hf t x) :=
  (isNegativeGradient_negativeGradientFlow f hf).orbit_antitone x hf'

end TauCeti
