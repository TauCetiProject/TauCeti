/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.GradientFlow
public import TauCeti.Analysis.Calculus.TangentCone.Basic
public import TauCeti.Dynamics.Flow.OfLipschitz
import TauCeti.Analysis.Calculus.Gradient
import TauCeti.Dynamics.Flow.Variational

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
  globally `C²` function, this flow is `C¹` jointly and at each fixed time
  (`TauCeti.differentiable_negativeGradientFlow_apply`: each time map is differentiable).
* `TauCeti.hasDerivAt_fderiv_negativeGradientFlow`: the variational equation
  `d/dt Dφₜ(x) = -D(∇f)(φₜ x) ∘ Dφₜ(x)`.
* `TauCeti.fderiv_negativeGradientFlow_apply_gradient`: `Dφₜ(x)(∇f x) = ∇f(φₜ x)`.
* `TauCeti.continuous_fderiv_negativeGradientFlow_neg`: `σ ↦ Dφ_{-σ}(φ_σ x)` is continuous.
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
* `TauCeti.negativeGradientFlow_apply_eq_of_gradient_eq`: negative-gradient flows agree at time `t`
  on `y` when the gradients agree along the orbit segment from `0` to `t`.
* `TauCeti.forall_negativeGradientFlow_eq_self_iff`: its rest points are the zeros of `∇ f`.
* `TauCeti.gradient_negativeGradientFlow_eq_zero_iff`: an orbit meets a zero of `∇ f` only if it
  starts at one.
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

/-- For a globally `C²` function, each time-`t` map of the negative-gradient flow is
differentiable. -/
theorem differentiable_negativeGradientFlow_apply (f : E → ℝ) (hf : LipschitzWith K (∇ f))
    (hfs : ContDiff ℝ 2 f) (t : ℝ) : Differentiable ℝ (negativeGradientFlow f hf t) :=
  (contDiff_negativeGradientFlow_apply f hf hfs t).differentiable one_ne_zero

/-- **The variational equation of the negative-gradient flow**: for a globally `C²` function,
`d/dt Dφₜ(x) = -D(∇f)(φₜ x) ∘ Dφₜ(x)`. -/
theorem hasDerivAt_fderiv_negativeGradientFlow (f : E → ℝ) (hf : LipschitzWith K (∇ f))
    (hfs : ContDiff ℝ 2 f) (x : E) (t : ℝ) :
    HasDerivAt (fun τ ↦ fderiv ℝ (negativeGradientFlow f hf τ) x)
      (-(fderiv ℝ (∇ f) (negativeGradientFlow f hf t x)).comp
        (fderiv ℝ (negativeGradientFlow f hf t) x)) t := by
  have h := hasDerivAt_fderiv_flowOfLipschitz hf.neg
    (hfs.gradient_right (m := 1) (by norm_num)).neg x t
  rw [fderiv_neg, ContinuousLinearMap.neg_comp] at h
  exact h

/-- **The negative gradient flow is a negative gradient flow**: each of its orbits solves
`γ' = -∇f(γ)`. -/
theorem isNegativeGradient_negativeGradientFlow (f : E → ℝ) (hf : LipschitzWith K (∇ f)) :
    Flow.IsNegativeGradient (negativeGradientFlow f hf) f :=
  Flow.isNegativeGradient_iff.2 fun x ↦ isIntegralCurve_flowOfLipschitz hf.neg x

/-- At time `0`, the orbit of `y` under the negative-gradient flow has velocity `-∇f y`. -/
theorem hasDerivAt_negativeGradientFlow_zero (f : E → ℝ) (hf : LipschitzWith K (∇ f)) (y : E) :
    HasDerivAt (fun t ↦ negativeGradientFlow f hf t y) (-∇ f y) 0 := by
  have := (isNegativeGradient_negativeGradientFlow f hf).isIntegralCurve y 0
  beta_reduce at this
  rwa [Flow.map_zero_apply] at this

/-- **The flow direction is tangent to an invariant set**: for a set `S` invariant under the
negative-gradient flow and a point `y ∈ S`, the velocity `-∇ f y` lies in the tangent cone of `S`
at `y`. -/
theorem neg_gradient_mem_tangentConeAt_of_isInvariant (f : E → ℝ) (hf : LipschitzWith K (∇ f))
    {S : Set E} (hS : IsInvariant (negativeGradientFlow f hf) S) {y : E} (hy : y ∈ S) :
    -∇ f y ∈ tangentConeAt ℝ S y := by
  simpa only [Flow.map_zero_apply] using
    (hasDerivAt_negativeGradientFlow_zero f hf y).mem_tangentConeAt (S := S)
      (Filter.Eventually.of_forall fun t ↦ hS t hy)

/-- **The derivative of the negative-gradient flow carries the gradient along**:
`Dφₜ(x) (∇f x) = ∇f (φₜ x)`. -/
theorem fderiv_negativeGradientFlow_apply_gradient (f : E → ℝ) (hf : LipschitzWith K (∇ f))
    (hfs : ContDiff ℝ 2 f) (t : ℝ) (x : E) :
    fderiv ℝ (negativeGradientFlow f hf t) x (∇ f x) = ∇ f (negativeGradientFlow f hf t x) := by
  have := Flow.fderiv_apply_of_hasDerivAt (hasDerivAt_negativeGradientFlow_zero f hf x)
    (hasDerivAt_negativeGradientFlow_zero f hf _)
    (differentiable_negativeGradientFlow_apply f hf hfs t x)
  rwa [map_neg, neg_inj] at this

/-- The inverse `Dφ_{-σ}(φ_σ x)` of the derivative of the negative-gradient flow along an orbit is
continuous in `σ`. -/
theorem continuous_fderiv_negativeGradientFlow_neg (f : E → ℝ) (hf : LipschitzWith K (∇ f))
    (hfs : ContDiff ℝ 2 f) (x : E) :
    Continuous fun σ ↦
      fderiv ℝ (negativeGradientFlow f hf (-σ)) (negativeGradientFlow f hf σ x) :=
  continuous_fderiv_flowOfLipschitz_neg hf.neg (hfs.gradient_right (m := 1) (by norm_num)).neg x

/-- **Every global negative gradient trajectory is an orbit** of the negative gradient flow. -/
theorem eq_negativeGradientFlow (f : E → ℝ) (hf : LipschitzWith K (∇ f)) {γ : ℝ → E}
    (hγ : IsIntegralCurve γ fun _ y ↦ -∇ f y) (t : ℝ) :
    γ t = negativeGradientFlow f hf t (γ 0) :=
  eq_flowOfLipschitz hf.neg hγ t

/-- **Negative-gradient flows agree where the gradients agree.** If the gradients of `g` and `f`
coincide along the orbit segment `{φ_τ y | τ ∈ [[0, t]]}` of the negative-gradient flow of `f`,
then the negative-gradient flow of `g` sends `y` at time `t` to the same point. -/
theorem negativeGradientFlow_apply_eq_of_gradient_eq {g : E → ℝ} {K' : ℝ≥0}
    (hg : LipschitzWith K' (∇ g)) (hf : LipschitzWith K (∇ f)) {y : E} {t : ℝ}
    (hfg : ∀ τ ∈ uIcc 0 t,
      ∇ g (negativeGradientFlow f hf τ y) = ∇ f (negativeGradientFlow f hf τ y)) :
    negativeGradientFlow g hg t y = negativeGradientFlow f hf t y := by
  rw [negativeGradientFlow, negativeGradientFlow]
  exact flowOfLipschitz_apply_eq_of_eqOn hg.neg hf.neg fun τ hτ ↦ congrArg Neg.neg (hfg τ hτ)

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

/-- **An orbit meets the critical points only if it is constant**: a point of the orbit of `x`
under the negative-gradient flow is a zero of `∇ f` exactly when `x` is. -/
@[simp]
theorem gradient_negativeGradientFlow_eq_zero_iff (f : E → ℝ) (hf : LipschitzWith K (∇ f))
    (x : E) (t : ℝ) : ∇ f (negativeGradientFlow f hf t x) = 0 ↔ ∇ f x = 0 := by
  refine ⟨fun h0 ↦ ?_, fun h0 ↦ by rwa [(forall_negativeGradientFlow_eq_self_iff f hf x).2 h0 t]⟩
  have hfix := (forall_negativeGradientFlow_eq_self_iff f hf _).2 h0 (-t)
  rw [← Flow.map_add, neg_add_cancel, Flow.map_zero_apply] at hfix
  exact hfix ▸ h0

/-- **Lyapunov descent along the negative gradient flow**: a function decreases along any orbit
on which it is differentiable.  This is the point at which differentiability of `f` is needed, the
construction of the flow itself only seeing the vector field `-∇ f`. -/
theorem negativeGradientFlow_orbit_antitone (f : E → ℝ) (hf : LipschitzWith K (∇ f))
    (x : E) (hf' : ∀ t, DifferentiableAt ℝ f (negativeGradientFlow f hf t x)) :
    Antitone fun t ↦ f (negativeGradientFlow f hf t x) :=
  (isNegativeGradient_negativeGradientFlow f hf).orbit_antitone x hf'

end TauCeti
