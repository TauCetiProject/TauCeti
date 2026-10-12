/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Exponential
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Inhomogeneous equations for bounded linear operators

A bounded operator on a real Banach space and a continuous forcing term give a unique global
solution of `u' = B u + f`, with any prescribed initial value. This supplies the ODE existence
step for autonomous Galerkin approximations of evolution equations. The solution is given by
the integrating factor formula `exp (t B) (x + ∫₀ᵗ exp (-s B) f(s) ds)`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §7.1.2.
-/

public section

open NormedSpace MeasureTheory

namespace ContinuousLinearMap

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- A bounded linear ODE with continuous forcing has a unique global solution with any
prescribed initial value at time zero. -/
theorem existsUnique_hasDerivAt_add (B : X →L[ℝ] X) {f : ℝ → X} (hf : Continuous f) (x : X) :
    ∃! u : ℝ → X, u 0 = x ∧ ∀ t, HasDerivAt u (B (u t) + f t) t := by
  let g : ℝ → X := fun s ↦ exp ((-s) • B) (f s)
  have hg : Continuous g :=
    ((differentiable_exp_smul_const ℝ B).continuous.comp continuous_neg).clm_apply hf
  let u : ℝ → X := fun t ↦ exp (t • B) (x + ∫ s in (0 : ℝ)..t, g s)
  have hinv (t : ℝ) (z : X) : exp (t • B) (exp ((-t) • B) z) = z := by
    rw [← comp_apply, ← TauCeti.exp_add_smul]
    simp
  have hcomm (t : ℝ) (z : X) : exp (t • B) (B z) = B (exp (t • B) z) := by
    exact congrArg (fun C : X →L[ℝ] X ↦ C z)
      (((Commute.refl B).smul_left t).exp_left.eq)
  have hu (t : ℝ) : HasDerivAt u (B (u t) + f t) t := by
    have hi := intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable 0 t)
      hg.aestronglyMeasurable.stronglyMeasurableAtFilter hg.continuousAt
    have h := (hasDerivAt_exp_smul_const' B t).clm_apply ((hasDerivAt_const t x).add hi)
    simpa only [u, g, Pi.add_apply, zero_add, mul_apply_eq_comp, hcomm, hinv] using h
  refine ⟨u, ⟨by simp [u], hu⟩, ?_⟩
  intro v hv
  let w : ℝ → X := fun t ↦ exp ((-t) • B) (v t - u t)
  have hw (t : ℝ) : HasDerivAt w 0 t := by
    have hd : HasDerivAt (fun s ↦ v s - u s) (B (v t - u t)) t := by
      convert (hv.2 t).sub (hu t) using 1
      simp [map_sub]
    have he := (hasDerivAt_exp_smul_const' B (-t)).scomp t
      (hasDerivAt_neg t)
    have h := he.clm_apply hd
    simpa only [w, Function.comp_def, mul_apply_eq_comp, neg_one_smul, neg_apply, hcomm,
      neg_add_cancel] using h
  have hw0 (t : ℝ) : w t = 0 := by
    rw [is_const_of_deriv_eq_zero (fun s ↦ (hw s).differentiableAt)
      (fun s ↦ (hw s).deriv) t 0]
    simp [w, hv.1, u]
  funext t
  have h := congrArg (fun z ↦ exp (t • B) z) (hw0 t)
  simpa only [w, hinv, map_zero, sub_eq_zero] using h

end ContinuousLinearMap
