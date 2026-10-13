/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Exponential
import Mathlib.Analysis.ODE.ExistUnique

/-!
# Inhomogeneous equations for bounded linear operators

A bounded operator on a real Banach space and a continuous forcing term give a unique global
solution of `u' = B u + f`, with any prescribed initial value. This supplies the ODE existence
step for autonomous Galerkin approximations of evolution equations. The solution is given by
the integrating factor formula `exp (t B) (exp (-t₀ B) x + ∫ₜ₀ᵗ exp (-s B) f(s) ds)`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §7.1.2.
-/

public section

open NormedSpace MeasureTheory

namespace ContinuousLinearMap

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- A bounded linear ODE with continuous forcing has a unique global solution with any
prescribed initial value at any time `t₀`. -/
theorem existsUnique_hasDerivAt_add (B : X →L[ℝ] X) {f : ℝ → X} (hf : Continuous f)
    (x : X) (t₀ : ℝ) :
    ∃! u : ℝ → X, u t₀ = x ∧ ∀ t, HasDerivAt u (B (u t) + f t) t := by
  let g : ℝ → X := fun s ↦ exp ((-s) • B) (f s)
  have hg : Continuous g :=
    ((differentiable_exp_smul_const ℝ B).continuous.comp continuous_neg).clm_apply hf
  let u : ℝ → X := fun t ↦ exp (t • B) (exp ((-t₀) • B) x + ∫ s in t₀..t, g s)
  have hinv (t : ℝ) (z : X) : exp (t • B) (exp ((-t) • B) z) = z := by
    rw [← comp_apply, ← TauCeti.exp_add_smul]
    simp
  have hcomm (t : ℝ) (z : X) : exp (t • B) (B z) = B (exp (t • B) z) := by
    exact congrArg (fun C : X →L[ℝ] X ↦ C z)
      (((Commute.refl B).smul_left t).exp_left.eq)
  have hu (t : ℝ) : HasDerivAt u (B (u t) + f t) t := by
    have hi := intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable t₀ t)
      hg.aestronglyMeasurable.stronglyMeasurableAtFilter hg.continuousAt
    have h := (hasDerivAt_exp_smul_const' B t).clm_apply
      ((hasDerivAt_const t (exp ((-t₀) • B) x)).add hi)
    simpa only [u, g, Pi.add_apply, zero_add, mul_apply_eq_comp, hcomm, hinv] using h
  have hu₀ : u t₀ = x := by
    simpa only [u, intervalIntegral.integral_same, add_zero] using hinv t₀ x
  refine ⟨u, ⟨hu₀, hu⟩, ?_⟩
  intro v hv
  exact ODE_solution_unique_univ (v := fun t z ↦ B z + f t) (s := fun _ ↦ Set.univ)
    (fun t ↦ lipschitzOnWith_iff_dist_le_mul.2 fun z _ w _ ↦ by
      simpa only [dist_add_right] using B.lipschitzWith.dist_le_mul z w)
    (fun t ↦ ⟨hv.2 t, Set.mem_univ _⟩) (fun t ↦ ⟨hu t, Set.mem_univ _⟩)
    (hv.1.trans hu₀.symm)

end ContinuousLinearMap
