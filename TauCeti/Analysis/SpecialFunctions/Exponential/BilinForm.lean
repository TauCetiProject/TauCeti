/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
public import TauCeti.Analysis.Normed.Algebra.Basic

/-!
# Exponentials of skew-adjoint operators preserve bilinear forms

The exponential `exp B` of a continuous endomorphism `B` of a real Banach space is a continuous
linear automorphism with inverse `exp (-B)`. If `B` is skew-adjoint for a real bilinear form `β`
on a finite-dimensional space, `β (B v) w + β v (B w) = 0`, then `exp B` preserves `β`: the
derivative of `t ↦ β (exp (t B) v) (exp (t B) w)` vanishes. For a symplectic form this says that
the exponential of an infinitesimally symplectic endomorphism is symplectic.

## Main declarations

* `ContinuousLinearMap.expEquiv`: `exp B` as a continuous linear automorphism.
* `LinearMap.IsSkewAdjoint.apply_exp_apply_exp`: the exponential of a `β`-skew-adjoint
  endomorphism preserves `β`.
-/

public section

noncomputable section

open NormedSpace

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

attribute [local instance] TauCeti.normedAlgebraRatOfReal

namespace ContinuousLinearMap

variable [CompleteSpace V]

/-- The exponential `exp B` of a continuous endomorphism of a real Banach space, as a continuous
linear automorphism with inverse `exp (-B)`. -/
@[expose]
def expEquiv (B : V →L[ℝ] V) : V ≃L[ℝ] V :=
  .equivOfInverse' (exp B) (exp (-B))
    (by rw [← mul_def, ← exp_add_of_commute (Commute.refl B).neg_right, add_neg_cancel, exp_zero,
      one_def])
    (by rw [← mul_def, ← exp_add_of_commute (Commute.refl B).neg_left, neg_add_cancel, exp_zero,
      one_def])

@[simp]
theorem expEquiv_apply (B : V →L[ℝ] V) (v : V) : B.expEquiv v = exp B v :=
  (rfl)

@[simp]
theorem expEquiv_symm_apply (B : V →L[ℝ] V) (v : V) : B.expEquiv.symm v = exp (-B) v :=
  (rfl)

end ContinuousLinearMap

/-- The exponential of an endomorphism that is skew-adjoint for a real bilinear form `β`
preserves `β`. For a symplectic form this says that the exponential of an infinitesimally
symplectic endomorphism is symplectic. -/
theorem LinearMap.IsSkewAdjoint.apply_exp_apply_exp [FiniteDimensional ℝ V]
    {β : LinearMap.BilinForm ℝ V} {B : V →L[ℝ] V} (hB : β.IsSkewAdjoint B) (v w : V) :
    β (exp B v) (exp B w) = β v w := by
  let βc := β.toContinuousBilinearMap
  have hβc (v w : V) : βc v w = β v w := LinearMap.toContinuousBilinearMap_apply _ _ _
  have hB0 (a b : V) : β (B a) b + β a (B b) = 0 := by
    have := hB a b
    rw [Pi.neg_apply, map_neg] at this
    linarith
  let f : ℝ → ℝ := fun t => βc (exp (t • B) v) (exp (t • B) w)
  have hexp (t : ℝ) (u : V) : HasDerivAt (fun s : ℝ => exp (s • B) u) (B (exp (t • B) u)) t := by
    simpa using (hasDerivAt_exp_smul_const' B t).clm_apply (hasDerivAt_const t u)
  have hf (t : ℝ) : HasDerivAt f 0 t := by
    have := βc.hasDerivAt_of_bilinear (fun _ => hexp t v) (fun _ => hexp t w)
    rwa [hβc, hβc, add_comm, hB0] at this
  have := is_const_of_deriv_eq_zero (fun t => (hf t).differentiableAt) (fun t => (hf t).deriv) 1 0
  simpa [f, hβc] using this
