/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Algebra
public import TauCeti.Analysis.SpecialFunctions.Exponential

/-!
# Naturality of the derivative of the exponential

Continuous algebra homomorphisms intertwine the derivatives of the exponential. In particular,
this transports the matrix derivative through a change of basis without differentiating a
second exponential series.
-/

public section

namespace ContinuousAlgHom

open NormedSpace

variable {𝕜 A B : Type*} [NontriviallyNormedField 𝕜] [CharZero 𝕜]
  [ContinuousSMul ℚ 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A] [CompleteSpace A]
  [NormedRing B] [NormedAlgebra 𝕜 B] [CompleteSpace B]

/-- Continuous algebra homomorphisms commute with the derivative of the exponential. -/
theorem map_expFDeriv (f : A →A[𝕜] B) (x y : A) :
    f (TauCeti.expFDeriv 𝕜 x y) = TauCeti.expFDeriv 𝕜 (f x) (f y) := by
  have heq : (fun z ↦ exp (f z)) = fun z ↦ f (exp z) := by
    funext z
    exact (NormedSpace.map_exp_of_mem_ball (𝕂 := 𝕜) f f.continuous z (by
      rw [Metric.mem_eball, expSeries_radius_eq_top]
      exact edist_lt_top _ _)).symm
  have hleft := (TauCeti.hasFDerivAt_exp (𝕂 := 𝕜) (f x)).comp x
    f.toContinuousLinearMap.hasFDerivAt
  have hright := f.toContinuousLinearMap.hasFDerivAt.comp x
    (TauCeti.hasFDerivAt_exp (𝕂 := 𝕜) x)
  simp only [Function.comp_def, coe_toContinuousLinearMap] at hleft hright
  rw [heq] at hleft
  exact (congrArg (fun L : A →L[𝕜] B ↦ L y) (hleft.unique hright)).symm

end ContinuousAlgHom
