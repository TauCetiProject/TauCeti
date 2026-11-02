/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import TauCeti.Geometry.Sphere.Circle

/-!
# Angles as planar unit vectors

`circleSphereHomeomorph` identifies `AddCircle (2 * π)` with the unit sphere in the
Euclidean plane through cosine and sine. It is complex exponentiation followed by the inverse
of `TauCeti.EuclideanSpace.sphereHomeomorphCircle`, using real orthonormal coordinates.
The inner product of two such vectors is the cosine of their angle difference, allowing
circular kernels to be read as kernels on the planar sphere.
-/

public section

noncomputable section

open Metric Set Real
open scoped InnerProductSpace

namespace TauCeti

/-- Cosine and sine identify the additive circle with the unit sphere in the Euclidean plane. -/
def circleSphereHomeomorph : AddCircle (2 * π) ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 :=
  (AddCircle.homeomorphCircle' : AddCircle (2 * π) ≃ₜ sphere (0 : ℂ) 1).trans
    EuclideanSpace.sphereHomeomorphCircle.symm

/-- The planar parametrization is complex exponentiation followed by real orthonormal
coordinates. -/
theorem coe_circleSphereHomeomorph (t : AddCircle (2 * π)) :
    (circleSphereHomeomorph t : EuclideanSpace ℝ (Fin 2)) =
      Complex.orthonormalBasisOneI.repr (Real.Angle.toCircle t) :=
  EuclideanSpace.coe_sphereHomeomorphCircle_symm_apply (Real.Angle.toCircle t)

/-- At a real angle, the planar sphere parametrization has coordinates cosine and sine. -/
@[simp]
theorem circleSphereHomeomorph_coe (t : ℝ) :
    (circleSphereHomeomorph t : EuclideanSpace ℝ (Fin 2)) =
      WithLp.toLp 2 ![cos t, sin t] := by
  have ht : ((Real.Angle.toCircle (t : AddCircle (2 * π))) : ℂ) =
      (cos t : ℂ) + sin t * Complex.I := by
    simpa only [Real.Angle.cos_coe, Real.Angle.sin_coe] using!
      Real.Angle.coe_toCircle (t : Real.Angle)
  rw [coe_circleSphereHomeomorph, WithLp.ext_iff, Complex.orthonormalBasisOneI_repr_apply, ht]
  simp [Complex.cos_ofReal_re, Complex.sin_ofReal_re]

/-- The inner product of the two parametrized directions is the cosine of their angle difference. -/
@[simp]
theorem inner_circleSphereHomeomorph (a b : AddCircle (2 * π)) :
    ⟪(circleSphereHomeomorph a : EuclideanSpace ℝ (Fin 2)),
      (circleSphereHomeomorph b : EuclideanSpace ℝ (Fin 2))⟫_ℝ =
      cos_periodic.lift (b - a) := by
  induction a using QuotientAddGroup.induction_on with | H a =>
  induction b using QuotientAddGroup.induction_on with | H b =>
  rw [← AddCircle.coe_sub, Function.Periodic.lift_coe]
  simp [EuclideanSpace.inner_eq_star_dotProduct, cos_sub, mul_comm]

end TauCeti
