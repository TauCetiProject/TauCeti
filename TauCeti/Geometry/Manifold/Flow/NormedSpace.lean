/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Flow.Complete
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Translation and rotation as maximal flows

The maximal flow of a constant field on a real normed space is translation. On the real plane
`ℝ × ℝ`, the field `(x, y) ↦ (-ω y, ω x)` generates counterclockwise rotation through angle
`ω t`. Both fields are complete, so these formulas describe the actual maximal flows at every
time, not just locally or at points where their totalized values happen to be defined.

The statements use the standard model `𝓘(ℝ, E)`, identifying its tangent fibers with `E`.
No completeness or finite-dimensionality assumption is needed for translation.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 9 (integral curves and flows).
-/

public section

open Set
open scoped Manifold

namespace TauCeti

section Translation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A line with velocity `v` is an integral curve of the constant field `v`. -/
theorem isMIntegralCurve_translation (v x : E) :
    IsMIntegralCurve (I := 𝓘(ℝ, E)) (fun t : ℝ ↦ x + t • v) (fun _ ↦ v) := by
  intro t
  have h : HasDerivAt (fun s : ℝ ↦ x + s • v) v t := by
    simpa only [id_eq, one_smul] using ((hasDerivAt_id t).smul_const v).const_add x
  exact h.hasFDerivAt.hasMFDerivAt

/-- Every constant vector field on a real normed space is complete. -/
theorem isCompleteVectorField_const (v : E) :
    IsCompleteVectorField (I := 𝓘(ℝ, E)) (fun _ : E ↦ v) := by
  refine (isCompleteVectorField_iff_exists_isMIntegralCurve (I := 𝓘(ℝ, E))
    (contMDiff_vectorSpace_iff_contDiff.mpr contDiff_const)).mpr fun x ↦ ?_
  exact ⟨fun t ↦ x + t • v, by simp, isMIntegralCurve_translation v x⟩

/-- The maximal flow of a constant field is translation by time times its velocity. -/
@[simp]
theorem flowOf_const (v : E) (t : ℝ) (x : E) :
    flowOf (I := 𝓘(ℝ, E)) (fun _ : E ↦ v) t x = x + t • v := by
  simpa only [zero_smul, add_zero] using
    flowOf_eq_of_isMIntegralCurve (contMDiff_vectorSpace_iff_contDiff.mpr contDiff_const)
      (isMIntegralCurve_translation v x) t

end Translation

section Rotation

/-- The standard trigonometric parametrization of a rotating point is an integral curve of
`(x, y) ↦ (-ω y, ω x)`. Positive angular velocity gives counterclockwise rotation. -/
theorem isMIntegralCurve_planarRotation (ω : ℝ) (p : ℝ × ℝ) :
    IsMIntegralCurve (I := 𝓘(ℝ, ℝ × ℝ))
      (fun t : ℝ ↦ (Real.cos (ω * t) * p.1 - Real.sin (ω * t) * p.2,
        Real.sin (ω * t) * p.1 + Real.cos (ω * t) * p.2))
      (fun q ↦ (-(ω * q.2), ω * q.1)) := by
  intro t
  have hc := ((hasDerivAt_id t).const_mul ω).cos
  have hs := ((hasDerivAt_id t).const_mul ω).sin
  have hfst := (hc.mul_const p.1).sub (hs.mul_const p.2)
  have hsnd := (hs.mul_const p.1).add (hc.mul_const p.2)
  exact ((hfst.prodMk hsnd).congr_deriv (by ext <;> simp <;> ring)).hasFDerivAt.hasMFDerivAt

/-- The rotation field is a smooth tangent section, at every regularity. -/
theorem contMDiff_planarRotation (ω : ℝ) (n : WithTop ENat) :
    ContMDiff 𝓘(ℝ, ℝ × ℝ) (𝓘(ℝ, ℝ × ℝ)).tangent n
      (fun q : ℝ × ℝ ↦ (⟨q, (-(ω * q.2), ω * q.1)⟩ :
        TangentBundle 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ))) :=
  contMDiff_vectorSpace_iff_contDiff.mpr
    ((contDiff_const.mul contDiff_snd).neg.prodMk (contDiff_const.mul contDiff_fst))

/-- The planar rotation field is complete, including at angular velocity zero. -/
theorem isCompleteVectorField_planarRotation (ω : ℝ) :
    IsCompleteVectorField (I := 𝓘(ℝ, ℝ × ℝ))
      (fun q : ℝ × ℝ ↦ (-(ω * q.2), ω * q.1)) := by
  refine (isCompleteVectorField_iff_exists_isMIntegralCurve
    (contMDiff_planarRotation ω 1)).mpr fun p ↦ ?_
  exact ⟨_, by simp, isMIntegralCurve_planarRotation ω p⟩

/-- The maximal flow of the planar rotation field is rotation through angle `ω t`. -/
@[simp]
theorem flowOf_planarRotation (ω t : ℝ) (p : ℝ × ℝ) :
    flowOf (I := 𝓘(ℝ, ℝ × ℝ)) (fun q : ℝ × ℝ ↦ (-(ω * q.2), ω * q.1)) t p =
      (Real.cos (ω * t) * p.1 - Real.sin (ω * t) * p.2,
        Real.sin (ω * t) * p.1 + Real.cos (ω * t) * p.2) := by
  simpa only [mul_zero, Real.cos_zero, Real.sin_zero, one_mul, zero_mul, sub_zero,
    zero_add, Prod.mk.eta] using
    flowOf_eq_of_isMIntegralCurve (contMDiff_planarRotation ω 1)
      (isMIntegralCurve_planarRotation ω p) t

/-- At angular velocity one, the point `(1, 0)` reaches `(0, 1)` at time `π / 2`, fixing the
orientation and time normalization of the rotation formula. -/
theorem flowOf_planarRotation_pi_div_two :
    flowOf (I := 𝓘(ℝ, ℝ × ℝ)) (fun q : ℝ × ℝ ↦ (-q.2, q.1)) (Real.pi / 2) (1, 0) =
      (0, 1) := by
  simpa only [one_mul, Real.cos_pi_div_two, Real.sin_pi_div_two, mul_one, mul_zero,
    sub_zero, add_zero] using flowOf_planarRotation 1 (Real.pi / 2) (1, 0)

end Rotation

end TauCeti
