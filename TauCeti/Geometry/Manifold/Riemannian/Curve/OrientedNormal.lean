/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.VolumeForm
public import TauCeti.Geometry.Manifold.MFDeriv.Curve
public import Mathlib.Analysis.InnerProductSpace.TwoDim
public import Mathlib.Analysis.Normed.Module.Normalize

/-!
# The oriented unit normal of a curve on a surface

On an oriented Riemannian surface, the oriented unit normal of a curve `γ` is its velocity rotated
by `+π/2` in the oriented tangent plane and divided by its speed, `ν = J γ' / ‖γ'‖`. At regular
points it is a unit vector orthogonal to the velocity, and the oriented area of the pair
`(γ', ν)` is the speed, so `ν` points to the left of `γ` with respect to the orientation. Along a
positively oriented boundary curve of a domain it is the inward normal. It vanishes where the
velocity does, and reversing the curve reverses it.

## Main results

* `TauCeti.Manifold.orientedUnitNormal`: the oriented unit normal `J γ' / ‖γ'‖`.
* `TauCeti.Manifold.norm_orientedUnitNormal` and
  `TauCeti.Manifold.inner_orientedUnitNormal_curveVelocity`: at a regular point it is a unit
  vector orthogonal to the velocity.
* `TauCeti.Manifold.riemannianVolumeForm_curveVelocity_orientedUnitNormal`: the oriented area of
  the velocity and the normal is the speed.
* `TauCeti.Manifold.orientedUnitNormal_comp_const_sub`: reversing the curve reverses the normal.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapter 9 (Gauss–Bonnet).
-/

public section

open Bundle TauCeti
open scoped Manifold ContDiff
noncomputable section

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (TangentSpace I : M → Type _)]

/-- The **oriented unit normal** `J γ' / ‖γ'‖` of a curve `γ` on an oriented surface: its
normalized velocity rotated by `+π/2` in the oriented tangent plane. It is the zero vector where
the velocity vanishes. -/
def orientedUnitNormal (o : Orientation I M (Fin 2)) (γ : ℝ → M) (t : ℝ) :
    TangentSpace I (γ t) :=
  letI := o.fact_finrank_tangentSpace (γ t)
  (o.orientationAt (γ t)).rightAngleRotation (NormedSpace.normalize (curveVelocity I γ t))

/-- The defining formula for `orientedUnitNormal`. -/
theorem orientedUnitNormal_apply (o : Orientation I M (Fin 2)) (γ : ℝ → M) (t : ℝ) :
    orientedUnitNormal o γ t =
      (letI := o.fact_finrank_tangentSpace (γ t);
        (o.orientationAt (γ t)).rightAngleRotation
          (NormedSpace.normalize (curveVelocity I γ t))) := (rfl)

/-- At a regular point, the oriented unit normal has norm one. -/
@[simp]
theorem norm_orientedUnitNormal (o : Orientation I M (Fin 2)) (γ : ℝ → M) {t : ℝ}
    (hv : curveVelocity I γ t ≠ 0) : ‖orientedUnitNormal o γ t‖ = 1 := by
  let := o.fact_finrank_tangentSpace (γ t)
  rw [orientedUnitNormal_apply, LinearIsometryEquiv.norm_map, NormedSpace.norm_normalize hv]

/-- The oriented unit normal is orthogonal to the velocity. -/
@[simp]
theorem inner_orientedUnitNormal_curveVelocity (o : Orientation I M (Fin 2))
    (γ : ℝ → M) (t : ℝ) : inner ℝ (orientedUnitNormal o γ t) (curveVelocity I γ t) = 0 := by
  let := o.fact_finrank_tangentSpace (γ t)
  rw [orientedUnitNormal_apply, NormedSpace.normalize, map_smul, real_inner_smul_left,
    (o.orientationAt (γ t)).inner_rightAngleRotation_self, mul_zero]

/-- The oriented unit normal vanishes exactly where the velocity does. -/
@[simp]
theorem orientedUnitNormal_eq_zero_iff (o : Orientation I M (Fin 2))
    (γ : ℝ → M) (t : ℝ) : orientedUnitNormal o γ t = 0 ↔ curveVelocity I γ t = 0 := by
  let := o.fact_finrank_tangentSpace (γ t)
  rw [orientedUnitNormal_apply, LinearIsometryEquiv.map_eq_zero_iff,
    NormedSpace.normalize_eq_zero_iff]

/-- The oriented area of the velocity followed by the oriented unit normal is the speed. Thus at
a regular point the pair `(γ', ν)` is a positively oriented basis of the tangent plane. -/
theorem riemannianVolumeForm_curveVelocity_orientedUnitNormal
    (o : Orientation I M (Fin 2)) (γ : ℝ → M) (t : ℝ) :
    riemannianVolumeForm o (γ t) ![curveVelocity I γ t, orientedUnitNormal o γ t] =
      ‖curveVelocity I γ t‖ := by
  let := o.fact_finrank_tangentSpace (γ t)
  rw [riemannianVolumeForm_apply, ← (o.orientationAt (γ t)).areaForm_to_volumeForm,
    orientedUnitNormal_apply, (o.orientationAt (γ t)).areaForm_rightAngleRotation_right,
    NormedSpace.normalize, real_inner_smul_right, real_inner_self_eq_norm_sq]
  by_cases h : ‖curveVelocity I γ t‖ = 0
  · simp [h]
  · field_simp

/-- Reversing a curve reverses its oriented unit normal. -/
theorem orientedUnitNormal_comp_const_sub (o : Orientation I M (Fin 2)) (γ : ℝ → M) (d t : ℝ) :
    orientedUnitNormal o (fun r ↦ γ (d - r)) t = -orientedUnitNormal o γ (d - t) := by
  let := o.fact_finrank_tangentSpace (γ (d - t))
  have hv : curveVelocity I (fun r ↦ γ (d - r)) t = -curveVelocity I γ (d - t) := by
    by_cases hγ : MDifferentiableAt 𝓘(ℝ) I γ (d - t)
    · simpa only [Function.comp_def, id_eq, neg_smul, one_smul] using
        curveVelocity_comp ((hasDerivAt_id t).const_sub d) hγ
    · have hγ' : ¬MDifferentiableAt 𝓘(ℝ) I (fun r ↦ γ (d - r)) t := fun h ↦ hγ <| by
        simpa only [Function.comp_def, sub_sub_cancel, id_eq] using h.comp_of_eq (d - t)
          (mdifferentiableAt_iff_differentiableAt.2 (differentiableAt_id.const_sub d))
          (sub_sub_cancel d t)
      rw [curveVelocity_apply, curveVelocity_apply, mfderiv_zero_of_not_mdifferentiableAt hγ,
        mfderiv_zero_of_not_mdifferentiableAt hγ']
      exact neg_zero.symm
  rw [orientedUnitNormal_apply, orientedUnitNormal_apply, hv, NormedSpace.normalize_neg, map_neg]

end TauCeti.Manifold
