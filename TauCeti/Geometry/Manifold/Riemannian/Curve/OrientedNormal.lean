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
velocity does, increasing reparametrizations do not change it, and reversing the curve reverses
it.

## Main results

* `TauCeti.Manifold.orientedUnitNormal`: the oriented unit normal `J γ' / ‖γ'‖`.
* `TauCeti.Manifold.norm_orientedUnitNormal` and
  `TauCeti.Manifold.inner_orientedUnitNormal_curveVelocity`: at a regular point it is a unit
  vector orthogonal to the velocity.
* `TauCeti.Manifold.riemannianVolumeForm_curveVelocity_orientedUnitNormal`: the oriented area of
  the velocity and the normal is the speed.
* `TauCeti.Manifold.orientedUnitNormal_comp`: reparametrization multiplies the normal by the
  sign of its derivative, with positive and negative derivative specializations.
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
  rw [orientedUnitNormal_apply, orientedUnitNormal_apply, curveVelocity_comp_const_sub,
    NormedSpace.normalize_neg, map_neg]

/-- Curves agreeing near a parameter have the same oriented unit normal there. -/
theorem _root_.Filter.EventuallyEq.orientedUnitNormal_eq
    {γ η : ℝ → M} {t : ℝ} (h : γ =ᶠ[nhds t] η) (o : Orientation I M (Fin 2)) :
    orientedUnitNormal o γ t = orientedUnitNormal o η t := by
  rw [orientedUnitNormal_apply, orientedUnitNormal_apply, h.self_of_nhds, h.curveVelocity_eq]

/-- Reparametrization multiplies the oriented unit normal by the sign of its derivative. -/
theorem orientedUnitNormal_comp (o : Orientation I M (Fin 2)) {γ : ℝ → M} {φ : ℝ → ℝ}
    {c t : ℝ} (hφ : HasDerivAt φ c t) (hγ : MDifferentiableAt 𝓘(ℝ) I γ (φ t)) :
    orientedUnitNormal o (γ ∘ φ) t = (SignType.sign c : ℝ) • orientedUnitNormal o γ (φ t) := by
  rw [orientedUnitNormal_apply, orientedUnitNormal_apply, curveVelocity_comp hφ hγ,
    NormedSpace.normalize_smul, map_smul]
  simp only [Function.comp_apply]

/-- A reparametrization with positive derivative at `t` does not change the oriented unit normal
at `t`. -/
theorem orientedUnitNormal_comp_of_pos (o : Orientation I M (Fin 2)) {γ : ℝ → M} {φ : ℝ → ℝ}
    {c t : ℝ} (hφ : HasDerivAt φ c t) (hc : 0 < c) (hγ : MDifferentiableAt 𝓘(ℝ) I γ (φ t)) :
    orientedUnitNormal o (γ ∘ φ) t = orientedUnitNormal o γ (φ t) := by
  simpa [hc] using orientedUnitNormal_comp o hφ hγ

/-- A reparametrization with negative derivative at a parameter reverses the oriented unit normal
there. -/
theorem orientedUnitNormal_comp_of_neg (o : Orientation I M (Fin 2)) {γ : ℝ → M} {φ : ℝ → ℝ}
    {c t : ℝ} (hφ : HasDerivAt φ c t) (hc : c < 0) (hγ : MDifferentiableAt 𝓘(ℝ) I γ (φ t)) :
    orientedUnitNormal o (γ ∘ φ) t = -orientedUnitNormal o γ (φ t) := by
  simpa [hc] using orientedUnitNormal_comp o hφ hγ

end TauCeti.Manifold
