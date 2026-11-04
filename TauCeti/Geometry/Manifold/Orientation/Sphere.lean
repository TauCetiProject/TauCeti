/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Sphere
public import TauCeti.Analysis.InnerProductSpace.Orientation
public import TauCeti.Geometry.Manifold.Orientation.TopForm
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
import TauCeti.Geometry.Manifold.DifferentialForm.Regularity

/-!
# The outward-normal orientation of a unit sphere

Let `E` be an oriented real inner product space of dimension `n + 1`, with unit sphere `Sⁿ`.
The tangent space of `Sⁿ` at `u` is carried by the derivative of the inclusion onto the
hyperplane `u^⊥` (`range_mvfderiv_subtypeVal`), and `u` itself is the outward normal there. The
*outward-normal orientation* `TauCeti.sphereOrientation o` declares a tangent basis
`v₁, …, vₙ` at `u` positive exactly when `u, v₁, …, vₙ` is a positive basis of `E`
(`TauCeti.orientation_eq_orientationAt_sphereOrientation_iff`), the convention by which
`o.orthogonalSpanSingleton` orients the hyperplane `u^⊥`.

Putting the outward normal first is the usual convention for the boundary orientation of the
closed unit ball. For the unit circle of `ℂ` with its standard orientation, the
positive tangent direction at `z` is `i z`, the counterclockwise one. Mathlib's stereographic
atlas of the sphere is not coherently oriented, so the orientation is constructed instead from the
nowhere-vanishing top form `(v₁, …, vₙ) ↦ vol(u, v₁, …, vₙ)`, the pullback to `Sⁿ` of the
contraction of the volume form of `E` with the position vector, through
`TauCeti.Manifold.Orientation.ofTopForm`.

## Main declarations

* `TauCeti.sphereOrientation`: the outward-normal orientation of the unit sphere.
* `TauCeti.orientation_eq_orientationAt_sphereOrientation_iff`: a tangent basis at `u` is
  positive exactly when `u` followed by its image in `E` has positive volume.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 15 (orientations from nonvanishing top forms, outward normals and
  boundary orientations).
* M. Spivak, *Calculus on Manifolds*, Benjamin, 1965, Chapter 5 (outward normals and the
  orientation of a boundary).
-/

public section

noncomputable section

open Metric Module
open scoped Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]

/-- A point of the sphere followed by the image of a linearly independent family of tangent
vectors at it is linearly independent in `E`: the derivative of the inclusion is injective with
range `u^⊥`, which does not contain `u`. -/
theorem _root_.LinearIndependent.finCons_mvfderiv_coe_sphere (u : sphere (0 : E) 1)
    {v : Fin n → TangentSpace (𝓡 n) u} (hv : LinearIndependent ℝ v) :
    LinearIndependent ℝ
      (Fin.cons (u : E) fun i ↦ mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) u (v i)) := by
  refine linearIndependent_finCons.2 ⟨hv.map' _ (LinearMap.ker_eq_bot_of_injective
    (injective_mvfderiv_subtypeVal_sphere (n := n) u)), fun h ↦ ne_zero_of_mem_unit_sphere u ?_⟩
  have hle : Submodule.span ℝ (Set.range fun i ↦
      mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) u (v i)) ≤ (ℝ ∙ (u : E))ᗮ := by
    rw [← range_mvfderiv_subtypeVal (n := n) u]
    exact Submodule.span_le.2 (Set.range_subset_iff.2 fun i ↦ LinearMap.mem_range_self _ _)
  exact inner_self_eq_zero.1 (Submodule.mem_orthogonal_singleton_iff_inner_right.1 (hle h))

/-- The contraction `x ↦ vol(x, ·)` of the volume form of `E` with the position vector. -/
private def radialVolumeForm (o : Orientation ℝ E (Fin (n + 1))) : RoughForm 𝓘(ℝ, E) E ℝ n :=
  fun x ↦ o.volumeFormL.curryLeft x

/-- The top form `(v₁, …, vₙ) ↦ vol(u, v₁, …, vₙ)` on the unit sphere: the pullback along the
inclusion of the contraction of the volume form of `E` with the position vector. -/
private def sphereTopForm (o : Orientation ℝ E (Fin (n + 1))) :
    RoughForm (𝓡 n) (sphere (0 : E) 1) ℝ n :=
  mpullback (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) (radialVolumeForm o)

private theorem sphereTopForm_apply (o : Orientation ℝ E (Fin (n + 1))) (u : sphere (0 : E) 1)
    (v : Fin n → TangentSpace (𝓡 n) u) :
    sphereTopForm o u v = o.volumeForm
      (Fin.cons (u : E) fun i ↦ mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) u (v i)) := by
  rw [sphereTopForm, mpullback_apply]
  -- The radial form is `curryLeft` of the volume form, `Matrix.vecCons` is `Fin.cons`, and
  -- `mvfderiv` of the inclusion is its `mfderiv`, as `NormedSpace.fromTangentSpace` is the
  -- identity.
  exact (o.volumeFormL.curryLeft_apply_apply _ _).trans (o.volumeFormL_apply _)

private theorem isSmoothForm_sphereTopForm (o : Orientation ℝ E (Fin (n + 1))) :
    IsSmoothForm (𝓡 n) 0 (sphereTopForm o) :=
  (isSmoothForm_modelSpace_iff.2 (o.volumeFormL.curryLeft : E →L[ℝ] _).contDiff).mpullback
    contMDiff_coe_sphere

private theorem sphereTopForm_ne_zero (o : Orientation ℝ E (Fin (n + 1)))
    (u : sphere (0 : E) 1) : sphereTopForm o u ≠ 0 := by
  let b := finBasisOfFinrankEq ℝ (TangentSpace (𝓡 n) u) (finrank_euclideanSpace_fin (𝕜 := ℝ))
  intro h
  have hb := DFunLike.congr_fun h ⇑b
  rw [sphereTopForm_apply] at hb
  exact Orientation.volumeForm_apply_ne_zero_iff.2
    (LinearIndependent.finCons_mvfderiv_coe_sphere u b.linearIndependent) (by simpa using hb)

/-- The **outward-normal orientation** of the unit sphere `Sⁿ` of an oriented real inner product
space `E` of dimension `n + 1`: a tangent basis `v₁, …, vₙ` at `u` is positive exactly when
`u, v₁, …, vₙ` is a positive basis of `E`
(`TauCeti.orientation_eq_orientationAt_sphereOrientation_iff`). -/
def sphereOrientation (o : Orientation ℝ E (Fin (n + 1))) :
    Manifold.Orientation (𝓡 n) (sphere (0 : E) 1) (Fin n) :=
  Manifold.Orientation.ofTopForm finrank_euclideanSpace_fin (sphereTopForm o)
    (isSmoothForm_sphereTopForm o) (sphereTopForm_ne_zero o)

/-- A tangent basis `v` of the unit sphere at `u` is positive for the outward-normal orientation
exactly when `u, v₁, …, vₙ`, read in `E` through the derivative of the inclusion, has positive
volume, that is, is a positive basis of `E`. -/
theorem orientation_eq_orientationAt_sphereOrientation_iff (o : Orientation ℝ E (Fin (n + 1)))
    {u : sphere (0 : E) 1} (v : Basis (Fin n) ℝ (TangentSpace (𝓡 n) u)) :
    v.orientation = (sphereOrientation o).orientationAt u ↔
      0 < o.volumeForm
        (Fin.cons (u : E) fun i ↦ mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) u (v i)) := by
  rw [sphereOrientation, Manifold.Orientation.orientation_eq_orientationAt_ofTopForm_iff,
    sphereTopForm_apply]

end TauCeti
