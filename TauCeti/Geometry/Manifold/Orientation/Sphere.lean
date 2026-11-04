/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Sphere
public import Mathlib.LinearAlgebra.Complex.Orientation
public import TauCeti.Analysis.InnerProductSpace.Orientation
public import TauCeti.Geometry.Manifold.Orientation.TopForm
import Mathlib.Analysis.InnerProductSpace.TwoDim
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
import TauCeti.Geometry.Manifold.DifferentialForm.Regularity
import TauCeti.Geometry.Manifold.Instances.Sphere

/-!
# The outward-normal orientation of a unit sphere

Let `E` be an oriented real inner product space of dimension `n + 1`, with unit sphere `Sⁿ`.
The tangent space of `Sⁿ` at `u` is carried by the derivative of the inclusion onto the
hyperplane `u^⊥` (`range_mvfderiv_subtypeVal`), and `u` itself is the outward normal there. The
*outward-normal orientation* `o.sphereOrientation` declares a tangent basis
`v₁, …, vₙ` at `u` positive exactly when `u, v₁, …, vₙ` is a positive basis of `E`
(`Orientation.orientation_eq_orientationAt_sphereOrientation_iff`), the convention by which
`o.orthogonalSpanSingleton` orients the hyperplane `u^⊥`.

Putting the outward normal first is the usual convention for the boundary orientation of the
closed unit ball. For the unit circle of `ℂ` with its standard orientation, the
positive tangent direction at `z` is `i z`, the counterclockwise one
(`Complex.orientation_eq_orientationAt_sphereOrientation_iff`). Mathlib's stereographic
atlas of the sphere is not coherently oriented, so the orientation is constructed instead from the
nowhere-vanishing top form `(v₁, …, vₙ) ↦ vol(u, v₁, …, vₙ)`, the pullback to `Sⁿ` of the
contraction of the volume form of `E` with the position vector, through
`TauCeti.Manifold.Orientation.ofTopForm`.

## Main declarations

* `Orientation.sphereOrientation`: the outward-normal orientation of the unit sphere.
* `Orientation.orientation_eq_orientationAt_sphereOrientation_iff`: a tangent basis at `u` is
  positive exactly when `u` followed by its image in `E` has positive volume, and
  `Orientation.orientation_eq_neg_orientationAt_sphereOrientation_iff` its negative counterpart.
* `Complex.orientation_eq_orientationAt_sphereOrientation_iff`: a tangent vector `w` of the unit
  circle of `ℂ` at `z` is positive exactly when it points counterclockwise,
  `Re z Im w - Im z Re w > 0`.

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
(`Orientation.orientation_eq_orientationAt_sphereOrientation_iff`). -/
def _root_.Orientation.sphereOrientation (o : Orientation ℝ E (Fin (n + 1))) :
    Manifold.Orientation (𝓡 n) (sphere (0 : E) 1) (Fin n) :=
  Manifold.Orientation.ofTopForm finrank_euclideanSpace_fin (sphereTopForm o)
    (isSmoothForm_sphereTopForm o) (sphereTopForm_ne_zero o)

/-- A tangent basis `v` of the unit sphere at `u` is positive for the outward-normal orientation
exactly when `u, v₁, …, vₙ`, read in `E` through the derivative of the inclusion, has positive
volume, that is, is a positive basis of `E`. -/
theorem _root_.Orientation.orientation_eq_orientationAt_sphereOrientation_iff
    (o : Orientation ℝ E (Fin (n + 1))) {u : sphere (0 : E) 1}
    (v : Basis (Fin n) ℝ (TangentSpace (𝓡 n) u)) :
    v.orientation = o.sphereOrientation.orientationAt u ↔
      0 < o.volumeForm
        (Fin.cons (u : E) fun i ↦ mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) u (v i)) := by
  rw [Orientation.sphereOrientation,
    Manifold.Orientation.orientation_eq_orientationAt_ofTopForm_iff, sphereTopForm_apply]

/-- A tangent basis `v` of the unit sphere at `u` is negative for the outward-normal orientation
exactly when `u, v₁, …, vₙ`, read in `E` through the derivative of the inclusion, has negative
volume. -/
theorem _root_.Orientation.orientation_eq_neg_orientationAt_sphereOrientation_iff
    (o : Orientation ℝ E (Fin (n + 1))) {u : sphere (0 : E) 1}
    (v : Basis (Fin n) ℝ (TangentSpace (𝓡 n) u)) :
    v.orientation = -o.sphereOrientation.orientationAt u ↔
      o.volumeForm
        (Fin.cons (u : E) fun i ↦ mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) u (v i)) < 0 := by
  rw [← Orientation.ne_iff_eq_neg _ _ (o.sphereOrientation.finrank_tangentSpace_eq u).symm, Ne,
    o.orientation_eq_orientationAt_sphereOrientation_iff, not_lt]
  exact (Orientation.volumeForm_apply_ne_zero_iff.2
    (LinearIndependent.finCons_mvfderiv_coe_sphere u v.linearIndependent)).le_iff_lt

section Circle

attribute [local instance] finrank_real_complex_fact'

/-- A tangent basis `c` of the unit circle of `ℂ` at `z` is positive for the outward-normal
orientation exactly when its vector `w`, read in `ℂ`, points counterclockwise:
`Re z Im w - Im z Re w > 0`. So the positive direction at `z` is that of `i z`. -/
theorem _root_.Complex.orientation_eq_orientationAt_sphereOrientation_iff
    {z : sphere (0 : ℂ) 1} (c : Basis (Fin 1) ℝ (TangentSpace (𝓡 1) z)) :
    c.orientation = Complex.orientation.sphereOrientation.orientationAt z ↔
      0 < (z : ℂ).re * (mvfderiv (𝓡 1) ((↑) : sphere (0 : ℂ) 1 → ℂ) z (c 0)).im -
        (z : ℂ).im * (mvfderiv (𝓡 1) ((↑) : sphere (0 : ℂ) 1 → ℂ) z (c 0)).re := by
  have hcons : (Fin.cons (z : ℂ) fun i ↦ mvfderiv (𝓡 1) ((↑) : sphere (0 : ℂ) 1 → ℂ) z
      (c i) : Fin 2 → ℂ) = ![(z : ℂ), mvfderiv (𝓡 1) ((↑) : sphere (0 : ℂ) 1 → ℂ) z (c 0)] := by
    ext i
    fin_cases i <;> rfl
  rw [Complex.orientation.orientation_eq_orientationAt_sphereOrientation_iff, hcons,
    ← Orientation.areaForm_to_volumeForm, Complex.areaForm]
  generalize mvfderiv (𝓡 1) ((↑) : sphere (0 : ℂ) 1 → ℂ) z (c 0) = w
  simp [Complex.mul_im]

end Circle

end TauCeti
