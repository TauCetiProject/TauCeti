/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Orientation.Preserving
public import TauCeti.Geometry.Euclidean.Inversion
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Maps with negative Jacobian determinant, and inversion in a sphere, reverse orientation

A finite-dimensional real normed space `E`, viewed as a manifold, has exactly two orientations,
and the tangent orientations of each of them are all the same orientation of `E`. So a map
`f : E → E` reverses every orientation of `E` at a point `v` as soon as the determinant of its
derivative at `v` is negative
(`TauCeti.Manifold.Orientation.isOrientationReversingAt_of_det_fderiv_neg`). For example, a
reflection of a nontrivial inner product space in a hyperplane, whose determinant is `-1`,
reverses every orientation at every point
(`TauCeti.Manifold.Orientation.exists_linearIsometryEquiv_isOrientationReversingAt`).

Away from its centre, the derivative of the inversion of a finite-dimensional real inner product
space `E` in a sphere of nonzero radius has negative determinant
(`EuclideanGeometry.det_fderiv_inversion_neg`). So the inversion reverses every orientation of `E`
at every point other than the centre
(`TauCeti.Manifold.Orientation.isOrientationReversingAt_inversion`).

This is why the connected sum, which glues two punctured balls by the inversion, joins the
orientations of its summands only when the two balls induce opposite orientations of `E`.

## Main results

* `TauCeti.Manifold.Orientation.isOrientationReversingAt_of_det_fderiv_neg`: a map of `E` whose
  derivative at a point has negative determinant reverses every orientation of `E` there.
* `TauCeti.Manifold.Orientation.exists_linearIsometryEquiv_isOrientationReversingAt`: a
  nontrivial inner product space has a linear isometry reversing every orientation.
* `TauCeti.Manifold.Orientation.isOrientationReversingAt_inversion`: the inversion reverses every
  orientation of `E` away from the centre.
-/

public section

open Module EuclideanGeometry
open scoped Manifold

namespace TauCeti.Manifold.Orientation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι]

/-- **A negative Jacobian determinant reverses orientation.** For every orientation `o` of the
finite-dimensional real normed space `E`, viewed as a manifold, a map `f : E → E` whose derivative
at `v` has negative determinant reverses `o` at `v`. -/
theorem isOrientationReversingAt_of_det_fderiv_neg (o : Manifold.Orientation 𝓘(ℝ, E) E ι)
    {f : E → E} {v : E} (hdet : (fderiv ℝ f v).det < 0) : IsOrientationReversingAt o o f v := by
  -- On the connected space `E`, `o` is a constant orientation or its opposite, so its tangent
  -- orientations are all the same orientation of `E`.
  have hc : ∀ x y : E, o.orientationAt x = o.orientationAt y := by
    classical
    rcases o.eq_or_eq_neg (model (I := 𝓘(ℝ, E))
      ((finBasisOfFinrankEq ℝ E o.card_eq.symm).reindex (Fintype.equivFin ι).symm).orientation
      o.card_eq) with h | h <;> intro x y <;> rw [h] <;>
      simp only [orientationAt_model, orientationAt_neg] <;>
      -- Both sides are the same orientation of `E`, read in the tangent spaces at `x` and `y`.
      rfl
  let D : E ≃L[ℝ] E := (LinearMap.equivOfDetNeZero _ hdet.ne).toContinuousLinearEquiv
  refine (isOrientationReversingAt_iff_of_coe_eq o o _ v D ?_).mpr ?_
  · ext w
    simp only [D, mfderiv_eq_fderiv]
    -- The identifications of the tangent spaces of `E` with `E` are the identity.
    rfl
  · rw [hc (f v) v]
    exact (_root_.Orientation.map_eq_neg_iff_det_neg _ _ o.card_eq).mpr hdet

/-- **A reflection reverses orientation.** A nontrivial finite-dimensional real inner product space
`E` has a linear isometry, the reflection in a hyperplane, which reverses every orientation of `E`
at every point. -/
theorem exists_linearIsometryEquiv_isOrientationReversingAt {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E]
    (oE : Manifold.Orientation 𝓘(ℝ, E) E ι) :
    ∃ ρ : E ≃ₗᵢ[ℝ] E, ∀ v, IsOrientationReversingAt oE oE ρ v := by
  obtain ⟨u, hu⟩ := exists_ne (0 : E)
  refine ⟨(ℝ ∙ u)ᗮ.reflection, fun v ↦ isOrientationReversingAt_of_det_fderiv_neg oE ?_⟩
  have hD : fderiv ℝ ((ℝ ∙ u)ᗮ.reflection) v =
      ((ℝ ∙ u)ᗮ.reflection.toContinuousLinearEquiv : E →L[ℝ] E) :=
    (ℝ ∙ u)ᗮ.reflection.toContinuousLinearEquiv.fderiv
  rw [hD]
  have h1 : finrank ℝ (ℝ ∙ u)ᗮᗮ = 1 := by
    rw [Submodule.orthogonal_orthogonal, finrank_span_singleton hu]
  calc _ = LinearMap.det (ℝ ∙ u)ᗮ.reflection.toLinearMap := (rfl)
    _ = -1 := by rw [Submodule.det_reflection, h1, pow_one]
    _ < 0 := by norm_num

/-- **Inversion in a sphere reverses orientation.** For every orientation `o` of the
finite-dimensional real inner product space `E`, viewed as a manifold, the inversion in the sphere
of centre `c` and nonzero radius `R` reverses `o` at every point `v ≠ c`. -/
theorem isOrientationReversingAt_inversion {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (o : Manifold.Orientation 𝓘(ℝ, E) E ι)
    {c v : E} {R : ℝ} (hR : R ≠ 0) (hv : v ≠ c) :
    IsOrientationReversingAt o o (inversion c R) v :=
  isOrientationReversingAt_of_det_fderiv_neg o (det_fderiv_inversion_neg hR hv)

end TauCeti.Manifold.Orientation
