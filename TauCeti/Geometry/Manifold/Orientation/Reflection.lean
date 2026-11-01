/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Orientation.Preserving
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Maps of a vector space with negative Jacobian reverse orientation

A finite-dimensional real normed space `E` is connected, so an orientation `o` of `E`, viewed as a
manifold, has the same tangent orientation at every point: it is a constant orientation or its
opposite. Hence a map `f : E → E` whose derivative at `v` has negative determinant reverses `o` at
`v` (`TauCeti.Manifold.Orientation.isOrientationReversingAt_of_det_fderiv_neg`).

The basic example is the reflection of an inner product space in the hyperplane orthogonal to a
nonzero vector, whose determinant is `-1`: it reverses every orientation of `E` at every point
(`TauCeti.Manifold.Orientation.isOrientationReversingAt_reflection`). Composing with it turns an
orientation-reversing chart into an orientation-preserving one.

## Main results

* `TauCeti.Manifold.Orientation.isOrientationReversingAt_of_det_fderiv_neg`: a map of `E` whose
  derivative has negative determinant reverses every orientation of `E`.
* `TauCeti.Manifold.Orientation.isOrientationReversingAt_reflection`: the reflection in a
  hyperplane reverses every orientation of `E`.
-/

public section

open Module
open scoped Manifold

namespace TauCeti.Manifold.Orientation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι]

/-- **A map with negative Jacobian reverses orientation.** For every orientation `o` of the
finite-dimensional real normed space `E`, viewed as a manifold, a map `f : E → E` whose derivative
at `v` has negative determinant reverses `o` at `v`. -/
theorem isOrientationReversingAt_of_det_fderiv_neg (o : Manifold.Orientation 𝓘(ℝ, E) E ι)
    {f : E → E} {v : E} (hdet : LinearMap.det (fderiv ℝ f v : E →ₗ[ℝ] E) < 0) :
    IsOrientationReversingAt o o f v := by
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

/-- **Reflections reverse orientation.** For every orientation `o` of the finite-dimensional real
inner product space `E`, viewed as a manifold, the reflection in the hyperplane orthogonal to a
nonzero vector `u` reverses `o` at every point. -/
theorem isOrientationReversingAt_reflection {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (o : Manifold.Orientation 𝓘(ℝ, E) E ι)
    {u : E} (hu : u ≠ 0) (v : E) :
    IsOrientationReversingAt o o (ℝ ∙ u)ᗮ.reflection v := by
  refine isOrientationReversingAt_of_det_fderiv_neg o ?_
  have hK : finrank ℝ (ℝ ∙ u)ᗮᗮ = 1 := by
    rw [Submodule.orthogonal_orthogonal, finrank_span_singleton hu]
  -- The reflection is its own derivative, and its determinant is `(-1) ^ 1`.
  have hD : fderiv ℝ (ℝ ∙ u)ᗮ.reflection v =
      ((ℝ ∙ u)ᗮ.reflection.toContinuousLinearEquiv : E →L[ℝ] E) :=
    (ℝ ∙ u)ᗮ.reflection.toContinuousLinearEquiv.fderiv
  rw [hD]
  -- The coercions of the reflection to a continuous linear map and to a linear map agree.
  have hrefl : (((ℝ ∙ u)ᗮ.reflection.toContinuousLinearEquiv : E →L[ℝ] E) : E →ₗ[ℝ] E) =
      (ℝ ∙ u)ᗮ.reflection.toLinearMap := (rfl)
  rw [hrefl, Submodule.det_reflection, hK, pow_one]
  exact neg_one_lt_zero

end TauCeti.Manifold.Orientation
