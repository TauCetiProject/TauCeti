/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Orientation.Preserving
public import Mathlib.Geometry.Euclidean.Inversion.Calculus
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Inversion in a sphere reverses orientation

The inversion `v ↦ v / ‖v‖²` of a finite-dimensional real inner product space `E` in its unit
sphere has derivative `‖v‖⁻² • ρ` at `v ≠ 0`, where `ρ` is the reflection in the hyperplane
orthogonal to `v` (Mathlib's `EuclideanGeometry.fderiv_inversion`). A reflection in a hyperplane
has determinant `-1`, so the derivative has negative determinant
(`TauCeti.Manifold.Orientation.det_fderiv_inversion_neg`), and the inversion reverses every
orientation of `E` at every point other than the centre
(`TauCeti.Manifold.Orientation.isOrientationReversingAt_inversion`).

This is why the connected sum, which glues two punctured balls by the inversion, joins the
orientations of its summands only when the two balls induce opposite orientations of `E`.

## Main results

* `TauCeti.Manifold.Orientation.det_fderiv_inversion_neg`: the derivative of the inversion has
  negative determinant away from the centre.
* `TauCeti.Manifold.Orientation.isOrientationReversingAt_inversion`: the inversion reverses every
  orientation of `E` away from the centre.
-/

public section

open Module EuclideanGeometry
open scoped Manifold

namespace TauCeti.Manifold.Orientation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι]

/-- The derivative of the inversion of `E` in its unit sphere has negative determinant at every
point other than the centre. -/
theorem det_fderiv_inversion_neg {v : E} (hv : v ≠ 0) :
    LinearMap.det (fderiv ℝ (inversion (0 : E) 1) v : E →ₗ[ℝ] E) < 0 := by
  rw [fderiv_inversion, ContinuousLinearMap.toLinearMap_smul, LinearMap.det_smul]
  -- The reflection is in the orthogonal complement of the line through `v`.
  have hK : finrank ℝ (ℝ ∙ (v - 0))ᗮᗮ = 1 := by
    rw [Submodule.orthogonal_orthogonal, sub_zero, finrank_span_singleton hv]
  rw [show (((ℝ ∙ (v - 0))ᗮ.reflection : E →L[ℝ] E) : E →ₗ[ℝ] E) =
    (ℝ ∙ (v - 0))ᗮ.reflection.toLinearMap from rfl, Submodule.det_reflection, hK]
  have : 0 < (1 / dist v 0) ^ 2 := by
    have : 0 < dist v 0 := dist_pos.2 hv
    positivity
  simp only [pow_one, mul_neg, mul_one, neg_lt_zero]
  exact pow_pos this _

/-- **The inversion in the unit sphere reverses orientation.** For every orientation `o` of the
finite-dimensional real inner product space `E`, viewed as a manifold, the inversion
`v ↦ v / ‖v‖²` reverses `o` at every point `v ≠ 0`. -/
theorem isOrientationReversingAt_inversion (o : Manifold.Orientation 𝓘(ℝ, E) E ι) {v : E}
    (hv : v ≠ 0) : IsOrientationReversingAt o o (inversion (0 : E) 1) v := by
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
  have hdet := det_fderiv_inversion_neg hv
  let D : E ≃L[ℝ] E := (LinearMap.equivOfDetNeZero _ hdet.ne).toContinuousLinearEquiv
  refine (isOrientationReversingAt_iff_of_coe_eq o o _ v D ?_).mpr ?_
  · ext w
    simp only [D, mfderiv_eq_fderiv]
    -- The identifications of the tangent spaces of `E` with `E` are the identity.
    rfl
  · rw [hc (inversion 0 1 v) v]
    exact (_root_.Orientation.map_eq_neg_iff_det_neg _ _ o.card_eq).mpr hdet

end TauCeti.Manifold.Orientation
