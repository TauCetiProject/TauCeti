/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.Model
public import TauCeti.Geometry.Manifold.Instances.HalfSpace

/-!
# The product half-space and the Euclidean half-space

The half-space `{q : (Fin n → ℝ) × ℝ | 0 ≤ q.2}`, the model space of
`TauCeti.modelWithCornersHalfSpace`, and Mathlib's `EuclideanHalfSpace (n + 1)` are related by the
linear isomorphism `(v, t) ↦ (t, v)` (`TauCeti.halfSpaceLinearEquiv`), which puts the height `t` in
the zeroth coordinate. It restricts to a homeomorphism of the two model spaces
(`TauCeti.halfSpaceHomeomorphEuclideanHalfSpace`) carrying the boundary hyperplane `{q | q.2 = 0}`
onto `{x | x 0 = 0}`.

## Main definitions

* `TauCeti.halfSpaceLinearEquiv`: the linear isomorphism `(v, t) ↦ (t, v)` of `(Fin n → ℝ) × ℝ`
  with `ℝⁿ⁺¹`.
* `TauCeti.halfSpaceHomeomorphEuclideanHalfSpace`: its restriction to a homeomorphism of the
  product half-space with `EuclideanHalfSpace (n + 1)`.

## Main results

* `TauCeti.image_halfSpaceHomeomorphEuclideanHalfSpace_setOf_snd_eq_zero`: the homeomorphism
  matches the two boundary hyperplanes.
-/

public section

namespace TauCeti

/-- The continuous linear isomorphism `(v, t) ↦ (t, v)` of `(Fin n → ℝ) × ℝ` with `ℝⁿ⁺¹`: the
factors are swapped, then `TauCeti.euclideanFinConsEquiv` puts `t` in the zeroth coordinate. -/
noncomputable def halfSpaceLinearEquiv (n : ℕ) :
    ((Fin n → ℝ) × ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
  (ContinuousLinearEquiv.prodComm ℝ (Fin n → ℝ) ℝ).trans (euclideanFinConsEquiv rfl)

/-- `TauCeti.halfSpaceLinearEquiv` sends `(v, t)` to `(t, v)` in `ℝⁿ⁺¹`. -/
@[simp]
theorem halfSpaceLinearEquiv_apply {n : ℕ} (q : (Fin n → ℝ) × ℝ) :
    halfSpaceLinearEquiv n q = euclideanFinConsEquiv rfl q.swap := by
  simp [halfSpaceLinearEquiv]

/-- The inverse of `TauCeti.halfSpaceLinearEquiv` sends `(t, v)` in `ℝⁿ⁺¹` to `(v, t)`. -/
@[simp]
theorem halfSpaceLinearEquiv_symm_apply {n : ℕ} (x : EuclideanSpace ℝ (Fin (n + 1))) :
    (halfSpaceLinearEquiv n).symm x = ((euclideanFinConsEquiv rfl).symm x).swap := by
  simp [halfSpaceLinearEquiv]

/-- The homeomorphism `(v, t) ↦ (t, v)` of the product half-space `{q : (Fin n → ℝ) × ℝ | 0 ≤ q.2}`,
the model space of `TauCeti.modelWithCornersHalfSpace`, with Mathlib's Euclidean half-space
`EuclideanHalfSpace (n + 1)`: the height `t` becomes the zeroth coordinate. It is the restriction
of `TauCeti.halfSpaceLinearEquiv`. -/
noncomputable def halfSpaceHomeomorphEuclideanHalfSpace (n : ℕ) :
    {q : (Fin n → ℝ) × ℝ | 0 ≤ q.2} ≃ₜ EuclideanHalfSpace (n + 1) :=
  (halfSpaceLinearEquiv n).toHomeomorph.subtype fun q => by simp

/-- `TauCeti.halfSpaceHomeomorphEuclideanHalfSpace` sends `(v, t)` to `(t, v)` in `ℝⁿ⁺¹`. -/
@[simp]
theorem coe_halfSpaceHomeomorphEuclideanHalfSpace_apply {n : ℕ}
    (q : {q : (Fin n → ℝ) × ℝ | 0 ≤ q.2}) :
    (halfSpaceHomeomorphEuclideanHalfSpace n q).val = euclideanFinConsEquiv rfl q.val.swap :=
  Homeomorph.subtype_apply_coe _ _ q

/-- The inverse of `TauCeti.halfSpaceHomeomorphEuclideanHalfSpace` sends `(t, v)` in `ℝⁿ⁺¹` to
`(v, t)`. -/
@[simp]
theorem coe_halfSpaceHomeomorphEuclideanHalfSpace_symm_apply {n : ℕ}
    (x : EuclideanHalfSpace (n + 1)) :
    ((halfSpaceHomeomorphEuclideanHalfSpace n).symm x).val =
      ((euclideanFinConsEquiv rfl).symm x.val).swap :=
  Homeomorph.subtype_symm_apply_coe _ _ x

/-- The homeomorphism `TauCeti.halfSpaceHomeomorphEuclideanHalfSpace` carries the boundary
hyperplane `{q | q.2 = 0}` of the product half-space onto the boundary hyperplane `{x | x 0 = 0}`
of the Euclidean half-space. -/
theorem image_halfSpaceHomeomorphEuclideanHalfSpace_setOf_snd_eq_zero (n : ℕ) :
    halfSpaceHomeomorphEuclideanHalfSpace n '' {q | q.val.2 = 0} = {x | x.val 0 = 0} := by
  ext x
  simp [(halfSpaceHomeomorphEuclideanHalfSpace n).image_eq_preimage_symm]

end TauCeti
