/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.HalfSpace
public import TauCeti.Geometry.Manifold.PLGroupoid.Map

/-!
# The two half-space models are PL homeomorphic

The homeomorphism `TauCeti.halfSpaceHomeomorphEuclideanHalfSpace` of the product half-space
`{q : (Fin n → ℝ) × ℝ | 0 ≤ q.2}` onto Mathlib's half-space `EuclideanHalfSpace (n + 1)` reads,
in the model vector spaces, as the continuous linear equivalence
`TauCeti.prodCommEuclideanFinConsEquiv n`. So it is PL in both directions
(`TauCeti.isPLMap_halfSpaceHomeomorphEuclideanHalfSpace`,
`TauCeti.isPLMap_halfSpaceHomeomorphEuclideanHalfSpace_symm`), by `TauCeti.isPLMap_of_comp_eq`.
-/

public section

open scoped Manifold

namespace TauCeti

variable {n : ℕ}

/-- The homeomorphism of the product half-space onto `EuclideanHalfSpace (n + 1)` is PL. -/
theorem isPLMap_halfSpaceHomeomorphEuclideanHalfSpace :
    IsPLMap (modelWithCornersHalfSpace (Fin n → ℝ)) (𝓡∂ (n + 1))
      (halfSpaceHomeomorphEuclideanHalfSpace n) :=
  isPLMap_of_comp_eq ((prodCommEuclideanFinConsEquiv n : _ →L[ℝ] _).toContinuousAffineMap)
    fun q => by
      rw [ContinuousLinearMap.coe_toContinuousAffineMap, ContinuousLinearEquiv.coe_coe]
      exact modelWithCornersEuclideanHalfSpace_halfSpaceHomeomorphEuclideanHalfSpace q

/-- The inverse of the homeomorphism of the product half-space onto `EuclideanHalfSpace (n + 1)`
is PL. -/
theorem isPLMap_halfSpaceHomeomorphEuclideanHalfSpace_symm :
    IsPLMap (𝓡∂ (n + 1)) (modelWithCornersHalfSpace (Fin n → ℝ))
      (halfSpaceHomeomorphEuclideanHalfSpace n).symm :=
  isPLMap_of_comp_eq ((prodCommEuclideanFinConsEquiv n).symm : _ →L[ℝ] _).toContinuousAffineMap
    fun y => by
      rw [ContinuousLinearMap.coe_toContinuousAffineMap, ContinuousLinearEquiv.coe_coe]
      exact modelWithCornersHalfSpace_halfSpaceHomeomorphEuclideanHalfSpace_symm y

end TauCeti
