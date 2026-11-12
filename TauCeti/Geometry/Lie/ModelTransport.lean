/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ModelTransport.Interior
public import TauCeti.Geometry.Lie.Functor

/-!
# The native Lie algebra under interior model transport

A finite-dimensional smooth real Lie group has a self-modelled copy with the same carrier,
topology and group operations, even if its original model with corners has boundary. The two
identity homomorphisms induce mutually inverse maps of the native Lie algebras. Their equivalence
transports Lie-algebra homomorphisms between the original models and the vector-space models,
for integration through the native Frobenius constructions.

## Main results

* `TauCeti.BoundarylessModel.lieMap_fromInteriorModelHom_toInteriorModelHom` and
  `lieMap_toInteriorModelHom_fromInteriorModelHom`: the two Lie maps are inverse.
* `TauCeti.BoundarylessModel.interiorLieEquiv`: the native Lie-algebra equivalence.
* `TauCeti.BoundarylessModel.interiorLieEquiv_apply` and `interiorLieEquiv_symm_apply`:
  its forward and inverse Lie maps.

## References

* A. Kirillov Jr., *An Introduction to Lie Groups and Lie Algebras*, Cambridge Studies in
  Advanced Mathematics 113 (2008), Chapter 3, §3.2, Proposition 3.12(1), for differentiation
  of group homomorphisms preserving the Lie bracket.
-/

public noncomputable section

open scoped Manifold ContDiff

namespace TauCeti.BoundarylessModel

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  [TopologicalSpace M] [ChartedSpace H M] [Group M] [LieGroup I ∞ M]
  [FiniteDimensional ℝ E]

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold
attribute [local instance] interiorChartedSpace

/-- Transport to the vector-space model and back preserves every native derivation. -/
@[simp]
theorem lieMap_fromInteriorModelHom_toInteriorModelHom (X : LeftInvariantDerivation I M) :
    lieMap (fromInteriorModelHom I (M := M)) (lieMap (toInteriorModelHom I (M := M)) X) = X := by
  exact (toInteriorModelHom I (M := M)).leftInverse_lieMap
    (fromInteriorModelHom I (M := M))
    (fromInteriorModelHom_comp_toInteriorModelHom I (M := M) (n := ∞)) X

/-- Transport back to the original model and forward preserves every copied native derivation. -/
@[simp]
theorem lieMap_toInteriorModelHom_fromInteriorModelHom
    (X : LeftInvariantDerivation 𝓘(ℝ, E) (BoundarylessModel I M)) :
      lieMap (toInteriorModelHom I (M := M)) (lieMap (fromInteriorModelHom I (M := M)) X) = X := by
  exact (fromInteriorModelHom I (M := M)).leftInverse_lieMap
    (toInteriorModelHom I (M := M))
    (toInteriorModelHom_comp_fromInteriorModelHom I (M := M) (n := ∞)) X

/-- The native Lie equivalence induced by the identity map to the vector-space model copy. -/
def interiorLieEquiv :
    LeftInvariantDerivation I M ≃ₗ⁅ℝ⁆
      LeftInvariantDerivation 𝓘(ℝ, E) (BoundarylessModel I M) :=
  TauCeti.Lie.lieEquivOfIsLocalDiffeomorphAt (toInteriorModelHom I (M := M)) (by
    rw [coe_toInteriorModelHom, ← coe_interiorDiffeomorph I ∞]
    exact (interiorDiffeomorph I ∞).isLocalDiffeomorph 1)

/-- The forward Lie equivalence is the Lie map of the forward identity homomorphism. -/
@[simp]
theorem interiorLieEquiv_apply (X : LeftInvariantDerivation I M) :
    interiorLieEquiv I (M := M) X = lieMap (toInteriorModelHom I (M := M)) X :=
  TauCeti.Lie.lieEquivOfIsLocalDiffeomorphAt_apply _ _ X

/-- The inverse Lie equivalence is the Lie map of the reverse identity homomorphism. -/
@[simp]
theorem interiorLieEquiv_symm_apply
    (X : LeftInvariantDerivation 𝓘(ℝ, E) (BoundarylessModel I M)) :
      (interiorLieEquiv I (M := M)).symm X = lieMap (fromInteriorModelHom I (M := M)) X := by
  apply (interiorLieEquiv I (M := M)).injective
  simp only [LieEquiv.coe_toLieHom, LieEquiv.apply_symm_apply, interiorLieEquiv_apply,
    lieMap_toInteriorModelHom_fromInteriorModelHom]

end TauCeti.BoundarylessModel
