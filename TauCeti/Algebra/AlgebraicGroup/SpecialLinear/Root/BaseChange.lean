/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Root.Adjoint
public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Tangent.BaseChange

/-!
# Scalar extension of special-linear adjoint root vectors

Scalar extension of the cotangent-dual model of `Lie(SLₙ)` agrees with the same
model constructed over the new base ring. The comparison sends each normalized
matrix-unit root vector to the corresponding root vector over that ring, retaining
its parameter. This identifies the actual generators used in integral pinnings.

The ambient comparison combines `Derivation.tangentScalarExtensionEquiv`,
`SpecialLinear.tangentCoefficientLieEquiv`, and cotangent duality. The geometric
compatibility of the middle comparison is proved in `SpecialLinear.Tangent.BaseChange`.

## References

* B. Conrad, *Reductive Group Schemes* (2014), §5.1.
* J. S. Milne, *Algebraic Groups* (2017), §21, Example 21.2.
-/

public section

open scoped TensorProduct

namespace TauCeti.SpecialLinear

universe u v

noncomputable section

variable (R : Type u) (K : Type v) [CommRing R] [CommRing K] [Algebra R K]
variable (r : ℕ)

/-- Scalar extension preserves every normalized root vector and its scalar parameter. -/
@[simp↓]
theorem cotangentDualBaseChangeEquiv_tmul_rootVector
    (p : SplitTorus.CoordinateRootIndex (Fin (r + 1))) (c : K) :
    cotangentDualBaseChangeEquiv R K (r + 1) (c ⊗ₜ[R] rootVector (R := R) p) =
      c • rootVector (R := K) p := by
  apply (Derivation.cotangentLinearEquiv (R := K)
    (A := coordinateHopfAlgebra K (r + 1)) (B := K)).injective
  rw [cotangentLinearEquiv_cotangentDualBaseChangeEquiv]
  apply (tangentLieEquivSl (R := K) (B := K) (r + 1)).injective
  simp only [LieEquiv.coe_toLieHom]
  -- Quotient-indexed scalar structures require elaborated rewriting for these maps.
  erw [tangentLieEquivSl_apply, tangentLieEquivSl_apply,
    tangentMatrix_tangentCoefficientLieEquiv,
    tangentScalarExtensionEquiv_tmul_rootVector, map_smul, map_smul,
    tangentMatrix_derivationComp_rootSubgroup, LinearEquiv.apply_symm_apply,
    tangentMatrix_cotangentLinearEquiv_rootVector]
  simpa only [smul_eq_mul, mul_one] using
    ((LieAlgebra.SpecialLinear.single p.1.1 p.1.2 p.2).map_smul c 1)

end

end TauCeti.SpecialLinear
