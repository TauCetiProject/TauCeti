/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Galois.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.GenericPoint.Reduction
public import TauCeti.FieldTheory.FunctionField.Place.Equiv

/-!
# Galois actions on the places of a Weierstrass function field

For a curve defined over `F`, coefficient automorphisms of `K/F` permute the places of `K(W)/K`.
The action transports valuations along the semilinear function-field action and preserves residue
degrees. On an elliptic curve, the point–place dictionary intertwines this action with the
coefficientwise action on points. These compatibilities let Galois conjugation transport the
zeros and poles used in the divisor construction of the Weil pairing.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.3 and III.8.
-/

public section

open TauCeti
open scoped WeierstrassCurve

namespace WeierstrassCurve

variable {F K : Type*} [Field F] [Field K] [Algebra F K] (W : WeierstrassCurve F)

/-- **The Galois action on places of a base-changed curve.** A coefficient automorphism carries
`v` to `v ∘ σ⁻¹`, where `σ` acts semilinearly on the function field. -/
noncomputable def placeGaloisAction :
    (K ≃ₐ[F] K) →* Equiv.Perm (Place K (W⁄K).toAffine.FunctionField) where
  toFun σ := Place.equivOfRingEquiv σ.toRingEquiv (W.functionFieldGaloisAction σ)
    (W.functionFieldGaloisAction_algebraMap σ)
  map_one' := by
    ext v z
    simp
    -- The inverse of the identity ring automorphism is definitionally the identity.
    rfl
  map_mul' σ τ := by
    ext v z
    simp only [map_mul, Equiv.Perm.mul_apply, Place.valuation_equivOfRingEquiv]
    -- Ring-automorphism multiplication composes maps; its inverse composes their inverses.
    rfl

/-- The inverse action on places is the action of the inverse coefficient automorphism. -/
@[simp]
theorem placeGaloisAction_symm (σ : K ≃ₐ[F] K) :
    (W.placeGaloisAction σ).symm = W.placeGaloisAction σ.symm :=
  (map_inv (W.placeGaloisAction) σ).symm

/-- The Galois action on places is transport of their valuations. -/
@[simp]
theorem placeGaloisAction_valuation (σ : K ≃ₐ[F] K)
    (v : Place K (W⁄K).toAffine.FunctionField) (z : (W⁄K).toAffine.FunctionField) :
    (W.placeGaloisAction σ v).valuation z =
      v.valuation ((W.functionFieldGaloisAction σ).symm z) :=
  Place.valuation_equivOfRingEquiv ..

/-- Galois conjugation preserves the order at the conjugate place. -/
@[simp]
theorem placeGaloisAction_ord (σ : K ≃ₐ[F] K)
    (v : Place K (W⁄K).toAffine.FunctionField) (z : (W⁄K).toAffine.FunctionField) :
    (W.placeGaloisAction σ v).ord z = v.ord ((W.functionFieldGaloisAction σ).symm z) :=
  Place.ord_equivOfRingEquiv ..

/-- Galois conjugation preserves the residue degree over `K`. -/
@[simp]
theorem placeGaloisAction_degree (σ : K ≃ₐ[F] K)
    (v : Place K (W⁄K).toAffine.FunctionField) :
    (W.placeGaloisAction σ v).degree = v.degree :=
  Place.degree_equivOfRingEquiv ..

/-- The Galois action fixes the place at infinity. -/
@[simp]
theorem placeGaloisAction_infinity (σ : K ≃ₐ[F] K) :
    W.placeGaloisAction σ (Place.infinity (W⁄K).toAffine) =
      Place.infinity (W⁄K).toAffine := by
  apply Place.eq_of_isEquiv
  rw [Place.valuation_infinity]
  apply Affine.isEquiv_infinityPlace_of_one_lt
  rw [← Affine.genericX_eq_algebraMap, placeGaloisAction_valuation,
    functionFieldGaloisAction_symm, functionFieldGaloisAction_genericX,
    Place.valuation_infinity, Affine.genericX_eq_algebraMap]
  exact Affine.one_lt_infinityPlace_X _

variable [DecidableEq K] [W.IsElliptic]

local instance : IsDedekindDomain (W⁄K).toAffine.CoordinateRing :=
  have := Affine.isIntegrallyClosed_coordinateRing (W⁄K).toAffine
  (W⁄K).toAffine.isDedekindDomain_coordinateRing_of_isIntegrallyClosed

/-- **The point–place dictionary is Galois-equivariant.** Conjugating a point conjugates its
place by the semilinear function-field action. -/
@[simp]
theorem placeGaloisAction_pointEquivDegreeOnePlace (σ : K ≃ₐ[F] K)
    (P : (W⁄K).toAffine.Point) :
    W.placeGaloisAction σ ((W⁄K).toAffine.pointEquivDegreeOnePlace P).1 =
      ((W⁄K).toAffine.pointEquivDegreeOnePlace
        (Multiplicative.toAdd (W.pointGaloisAction σ) P)).1 := by
  rcases P with _ | ⟨x, y, h⟩
  · rw [← Affine.Point.zero_def]
    simp only [map_zero]
    rw [Affine.Point.zero_def, Affine.coe_pointEquivDegreeOnePlace_zero,
      placeGaloisAction_infinity]
  rw [pointGaloisAction_apply, Affine.Point.map_some,
    Affine.coe_pointEquivDegreeOnePlace_some, Affine.coe_pointEquivDegreeOnePlace_some]
  set v := W.placeGaloisAction σ
    (Place.ofPrime K (W⁄K).toAffine.FunctionField (Affine.CoordinateRing.pointPlace h.1))
  have hv : ∀ r : (W⁄K).toAffine.CoordinateRing,
      algebraMap (W⁄K).toAffine.CoordinateRing (W⁄K).toAffine.FunctionField r ∈ v.integers := by
    intro r
    rw [Place.mem_integers_iff, placeGaloisAction_valuation, functionFieldGaloisAction_symm,
      functionFieldGaloisAction_algebraMap_coordinateRing]
    exact (Place.mem_integers_iff _).mp (Place.algebraMap_mem_integers_ofPrime _ _ _ _)
  rw [← Place.ofPrime_center K _ v hv]
  congr 1
  apply Affine.CoordinateRing.eq_pointPlace_of_mem_asIdeal
  · rw [Place.mem_center_asIdeal, Affine.algebraMap_XClass, placeGaloisAction_valuation,
      functionFieldGaloisAction_symm]
    simp only [map_sub, functionFieldGaloisAction_genericX,
      functionFieldGaloisAction_algebraMap, AlgEquiv.coe_toAlgHom,
      AlgEquiv.symm_apply_apply]
    exact Affine.valuation_pointPlace_genericX_sub_lt_one _ h.1
  · rw [Place.mem_center_asIdeal, Affine.algebraMap_YClass, placeGaloisAction_valuation,
      functionFieldGaloisAction_symm]
    simp only [map_sub, functionFieldGaloisAction_genericY,
      functionFieldGaloisAction_algebraMap, AlgEquiv.coe_toAlgHom,
      AlgEquiv.symm_apply_apply]
    exact Affine.valuation_pointPlace_genericY_sub_lt_one _ h.1

end WeierstrassCurve
