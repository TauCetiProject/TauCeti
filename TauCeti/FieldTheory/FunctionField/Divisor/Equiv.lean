/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.WeilDivisor.Principal.Congr
public import TauCeti.FieldTheory.FunctionField.Divisor.ProductFormula
public import TauCeti.FieldTheory.FunctionField.RiemannRoch.Equiv

/-!
# Divisor class groups under semilinear field isomorphisms

Let `τ : F ≃+* F'` be an isomorphism of function fields carrying the constants `k` onto `k'` along
`σ : k ≃+* k'`. It transports places (`Place.equivOfRingEquiv`) and hence divisors, by reindexing,
preserving degrees (`Divisor.degree_domCongr_equivOfRingEquiv`). This file shows that it carries
the divisor of a function `z` to the divisor of `τ z`. Consequently it carries principal divisors
onto principal divisors, and induces isomorphisms of the divisor class groups and of the
degree-zero divisor class groups `Cl⁰(F) ≃+ Cl⁰(F')`.

Isomorphic function fields therefore have isomorphic degree-zero divisor class groups, which is
how a class group computed for one model of a curve is transported to another model of it.

## Main declarations

* `Divisor.domCongr_equivOfRingEquiv_principal`: `τ` carries `div z` to `div (τ z)`;
* `Divisor.classGroupEquivOfRingEquiv`: the induced isomorphism `Cl(F) ≃+ Cl(F')`;
* `Divisor.degreeZeroClassGroupEquivOfRingEquiv`: its restriction `Cl⁰(F) ≃+ Cl⁰(F')`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section I.4.
-/

public section

namespace TauCeti

namespace Divisor

open AlgebraicGeometry

variable {k k' F F' : Type*} [Field k] [Field k'] [Field F] [Field F']
  [Algebra k F] [Algebra k' F']
variable (σ : k ≃+* k') (τ : F ≃+* F')
  (h : ∀ c, τ (algebraMap k F c) = algebraMap k' F' (σ c))
  (hF : IsFunctionField k F) (hF' : IsFunctionField k' F')

-- Transport rules run before `Finsupp.domCongr_apply` expands the divisor reindexing.
/-- **A semilinear field isomorphism transports principal divisors**: reindexing `div z` along the
induced bijection of places gives `div (τ z)`. -/
@[simp↓]
theorem domCongr_equivOfRingEquiv_principal (z : Fˣ) :
    Finsupp.domCongr (Place.equivOfRingEquiv σ τ h) (principal hF z) =
      principal hF' (Units.map (τ : F →* F') z) := by
  refine WeilDivisor.ext fun Q ↦ ?_
  obtain ⟨P, rfl⟩ := (Place.equivOfRingEquiv σ τ h).surjective Q
  simp only [WeilDivisor.coeff, Finsupp.domCongr_apply, Finsupp.equivMapDomain_apply,
    Equiv.symm_apply_apply]
  rw [← WeilDivisor.coeff, ← WeilDivisor.coeff, coeff_principal, coeff_principal,
    Place.ord_equivOfRingEquiv, Units.coe_map, MonoidHom.coe_ofClass, RingEquiv.symm_apply_apply]

/-- The principal divisors of the order systems of places, transported along a semilinear field
isomorphism. -/
private theorem domCongr_equivOfRingEquiv_principalDivisor (z : Additive Fˣ) :
    Finsupp.domCongr (Place.equivOfRingEquiv σ τ h) ((Place.orderSystem hF).principalDivisor z) =
      (Place.orderSystem hF').principalDivisor
        ((Units.mapEquiv (τ : F ≃* F')).toAdditive z) := by
  rw [principalDivisor_eq, principalDivisor_eq, domCongr_equivOfRingEquiv_principal σ τ h hF hF']
  rfl

/-- **The divisor class groups of isomorphic function fields are isomorphic**: a semilinear field
isomorphism `τ` sends the class of `D` to the class of its transport along the induced bijection
of places. -/
noncomputable def classGroupEquivOfRingEquiv :
    (Place.orderSystem hF).ClassGroup ≃+ (Place.orderSystem hF').ClassGroup :=
  WeilDivisor.OrderSystem.classGroupCongr (Place.equivOfRingEquiv σ τ h)
    (Units.mapEquiv (τ : F ≃* F')).toAdditive
    (domCongr_equivOfRingEquiv_principalDivisor σ τ h hF hF')

/-- `classGroupEquivOfRingEquiv` sends the class of `D` to the class of its transport. -/
@[simp]
theorem classGroupEquivOfRingEquiv_divisorClass (D : Divisor k F) :
    classGroupEquivOfRingEquiv σ τ h hF hF' ((Place.orderSystem hF).divisorClass D) =
      (Place.orderSystem hF').divisorClass (Finsupp.domCongr (Place.equivOfRingEquiv σ τ h) D) :=
  WeilDivisor.OrderSystem.classGroupCongr_divisorClass _ _ _ D

/-- The inverse of `classGroupEquivOfRingEquiv` sends the class of `D` to the class of its
transport back along the induced bijection of places. -/
@[simp]
theorem classGroupEquivOfRingEquiv_symm_divisorClass (D : Divisor k' F') :
    (classGroupEquivOfRingEquiv σ τ h hF hF').symm ((Place.orderSystem hF').divisorClass D) =
      (Place.orderSystem hF).divisorClass
        (Finsupp.domCongr (Place.equivOfRingEquiv σ τ h).symm D) :=
  WeilDivisor.OrderSystem.classGroupCongr_symm_divisorClass _ _ _ D

/-- `classGroupEquivOfRingEquiv` preserves the degree of a divisor class. -/
@[simp]
theorem degreeClass_classGroupEquivOfRingEquiv (c : (Place.orderSystem hF).ClassGroup) :
    degreeClass hF' (classGroupEquivOfRingEquiv σ τ h hF hF' c) = degreeClass hF c := by
  obtain ⟨D, rfl⟩ := (Place.orderSystem hF).divisorClass_surjective c
  rw [classGroupEquivOfRingEquiv_divisorClass, degreeClass_divisorClass, degreeClass_divisorClass,
    degree_domCongr_equivOfRingEquiv]

/-- **The degree-zero divisor class groups of isomorphic function fields are isomorphic**:
`Cl⁰(F) ≃+ Cl⁰(F')`, the restriction of `classGroupEquivOfRingEquiv`. -/
noncomputable def degreeZeroClassGroupEquivOfRingEquiv :
    (degreeClass hF).ker ≃+ (degreeClass hF').ker :=
  (AddEquiv.addSubgroupCongr (ker_degreeClass_eq_picZero hF)).trans <|
    (WeilDivisor.OrderSystem.picZeroCongr (Place.equivOfRingEquiv σ τ h)
      (Units.mapEquiv (τ : F ≃* F')).toAdditive
      (domCongr_equivOfRingEquiv_principalDivisor σ τ h hF hF') _ _
      (fun P ↦ by rw [Place.degree_equivOfRingEquiv])).trans
    (AddEquiv.addSubgroupCongr (ker_degreeClass_eq_picZero hF').symm)

/-- `degreeZeroClassGroupEquivOfRingEquiv` is the restriction of `classGroupEquivOfRingEquiv`. -/
@[simp]
theorem coe_degreeZeroClassGroupEquivOfRingEquiv_apply (c : (degreeClass hF).ker) :
    (degreeZeroClassGroupEquivOfRingEquiv σ τ h hF hF' c : (Place.orderSystem hF').ClassGroup) =
      classGroupEquivOfRingEquiv σ τ h hF hF' c :=
  WeilDivisor.OrderSystem.coe_picZeroCongr_apply _ _ _ _ _ _ _

/-- The inverse of `degreeZeroClassGroupEquivOfRingEquiv` is the restriction of the inverse of
`classGroupEquivOfRingEquiv`. -/
@[simp]
theorem coe_degreeZeroClassGroupEquivOfRingEquiv_symm_apply (c : (degreeClass hF').ker) :
    ((degreeZeroClassGroupEquivOfRingEquiv σ τ h hF hF').symm c :
        (Place.orderSystem hF).ClassGroup) =
      (classGroupEquivOfRingEquiv σ τ h hF hF').symm c :=
  WeilDivisor.OrderSystem.coe_picZeroCongr_symm_apply _ _ _ _ _ _ _

end Divisor

end TauCeti
