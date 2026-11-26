/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Invariant.Basic
import TauCeti.RingTheory.Invariant.Basic

/-!
# Integral elements fixed by a Galois group

Let `R` be integrally closed in a field `K` and let `L / K` be a Galois extension, possibly
infinite. An element of `L` lies in the image of `R` exactly when it is integral over `R` and
fixed by every `K`-automorphism of `L`. This combines the fixed-field theorem for infinite Galois
extensions with the integral closedness of `R` in `K`. For instance, an algebraic integer in an
algebraic closure of `ℚ` fixed by the absolute Galois group is a rational integer.

Mathlib's `Algebra.isInvariant_of_isGalois` records the analogous fact for a finite Galois
extension of the fraction field of an integrally closed domain, phrased through the integral
closure of that domain in `L`. We also record the corresponding `Algebra.IsInvariant` instance on
`integralClosure R L` and the canonical isomorphism between the `H`-invariants of
`integralClosure R L` and `integralClosure R (IntermediateField.fixedField H)`.

## Main results

* `TauCeti.InfiniteGalois.mem_range_algebraMap_iff_isIntegral_and_fixed`: an element of a Galois
  extension `L / K` comes from `R` if and only if it is integral over `R` and fixed by `Gal(L/K)`.
* `TauCeti.InfiniteGalois.isInvariant_integralClosure`: `R → integralClosure R L` is an invariant
  extension for `Gal(L/K)`.
* `TauCeti.fixedPointsIntegralClosureEquivFixedField`: canonical ring isomorphism between
  `FixedPoints.subring (integralClosure R L) H` and
  `integralClosure R (IntermediateField.fixedField H)`, equivariant along
  `IsGalois.normalAutEquivQuotient`.
-/

public section

namespace TauCeti.InfiniteGalois

variable {R K L : Type*} [CommRing R] [Field K] [Field L] [Algebra R K] [Algebra K L]
  [Algebra R L] [IsScalarTower R K L] [IsIntegrallyClosedIn R K] [IsGalois K L]

variable (K) in
/-- For `R` integrally closed in `K` and a Galois extension `L / K`, an element of `L` comes from
`R` if and only if it is integral over `R` and fixed by every `K`-automorphism of `L`. -/
theorem mem_range_algebraMap_iff_isIntegral_and_fixed (x : L) :
    x ∈ Set.range (algebraMap R L) ↔ IsIntegral R x ∧ ∀ τ : Gal(L/K), τ x = x := by
  refine ⟨?_, fun ⟨hx, hfix⟩ ↦ ?_⟩
  · rintro ⟨r, rfl⟩
    refine ⟨isIntegral_algebraMap, fun τ ↦ ?_⟩
    rw [IsScalarTower.algebraMap_apply R K L, τ.commutes]
  obtain ⟨q, rfl⟩ := (_root_.InfiniteGalois.mem_range_algebraMap_iff_fixed x).mpr hfix
  obtain ⟨r, rfl⟩ := IsIntegrallyClosedIn.isIntegral_iff.mp <|
    (isIntegral_algHom_iff ((Algebra.ofId K L).restrictScalars R)
      (algebraMap K L).injective).mp hx
  exact ⟨r, IsScalarTower.algebraMap_apply R K L r⟩

variable (R K L) in
/-- If `R` is integrally closed in `K` and `L / K` is Galois, then `R → integralClosure R L` is an
invariant extension for `Gal(L/K)`. -/
theorem isInvariant_integralClosure :
    Algebra.IsInvariant R (integralClosure R L) (L ≃ₐ[K] L) where
  isInvariant x hx := by
    obtain ⟨r, hr⟩ := (mem_range_algebraMap_iff_isIntegral_and_fixed K x.val).2
      ⟨x.property, fun τ ↦ congrArg Subtype.val (hx τ)⟩
    exact ⟨r, Subtype.ext hr⟩

end TauCeti.InfiniteGalois

namespace TauCeti

variable (R K L : Type*) [CommRing R] [Field K] [Field L]
  [Algebra R K] [Algebra K L] [Algebra R L] [IsScalarTower R K L]

/-- The canonical ring isomorphism identifying the `H`-fixed points of `integralClosure R L` with
`integralClosure R (IntermediateField.fixedField H)`. -/
def fixedPointsIntegralClosureEquivFixedField (H : Subgroup (L ≃ₐ[K] L)) :
    FixedPoints.subring (integralClosure R L) H ≃+*
      integralClosure R (IntermediateField.fixedField H) where
  toFun x :=
    ⟨⟨x.val.val, fun σ ↦ congrArg Subtype.val (x.property σ)⟩,
      (isIntegral_algHom_iff ((IntermediateField.fixedField H).val.restrictScalars R)
        Subtype.val_injective).1 x.val.property⟩
  invFun y :=
    ⟨⟨y.val.val, (isIntegral_algHom_iff ((IntermediateField.fixedField H).val.restrictScalars R)
        Subtype.val_injective).2 y.property⟩,
      fun σ ↦ Subtype.ext (y.val.property σ)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

/-- `fixedPointsIntegralClosureEquivFixedField` preserves the underlying element of `L`. -/
@[simp]
theorem coe_fixedPointsIntegralClosureEquivFixedField (H : Subgroup (L ≃ₐ[K] L))
    (x : FixedPoints.subring (integralClosure R L) H) :
    ((fixedPointsIntegralClosureEquivFixedField R K L H x :
        integralClosure R (IntermediateField.fixedField H)) : L) =
      ((x : integralClosure R L) : L) :=
  (rfl)

/-- The inverse of `fixedPointsIntegralClosureEquivFixedField` preserves the underlying element of
`L`. -/
@[simp]
theorem coe_fixedPointsIntegralClosureEquivFixedField_symm (H : Subgroup (L ≃ₐ[K] L))
    (y : integralClosure R (IntermediateField.fixedField H)) :
    (((fixedPointsIntegralClosureEquivFixedField R K L H).symm y : integralClosure R L) : L) =
      (y : L) :=
  (rfl)

/-- `fixedPointsIntegralClosureEquivFixedField` is equivariant along
`IsGalois.normalAutEquivQuotient`. -/
theorem fixedPointsIntegralClosureEquivFixedField_smul
    [FiniteDimensional K L] [IsGalois K L] (H : Subgroup (L ≃ₐ[K] L)) [H.Normal]
    (q : (L ≃ₐ[K] L) ⧸ H) (x : FixedPoints.subring (integralClosure R L) H) :
    fixedPointsIntegralClosureEquivFixedField R K L H (q • x) =
      IsGalois.normalAutEquivQuotient H q •
        fixedPointsIntegralClosureEquivFixedField R K L H x := by
  refine QuotientGroup.induction_on q fun σ ↦ ?_
  ext
  simp only [coe_fixedPointsIntegralClosureEquivFixedField, Subgroup.coe_mk_smul_subring,
    integralClosure.coe_smul, IsGalois.normalAutEquivQuotient_apply]
  exact (AlgEquiv.restrictNormal_commutes σ (IntermediateField.fixedField H)
    ⟨x.val.val, fun τ ↦ congrArg Subtype.val (x.property τ)⟩).symm

end TauCeti

end
