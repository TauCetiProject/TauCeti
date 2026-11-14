/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.Galois.IsGaloisGroup
public import Mathlib.RingTheory.Invariant.Galois

/-!
# Galois groups of integral closures

If `G` is a Galois group of an algebraic field extension `M / L` and `C` is an integrally closed
domain with fraction field `L`, then `G` is a Galois group of the integral closure `B` of `C` in
`M` over `C`, for any action of `G` on `B` compatible with its action on `M`. The group `G` need
not be finite.

Mathlib's `IsGaloisGroup.of_isFractionRing` states this with `M` a fraction field of `B` and
`B / C` integral; both follow from `B` being the integral closure of `C` in `M`, which is how the
rings arise over a Dedekind base. The second statement is the form needed for a tower: for a
domain `A` with fraction field `K`, an algebraic extension `L` of `K`, an algebraic extension `M`
of `L`, and the integral closures `C` and `B` of `A` in `L` and in `M`, a Galois group of `M / L`
is a Galois group of `B / C`. The third statement specializes the tower to a fixed field: for a
finite extension `M / K` and a subgroup `H` of `Gal(M/K)`, with `C` the integral closure of `A`
in `M ^ H`, the subgroup `H` is a Galois group of `B / C`.

## Main results

* `IsGaloisGroup.of_isIntegralClosure`: a Galois group of `M / L` is a Galois group of the
  integral closure of `C` in `M` over `C`.
* `IsGaloisGroup.of_isIntegralClosure_tower`: the same for the integral closures of a common
  base `A` in `L` and in `M`.
* `IsGaloisGroup.of_isIntegralClosure_fixedField`: a subgroup `H` of `Gal(M/K)` is a Galois group
  of the integral closures of a common base in `M ^ H` and in `M`.
* `TauCeti.IsIntegralClosure.isGaloisGroup_fixedField_and_faithfulSMul`: the same, bundled with
  the injectivity of `C → B`, as used to set up instances for the fixed-field integral closure.
* `TauCeti.fixedPointsSubalgebraIntegralClosureEquiv`: `(integralClosure A L)^H ≃ₐ[A]
  integralClosure A (fixedField H)`.
-/

public section

/-- The action of `Gal(L/K)` on an integral closure `B` of `A` in `L` commutes with the action of
`A`, since it is the restriction of the action by `K`-algebra automorphisms of `L`. -/
theorem IsIntegralClosure.smulCommClass (A K L B : Type*)
    [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A K] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [Algebra A B] [Algebra B L] [IsScalarTower A B L]
    [IsFractionRing A K] [IsIntegralClosure B A L] [Algebra.IsAlgebraic K L] :
    letI := IsIntegralClosure.MulSemiringAction A K L B
    SMulCommClass (L ≃ₐ[K] L) A B :=
  letI := IsIntegralClosure.MulSemiringAction A K L B
  ⟨fun σ a b ↦ map_smul (galRestrict A K L B σ) a b⟩

namespace IsGaloisGroup

section IntegrallyClosed

variable (G C B L M : Type*) [Group G] [CommRing C] [CommRing B]
  [Algebra C B] [Field L] [Field M] [Algebra C L] [Algebra L M] [Algebra.IsAlgebraic L M]
  [Algebra C M] [Algebra B M] [IsScalarTower C L M] [IsScalarTower C B M] [IsFractionRing C L]
  [IsIntegrallyClosed C] [IsIntegralClosure B C M] [MulSemiringAction G M] [MulSemiringAction G B]
  [SMulDistribClass G B M]

/-- **A Galois group of fields is a Galois group of integral closures.** If `G` is a Galois group
of an algebraic extension `M / L`, where `L` is the fraction field of an integrally closed domain
`C`, then `G` is a Galois group of the integral closure of `C` in `M` over `C`. The group `G` need
not be finite. -/
theorem of_isIntegralClosure [IsGaloisGroup G L M] : IsGaloisGroup G C B :=
  have : IsDomain C := (IsFractionRing.injective C L).isDomain _
  have : IsDomain B := (IsIntegralClosure.algebraMap_injective B C M).isDomain _
  have : Algebra.IsAlgebraic C M := IsFractionRing.comap_isAlgebraic_iff.mpr ‹_›
  have : FaithfulSMul C M := .trans C L M
  have : IsFractionRing B M := IsIntegralClosure.isFractionRing_of_algebraic C B
    fun _ ↦ (FaithfulSMul.algebraMap_eq_zero_iff C M).mp
  have : Algebra.IsIntegral C B := IsIntegralClosure.isIntegral_algebra C M
  of_isFractionRing G C B L M

end IntegrallyClosed

section Tower

variable (G A K L M C B : Type*) [Group G] [CommRing A] [IsDomain A] [Field K]
  [Algebra A K] [IsFractionRing A K] [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
  [Algebra.IsAlgebraic K L] [Field M] [Algebra L M] [Algebra.IsAlgebraic L M] [Algebra A M]
  [CommRing C] [Algebra A C]
  [Algebra C L] [IsScalarTower A C L] [IsIntegralClosure C A L] [CommRing B] [Algebra A B]
  [Algebra B M] [IsScalarTower A B M] [IsIntegralClosure B A M] [Algebra C B] [Algebra C M]
  [IsScalarTower A C B] [IsScalarTower C L M] [IsScalarTower C B M]
  [MulSemiringAction G M] [MulSemiringAction G B] [SMulDistribClass G B M]

include A K in
/-- **Galois groups in a tower of integral closures.** Let `A` be a domain with fraction field
`K`, let `L` be an algebraic extension of `K` and `M` an algebraic extension of `L`, and let `C`
and `B` be the integral closures of `A` in `L` and in `M`. A Galois group of `M / L` is then a
Galois group of `B` over `C`. -/
theorem of_isIntegralClosure_tower [IsGaloisGroup G L M] : IsGaloisGroup G C B :=
  have : IsDomain C := (IsIntegralClosure.algebraMap_injective C A L).isDomain _
  have : Algebra.IsAlgebraic A L := IsFractionRing.comap_isAlgebraic_iff.mpr ‹_›
  have : FaithfulSMul A L := .trans A K L
  have : IsFractionRing C L := IsIntegralClosure.isFractionRing_of_algebraic A C
    fun _ ↦ (FaithfulSMul.algebraMap_eq_zero_iff A L).mp
  have : IsIntegrallyClosed C := (isIntegrallyClosed_iff_isIntegrallyClosedIn L).mpr
    (IsIntegrallyClosedIn.of_isIntegralClosure A)
  have : Algebra.IsIntegral A C := IsIntegralClosure.isIntegral_algebra A L
  have : IsScalarTower A C M := .of_algebraMap_eq' <| by
    rw [IsScalarTower.algebraMap_eq A B M, IsScalarTower.algebraMap_eq A C B,
      ← RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq C B M]
  have : IsIntegralClosure B C M := IsIntegralClosure.tower_top (R := A)
  of_isIntegralClosure G C B L M

end Tower

section FixedField

open IntermediateField

variable (A : Type*) {K M : Type*} [CommRing A] [IsDomain A] [Field K] [Algebra A K]
  [IsFractionRing A K] [Field M] [Algebra K M] [FiniteDimensional K M] [Algebra A M]
  (H : Subgroup Gal(M/K)) [Algebra A (fixedField H)] [IsScalarTower A K (fixedField H)]
  (C B : Type*) [CommRing C] [Algebra A C] [Algebra C (fixedField H)]
  [IsScalarTower A C (fixedField H)] [IsIntegralClosure C A (fixedField H)] [CommRing B]
  [Algebra A B] [Algebra B M] [IsScalarTower A B M] [IsIntegralClosure B A M] [Algebra C B]
  [Algebra C M] [IsScalarTower A C B] [IsScalarTower C (fixedField H) M] [IsScalarTower C B M]
  [MulSemiringAction Gal(M/K) B] [SMulDistribClass Gal(M/K) B M]

include A K in
/-- **Fixed-field subgroups as Galois groups of integral closures.** Let `A` be a domain with
fraction field `K`, let `M / K` be a finite extension, and let `H` be a subgroup of `Gal(M/K)`. If
`C` and `B` are the integral closures of `A` in the fixed field `M ^ H` and in `M`, then `H` is a
Galois group of `B` over `C`. The extension `M / K` need not be Galois. -/
theorem of_isIntegralClosure_fixedField : IsGaloisGroup H C B :=
  have : IsGalois (fixedField H) M := IsGalois.of_fixed_field M H
  have : IsGaloisGroup H (fixedField H) M :=
    of_mulEquiv_algEquiv (subgroupEquivAlgEquiv H) fun _ _ ↦ rfl
  of_isIntegralClosure_tower H A K (fixedField H) M C B

include A in
/-- The subgroup `H` is a Galois group of `B` over `C`, and `C` embeds in `B`. -/
theorem _root_.TauCeti.IsIntegralClosure.isGaloisGroup_fixedField_and_faithfulSMul :
    IsGaloisGroup H C B ∧ FaithfulSMul C B := by
  have : FaithfulSMul C (fixedField H) := IsIntegralClosure.faithfulSMul A C (fixedField H)
  have : FaithfulSMul C M := .trans C (fixedField H) M
  exact ⟨IsGaloisGroup.of_isIntegralClosure_fixedField A H C B, .tower_bot C B M⟩

end FixedField

end IsGaloisGroup

namespace TauCeti

section FixedFieldIntegralClosure

open IntermediateField

variable (A : Type*) {K L : Type*} [CommRing A] [Field K] [Field L]
  [Algebra A K] [Algebra K L] [Algebra A L] [IsScalarTower A K L]

/-- The `A`-subalgebra of `H`-fixed elements of `integralClosure A L` is isomorphic as an
`A`-algebra to `integralClosure A (IntermediateField.fixedField H)`. -/
def fixedPointsSubalgebraIntegralClosureEquiv (H : Subgroup (L ≃ₐ[K] L)) :
    FixedPoints.subalgebra A (integralClosure A L) H ≃ₐ[A]
      integralClosure A (fixedField H) where
  toFun x := ⟨⟨(x.1 : L), fun h ↦ congrArg Subtype.val (x.2 h)⟩, by
    have : IsScalarTower A (fixedField H) L := IsScalarTower.of_algebraMap_eq' rfl
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom A (fixedField H) L)
      (fixedField H).val.injective).mp x.1.2⟩
  invFun y := ⟨⟨(y.1 : L), by
    have : IsScalarTower A (fixedField H) L := IsScalarTower.of_algebraMap_eq' rfl
    exact y.2.map (IsScalarTower.toAlgHom A (fixedField H) L)⟩,
    fun h ↦ Subtype.ext (y.1.2 h)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' r := Subtype.ext <| Subtype.ext <| by
    simp [IsScalarTower.algebraMap_apply A K L r,
      IsScalarTower.algebraMap_apply A K (fixedField H) r]

/-- Forward coercion to `L` of `fixedPointsSubalgebraIntegralClosureEquiv`. -/
@[simp]
theorem coe_fixedPointsSubalgebraIntegralClosureEquiv_apply (H : Subgroup (L ≃ₐ[K] L))
    (x : FixedPoints.subalgebra A (integralClosure A L) H) :
    (((fixedPointsSubalgebraIntegralClosureEquiv A H x :
      integralClosure A (fixedField H)) : fixedField H) : L) = ((x : integralClosure A L) : L) := by
  rfl

/-- Inverse coercion to `L` of `fixedPointsSubalgebraIntegralClosureEquiv`. -/
@[simp]
theorem coe_fixedPointsSubalgebraIntegralClosureEquiv_symm_apply (H : Subgroup (L ≃ₐ[K] L))
    (y : integralClosure A (fixedField H)) :
    (((fixedPointsSubalgebraIntegralClosureEquiv A H).symm y :
      integralClosure A L) : L) = ((y : fixedField H) : L) := by
  rfl

end FixedFieldIntegralClosure

end TauCeti
