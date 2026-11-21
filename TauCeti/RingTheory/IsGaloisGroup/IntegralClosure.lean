/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.Galois.IsGaloisGroup
public import Mathlib.RingTheory.Invariant.Galois
public import TauCeti.FieldTheory.Galois.Restriction
public import TauCeti.RingTheory.LocalRing.FixedPoints
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import TauCeti.FieldTheory.Galois.IsGaloisGroup
import TauCeti.RingTheory.IntegralClosure.Transfer
import TauCeti.RingTheory.Invariant.Basic

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
in `M ^ H`, the subgroup `H` is a Galois group of `B / C`. The fourth statement records the
analogous result for the image of `Gal(M/L)` inside `Gal(M/K)` under restriction of scalars.

## Main results

* `IsGaloisGroup.of_isIntegralClosure`: a Galois group of `M / L` is a Galois group of the
  integral closure of `C` in `M` over `C`.
* `IsGaloisGroup.of_isIntegralClosure_tower`: the same for the integral closures of a common
  base `A` in `L` and in `M`.
* `IsGaloisGroup.of_isIntegralClosure_fixedField`: a subgroup `H` of `Gal(M/K)` is a Galois group
  of the integral closures of a common base in `M ^ H` and in `M`.
* `TauCeti.IsIntegralClosure.isGaloisGroup_fixedField_and_faithfulSMul`: the same, bundled with
  the injectivity of `C → B`, as used to set up instances for the fixed-field integral closure.
* `IsGaloisGroup.of_isIntegralClosure_range_restrictScalarsHom`: the image of `Gal(M/L)` in
  `Gal(M/K)` under restriction of scalars is a Galois group of the integral closure of `C` in `M`
  over `C`.
* `TauCeti.IsGaloisGroup.moduleFinite_of_isIntegrallyClosed`: conversely, starting from the
  rings, a domain `B` with a finite Galois group over a Noetherian integrally closed domain `A`
  embedding in `B` is a finite `A`-module.
* `TauCeti.fixedPointsSubalgebraIntegralClosureEquiv`: `(integralClosure A L)^H ≃ₐ[A]
  integralClosure A (fixedField H)`, together with its Galois-action equivariance, transfer of
  `IsLocalRing`, `AlgEquiv.restrictScalars_smul_integralClosure`,
  `TauCeti.algEquivEquivEmbeddingSubgroup_smul_integralClosure`, and `FaithfulSMul` instances on
  `integralClosure A L`.
-/

public section

/-- Restricting the scalars of an automorphism along `L / E / K` does not change its action on
`integralClosure A L`. -/
@[simp] theorem AlgEquiv.restrictScalars_smul_integralClosure {A K E L : Type*} [CommRing A]
    [CommRing K] [CommRing E] [CommRing L] [Algebra A L] [Algebra K E] [Algebra E L] [Algebra K L]
    [IsScalarTower K E L] [SMulCommClass (L ≃ₐ[K] L) A L] [SMulCommClass (L ≃ₐ[E] L) A L]
    (σ : L ≃ₐ[E] L) (x : integralClosure A L) :
    σ.restrictScalars K • x = σ • x :=
  Subtype.ext (by simp [AlgEquiv.smul_def])

/-- Acting on `integralClosure A L` by `σ : L ≃ₐ[E] L` agrees with acting via
`TauCeti.algEquivEquivEmbeddingSubgroup K E L σ : TauCeti.embeddingSubgroup K E L`. -/
@[simp] theorem TauCeti.algEquivEquivEmbeddingSubgroup_smul_integralClosure {A K E L : Type*}
    [CommRing A] [Field K] [Field E] [Field L] [Algebra A L] [Algebra K E] [Algebra E L]
    [Algebra K L] [IsScalarTower K E L] [SMulCommClass (L ≃ₐ[K] L) A L]
    [SMulCommClass (L ≃ₐ[E] L) A L] (σ : L ≃ₐ[E] L) (x : integralClosure A L) :
    (TauCeti.algEquivEquivEmbeddingSubgroup K E L σ :
      TauCeti.embeddingSubgroup K E L) • x = σ • x :=
  Subtype.ext (by simp [Subgroup.smul_def, AlgEquiv.smul_def])

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
  (H : Subgroup Gal(M/K)) [Algebra A (IntermediateField.fixedField H)]
  [IsScalarTower A K (IntermediateField.fixedField H)]
  (C B : Type*) [CommRing C] [Algebra A C] [Algebra C (IntermediateField.fixedField H)]
  [IsScalarTower A C (IntermediateField.fixedField H)]
  [IsIntegralClosure C A (IntermediateField.fixedField H)] [CommRing B]
  [Algebra A B] [Algebra B M] [IsScalarTower A B M] [IsIntegralClosure B A M] [Algebra C B]
  [Algebra C M] [IsScalarTower A C B] [IsScalarTower C (IntermediateField.fixedField H) M]
  [IsScalarTower C B M]
  [MulSemiringAction Gal(M/K) B] [SMulDistribClass Gal(M/K) B M]

include A K in
/-- **Fixed-field subgroups as Galois groups of integral closures.** Let `A` be a domain with
fraction field `K`, let `M / K` be a finite extension, and let `H` be a subgroup of `Gal(M/K)`. If
`C` and `B` are the integral closures of `A` in the fixed field `M ^ H` and in `M`, then `H` is a
Galois group of `B` over `C`. The extension `M / K` need not be Galois. -/
theorem of_isIntegralClosure_fixedField : IsGaloisGroup H C B :=
  have : IsGalois (IntermediateField.fixedField H) M := IsGalois.of_fixed_field M H
  have : IsGaloisGroup H (IntermediateField.fixedField H) M :=
    of_mulEquiv_algEquiv (subgroupEquivAlgEquiv H) fun _ _ ↦ rfl
  of_isIntegralClosure_tower H A K (IntermediateField.fixedField H) M C B

include A in
/-- The subgroup `H` is a Galois group of `B` over `C`, and `C` embeds in `B`. -/
theorem _root_.TauCeti.IsIntegralClosure.isGaloisGroup_fixedField_and_faithfulSMul :
    IsGaloisGroup H C B ∧ FaithfulSMul C B := by
  have : FaithfulSMul C (IntermediateField.fixedField H) :=
    IsIntegralClosure.faithfulSMul A C (IntermediateField.fixedField H)
  have : FaithfulSMul C M := .trans C (IntermediateField.fixedField H) M
  exact ⟨IsGaloisGroup.of_isIntegralClosure_fixedField A H C B, .tower_bot C B M⟩

end FixedField

section RestrictScalars

variable (K L M C B : Type*) [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M] [IsGalois L M]
  [CommRing C] [CommRing B] [Algebra C B] [Algebra C L] [Algebra C M] [Algebra B M]
  [IsScalarTower C L M] [IsScalarTower C B M] [IsFractionRing C L] [IsIntegrallyClosed C]
  [IsIntegralClosure B C M] [MulSemiringAction Gal(M/K) B] [SMulDistribClass Gal(M/K) B M]

/-- **Restricted-scalars subgroups as Galois groups of integral closures.** Let `K ⊆ L ⊆ M` be a
tower of fields with `M / L` Galois, let `C` be an integrally closed domain with fraction field `L`,
and let `B` be the integral closure of `C` in `M`. Then the image of `Gal(M/L)` in `Gal(M/K)` under
restriction of scalars is a Galois group of `B` over `C`. -/
theorem of_isIntegralClosure_range_restrictScalarsHom :
    IsGaloisGroup (AlgEquiv.restrictScalarsHom K : Gal(M/L) →* Gal(M/K)).range C B :=
  have : IsGaloisGroup (AlgEquiv.restrictScalarsHom K : Gal(M/L) →* Gal(M/K)).range L M :=
    range_restrictScalarsHom K L M
  of_isIntegralClosure _ C B L M

end RestrictScalars

end IsGaloisGroup

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra in
/-- If a finite group `G` is a Galois group of a domain `B` over a Noetherian integrally closed
domain `A` embedding in `B`, then `B` is a finite `A`-module. -/
theorem TauCeti.IsGaloisGroup.moduleFinite_of_isIntegrallyClosed (G A B : Type*) [Group G]
    [Finite G] [CommRing A] [IsIntegrallyClosed A] [IsNoetherianRing A] [CommRing B] [IsDomain B]
    [Algebra A B] [FaithfulSMul A B] [MulSemiringAction G B] [IsGaloisGroup G A B] :
    Module.Finite A B := by
  have : IsDomain A := .of_faithfulSMul A B
  let := IsFractionRing.mulSemiringAction G B (FractionRing B)
  have := IsGaloisGroup.isGalois G (FractionRing A) (FractionRing B)
  have := IsGaloisGroup.finiteDimensional G (FractionRing A) (FractionRing B)
  have := Algebra.IsInvariant.isIntegral A B G
  -- `B` embeds `A`-linearly in the integral closure of `A` in `Frac B`, which is finite over `A`.
  have := IsIntegralClosure.finite A (FractionRing A) (FractionRing B)
    (integralClosure A (FractionRing B))
  exact TauCeti.IsIntegralClosure.finite_of_injective (C' := integralClosure A (FractionRing B))
    (IsScalarTower.toAlgHom A B (FractionRing B)) (IsFractionRing.injective B (FractionRing B))

namespace TauCeti

section FaithfulSMul
variable {G A L : Type*} [CommRing A] [Field L] [Algebra A L] [Group G] [MulSemiringAction G L]
  [SMulCommClass G A L] [FaithfulSMul G L]
/-- A faithful group action on a field `L` restricts faithfully to `integralClosure A L` whenever
`L` is a fraction field of `integralClosure A L`. -/
instance instFaithfulSMulIntegralClosureOfIsFractionRing [IsFractionRing (integralClosure A L) L] :
    FaithfulSMul G (integralClosure A L) :=
  ⟨fun h ↦ eq_of_smul_eq_smul fun y : L ↦ by
    obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (integralClosure A L) y
    simp only [smul_div₀', ← algebraMap.coe_smul', h]⟩
/-- A faithful group action on an algebraic field extension `L` over an embedded base ring `A`
restricts faithfully to `integralClosure A L`. -/
instance instFaithfulSMulIntegralClosureOfIsAlgebraic [FaithfulSMul A L] [Algebra.IsAlgebraic A L] :
    FaithfulSMul G (integralClosure A L) :=
  letI := IsIntegralClosure.isFractionRing_of_algebraic A (integralClosure A L)
    fun _ ↦ (FaithfulSMul.algebraMap_eq_zero_iff A L).mp
  inferInstance
end FaithfulSMul
/-- For an algebraic extension `L / K` over a fraction field `K` of `A`, `L ≃ₐ[K] L` acts
faithfully on `integralClosure A L`. -/
instance instFaithfulSMulAlgEquivIntegralClosure {A K L : Type*} [CommRing A] [Field K] [Field L]
    [Algebra A K] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsFractionRing A K]
    [Algebra.IsAlgebraic K L] : FaithfulSMul (L ≃ₐ[K] L) (integralClosure A L) :=
  have : IsDomain A := (IsFractionRing.injective A K).isDomain _
  have : FaithfulSMul A L := .trans A K L
  have : Algebra.IsAlgebraic A L := IsFractionRing.comap_isAlgebraic_iff.mpr ‹_›
  inferInstance

section FixedFieldEquiv
open IntermediateField
variable (A : Type*) {K L : Type*} [CommRing A] [Field K] [Field L] [Algebra A K] [Algebra K L]
  [Algebra A L] [IsScalarTower A K L] (H : Subgroup (L ≃ₐ[K] L))
/-- The `A`-subalgebra of `H`-fixed elements of `integralClosure A L` is isomorphic as an
`A`-algebra to `integralClosure A (IntermediateField.fixedField H)`. -/
def fixedPointsSubalgebraIntegralClosureEquiv :
    FixedPoints.subalgebra A (integralClosure A L) H ≃ₐ[A] integralClosure A (fixedField H) :=
  haveI := IsScalarTower.to₁₃₄ A K (fixedField H) L
  { toFun x := ⟨⟨(x.val : L), fun h ↦ congrArg Subtype.val (x.property h)⟩,
      (isIntegral_algHom_iff (IsScalarTower.toAlgHom A (fixedField H) L)
        (fixedField H).val.injective).mp x.val.property⟩
    invFun y := ⟨⟨(y.val : L), y.property.map (IsScalarTower.toAlgHom A (fixedField H) L)⟩,
      fun h ↦ Subtype.ext (y.val.property h)⟩
    left_inv _ := rfl, right_inv _ := rfl, map_mul' _ _ := rfl, map_add' _ _ := rfl
    commutes' r := Subtype.ext <| Subtype.ext <| by
      simp [IsScalarTower.algebraMap_apply A K L r,
        IsScalarTower.algebraMap_apply A K (fixedField H) r] }
@[simp] theorem coe_fixedPointsSubalgebraIntegralClosureEquiv_apply
    (x : FixedPoints.subalgebra A (integralClosure A L) H) :
    (((fixedPointsSubalgebraIntegralClosureEquiv A H x : integralClosure A (fixedField H)) :
      fixedField H) : L) = ((x : integralClosure A L) : L) := (rfl)
@[simp] theorem coe_fixedPointsSubalgebraIntegralClosureEquiv_symm_apply
    (y : integralClosure A (fixedField H)) :
    (((fixedPointsSubalgebraIntegralClosureEquiv A H).symm y : integralClosure A L) : L) =
      ((y : fixedField H) : L) := (rfl)
section Galois
variable [FiniteDimensional K L] [IsGalois K L] [H.Normal]
/-- `fixedPointsSubalgebraIntegralClosureEquiv` intertwines the quotient action of `Gal(L/K) ⧸ H`
with the Galois action of `Gal(fixedField H / K)` via `IsGalois.normalAutEquivQuotient H`. -/
theorem fixedPointsSubalgebraIntegralClosureEquiv_smul (q : (L ≃ₐ[K] L) ⧸ H)
    (x : FixedPoints.subalgebra A (integralClosure A L) H) :
    fixedPointsSubalgebraIntegralClosureEquiv A H (q • x) =
      IsGalois.normalAutEquivQuotient H q • fixedPointsSubalgebraIntegralClosureEquiv A H x := by
  induction q using QuotientGroup.induction_on with | H σ =>
    exact Subtype.ext <| Subtype.ext <| by
      simp [IsGalois.normalAutEquivQuotient_apply, AlgEquiv.restrictNormalHom_apply,
        AlgEquiv.smul_def, Subgroup.coe_mk_smul]
/-- `(fixedPointsSubalgebraIntegralClosureEquiv A H).symm` intertwines the Galois action of
`Gal(fixedField H / K)` with `(IsGalois.normalAutEquivQuotient H).symm`. -/
theorem fixedPointsSubalgebraIntegralClosureEquiv_symm_smul (τ : fixedField H ≃ₐ[K] fixedField H)
    (y : integralClosure A (fixedField H)) :
    (fixedPointsSubalgebraIntegralClosureEquiv A H).symm (τ • y) =
      (IsGalois.normalAutEquivQuotient H).symm τ •
        (fixedPointsSubalgebraIntegralClosureEquiv A H).symm y :=
  (fixedPointsSubalgebraIntegralClosureEquiv A H).injective <| by
    simp [fixedPointsSubalgebraIntegralClosureEquiv_smul]
end Galois
variable {A H} in
/-- If `integralClosure A L` is local, so is `integralClosure A (fixedField H)`. -/
instance instIsLocalRingIntegralClosureFixedField [IsLocalRing (integralClosure A L)] :
    IsLocalRing (integralClosure A (fixedField H)) :=
  (fixedPointsSubalgebraIntegralClosureEquiv A H).toRingEquiv.isLocalRing
end FixedFieldEquiv

end TauCeti
