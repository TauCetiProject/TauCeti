/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import TauCeti.RingTheory.Invariant.Basic
public import TauCeti.RingTheory.IsGaloisGroup.IntegralClosure
public import TauCeti.RingTheory.LocalRing.FixedPoints

/-!
# Fixed-point subrings and subalgebras of discrete valuation rings

When a monoid `G` acts by ring endomorphisms on a discrete valuation ring `B`, choosing a nonzero
element of minimal additive valuation in any nonzero ideal shows that `FixedPoints.subring B G` and
`FixedPoints.subalgebra A B G` are principal ideal domains. When `G` is a finite group — or when
`(maximalIdeal A).map (algebraMap A B) ≠ ⊥`, e.g. when `B` lies locally and faithfully over a
discrete valuation ring `A` — the fixed ring cannot be a field and is a discrete valuation ring.
Applying this to `integralClosure A L` transfers `IsLocalRing` and `IsDiscreteValuationRing` to
`integralClosure A E` in field towers and to `integralClosure A (IntermediateField.fixedField H)`.
-/

public section

open IsLocalRing

namespace TauCeti

section IsDiscreteValuationRing

/-- The fixed-point subring of a discrete valuation ring under any monoid action is a principal
ideal ring. -/
instance instIsPrincipalIdealRingFixedPointsSubring {B G : Type*} [CommRing B] [IsDomain B]
    [_root_.IsDiscreteValuationRing B] [Monoid G] [MulSemiringAction G B] :
    IsPrincipalIdealRing (FixedPoints.subring B G) where
  principal I := by
    by_cases hI : I = ⊥
    · exact ⟨0, by simp [hI]⟩
    obtain ⟨x₀, hx₀I, hx₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
    let f : {x : FixedPoints.subring B G // x ∈ I ∧ x ≠ 0} → ℕ :=
      fun z ↦ (_root_.IsDiscreteValuationRing.addVal B (z.1 : B)).toNat
    obtain ⟨⟨a, haI, ha0⟩, -, hmin⟩ :=
      (InvImage.wf f Nat.lt_wfRel.wf).has_min Set.univ ⟨⟨x₀, hx₀I, hx₀0⟩, trivial⟩
    refine ⟨a, le_antisymm (fun y hyI ↦ ?_) (Ideal.span_le.2 (Set.singleton_subset_iff.2 haI))⟩
    by_cases hy0 : y = 0
    · simp [hy0]
    have ha_top : _root_.IsDiscreteValuationRing.addVal B (a : B) ≠ ⊤ :=
      _root_.IsDiscreteValuationRing.addVal_eq_top_iff.not.2 (Subtype.coe_ne_coe.2 ha0)
    have hy_top : _root_.IsDiscreteValuationRing.addVal B (y : B) ≠ ⊤ :=
      _root_.IsDiscreteValuationRing.addVal_eq_top_iff.not.2 (Subtype.coe_ne_coe.2 hy0)
    have hle : _root_.IsDiscreteValuationRing.addVal B (a : B) ≤
        _root_.IsDiscreteValuationRing.addVal B (y : B) := by
      rw [← ENat.natCast_toNat ha_top, ← ENat.natCast_toNat hy_top]
      exact_mod_cast not_lt.1 (hmin ⟨y, hyI, hy0⟩ trivial)
    exact Ideal.mem_span_singleton.2
      (dvd_coe_fixedPoints_subring_iff.1 (_root_.IsDiscreteValuationRing.addVal_le_iff_dvd.1 hle))

/-- The fixed-point subalgebra of a discrete valuation ring under any monoid action is a principal
ideal ring. -/
instance instIsPrincipalIdealRingFixedPointsSubalgebra {A B G : Type*} [CommSemiring A]
    [CommRing B] [IsDomain B] [_root_.IsDiscreteValuationRing B] [Algebra A B] [Monoid G]
    [MulSemiringAction G B] [SMulCommClass G A B] :
    IsPrincipalIdealRing (FixedPoints.subalgebra A B G) :=
  IsPrincipalIdealRing.of_surjective (fixedPointsSubringEquivSubalgebra A B G).toRingHom
    (fixedPointsSubringEquivSubalgebra A B G).surjective

/-- The fixed-point subalgebra of a discrete valuation ring under a finite group action is a
discrete valuation ring. -/
instance instIsDiscreteValuationRingFixedPointsSubalgebra {A B G : Type*} [CommRing A] [CommRing B]
    [IsDomain B] [_root_.IsDiscreteValuationRing B] [Algebra A B] [Group G] [Finite G]
    [MulSemiringAction G B] [SMulCommClass G A B] :
    _root_.IsDiscreteValuationRing (FixedPoints.subalgebra A B G) where
  not_a_field' hbot :=
    _root_.IsDiscreteValuationRing.not_isField B
      (((Algebra.IsInvariant.isIntegral (FixedPoints.subalgebra A B G) B G).isField_iff_isField
        (FaithfulSMul.algebraMap_injective (FixedPoints.subalgebra A B G) B)).mp
        (isField_iff_maximalIdeal_eq.2 hbot))

/-- The fixed-point subring of a discrete valuation ring under a finite group action is a discrete
valuation ring. -/
instance instIsDiscreteValuationRingFixedPointsSubring {B G : Type*} [CommRing B] [IsDomain B]
    [_root_.IsDiscreteValuationRing B] [Group G] [Finite G] [MulSemiringAction G B] :
    _root_.IsDiscreteValuationRing (FixedPoints.subring B G) :=
  _root_.IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
    (fixedPointsSubringEquivSubalgebra ℤ B G).symm

/-- When a discrete valuation ring `B` lies locally over a local ring `A` whose maximal ideal has
nonzero image in `B`, `FixedPoints.subalgebra A B G` is a discrete valuation ring for any monoid
`G`. -/
theorem isDiscreteValuationRing_fixedPoints_subalgebra_of_map_maximalIdeal_ne_bot {A B G : Type*}
    [CommRing A] [IsLocalRing A] [CommRing B] [IsDomain B] [_root_.IsDiscreteValuationRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Monoid G] [MulSemiringAction G B]
    [SMulCommClass G A B] (h : (maximalIdeal A).map (algebraMap A B) ≠ ⊥) :
    _root_.IsDiscreteValuationRing (FixedPoints.subalgebra A B G) where
  not_a_field' hbot := h <| (Ideal.map_eq_bot_iff_le_ker _).2 fun a ha ↦ by
    have hmem := map_nonunit (algebraMap A (FixedPoints.subalgebra A B G)) a ha
    rw [hbot, Ideal.mem_bot] at hmem
    rw [RingHom.mem_ker, IsScalarTower.algebraMap_apply A (FixedPoints.subalgebra A B G) B, hmem,
      map_zero]

/-- When a discrete valuation ring `B` lies locally and faithfully over a discrete valuation ring
`A`, `FixedPoints.subalgebra A B G` is a discrete valuation ring for any monoid `G`. -/
theorem isDiscreteValuationRing_fixedPoints_subalgebra_of_isLocalHom {A B G : Type*} [CommRing A]
    [IsDomain A] [_root_.IsDiscreteValuationRing A] [CommRing B] [IsDomain B]
    [_root_.IsDiscreteValuationRing B] [Algebra A B] [IsLocalHom (algebraMap A B)]
    [FaithfulSMul A B] [Monoid G] [MulSemiringAction G B] [SMulCommClass G A B] :
    _root_.IsDiscreteValuationRing (FixedPoints.subalgebra A B G) :=
  isDiscreteValuationRing_fixedPoints_subalgebra_of_map_maximalIdeal_ne_bot fun h ↦ by
    obtain ⟨ϖ, hϖ⟩ := _root_.IsDiscreteValuationRing.exists_irreducible A
    have hmem : algebraMap A B ϖ ∈ (maximalIdeal A).map (algebraMap A B) :=
      Ideal.mem_map_of_mem _ ((mem_maximalIdeal _).2 (mem_nonunits_iff.2 hϖ.not_isUnit))
    rw [h, Ideal.mem_bot] at hmem
    exact hϖ.ne_zero (FaithfulSMul.algebraMap_injective A B (hmem.trans (map_zero _).symm))

end IsDiscreteValuationRing

section FixedFieldIntegralClosure

open IntermediateField

/-- In a tower of fields `K / E / L` over `A`, if `integralClosure A L` is a local ring, then
`integralClosure A E` is also a local ring. -/
theorem isLocalRing_integralClosure_of_tower (A K E L : Type*) [CommRing A] [Field K] [Field E]
    [Field L] [Algebra A K] [Algebra K E] [Algebra E L] [Algebra K L] [Algebra A E] [Algebra A L]
    [IsScalarTower A K E] [IsScalarTower A K L] [IsScalarTower K E L]
    [IsLocalRing (integralClosure A L)] : IsLocalRing (integralClosure A E) := by
  have : IsScalarTower A E L := .of_algebraMap_eq fun r ↦ by
    rw [IsScalarTower.algebraMap_apply A K L, IsScalarTower.algebraMap_apply K E L,
      ← IsScalarTower.algebraMap_apply A K E]
  let f := (IsScalarTower.toAlgHom A E L).mapIntegralClosure
  have hf_int : f.toRingHom.IsIntegral :=
    RingHom.IsIntegral.tower_top (algebraMap A (integralClosure A E)) f.toRingHom
      (f.comp_algebraMap.symm ▸ algebraMap_isIntegral_iff.mpr inferInstance)
  have : IsLocalHom f.toRingHom := hf_int.isLocalHom fun _ _ h ↦
    Subtype.ext ((algebraMap E L).injective (congrArg Subtype.val h))
  exact f.toRingHom.domain_isLocalRing

/-- If `integralClosure A L` is a local ring, then `integralClosure A (fixedField H)` is also a
local ring for every subgroup `H ≤ Gal(L/K)`. -/
instance instIsLocalRingIntegralClosureFixedField {A K L : Type*} [CommRing A] [Field K] [Field L]
    [Algebra A K] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [IsLocalRing (integralClosure A L)] {H : Subgroup (L ≃ₐ[K] L)} :
    IsLocalRing (integralClosure A (fixedField H)) :=
  (fixedPointsSubalgebraIntegralClosureEquiv A H).toRingEquiv.isLocalRing

/-- If `integralClosure A L` is a discrete valuation ring and `H ≤ Gal(L/K)` is a finite subgroup,
then `integralClosure A (fixedField H)` is also a discrete valuation ring. -/
instance instIsDiscreteValuationRingIntegralClosureFixedField {A K L : Type*} [CommRing A]
    [Field K] [Field L] [Algebra A K] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [_root_.IsDiscreteValuationRing (integralClosure A L)] {H : Subgroup (L ≃ₐ[K] L)} [Finite H] :
    _root_.IsDiscreteValuationRing (integralClosure A (fixedField H)) :=
  _root_.IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
    (fixedPointsSubalgebraIntegralClosureEquiv A H)

end FixedFieldIntegralClosure

end TauCeti
