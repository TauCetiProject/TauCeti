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

When a monoid `G` acts by ring endomorphisms on a DVR `B`, choosing a nonzero element of minimal
additive valuation in any nonzero ideal shows `FixedPoints.subring B G` and
`FixedPoints.subalgebra A B G` are PIDs. When `B` is integral over `FixedPoints.subalgebra A B G`
(in particular when `G` is a finite group), or when `G` acts by `A`-algebra endomorphisms
(`SMulCommClass G A B`) over a local ring `A` with `IsLocalHom (algebraMap A B)` and
`(maximalIdeal A).map (algebraMap A B) ≠ ⊥` (e.g. faithfully over a DVR `A`),
`FixedPoints.subalgebra A B G` is not a field and hence is a DVR; this transfers
`IsDiscreteValuationRing` to `FixedPoints.subring B G` (for finite `G`) and to
`integralClosure A (IntermediateField.fixedField H)` for any subgroup `H ≤ Gal(L/K)`.
-/

public section

open IntermediateField IsLocalRing

namespace TauCeti

/-- The fixed-point subring of a DVR under any monoid action is a principal ideal ring. -/
instance instIsPrincipalIdealRingFixedPointsSubring {B G : Type*} [CommRing B] [IsDomain B]
    [_root_.IsDiscreteValuationRing B] [Monoid G] [MulSemiringAction G B] :
    IsPrincipalIdealRing (FixedPoints.subring B G) where
  principal I := by
    by_cases hI : I = ⊥; · exact ⟨0, by simp [hI]⟩
    obtain ⟨x₀, hx₀I, hx₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
    let f (z : {x : FixedPoints.subring B G // x ∈ I ∧ x ≠ 0}) : ℕ :=
      (_root_.IsDiscreteValuationRing.addVal B (z.1 : B)).toNat
    obtain ⟨⟨a, haI, ha0⟩, -, hmin⟩ :=
      (InvImage.wf f Nat.lt_wfRel.wf).has_min Set.univ ⟨⟨x₀, hx₀I, hx₀0⟩, trivial⟩
    refine ⟨a, le_antisymm (fun y hyI ↦ ?_) (Ideal.span_le.2 (Set.singleton_subset_iff.2 haI))⟩
    by_cases hy0 : y = 0; · simp [hy0]
    have ha_top := _root_.IsDiscreteValuationRing.addVal_eq_top_iff.not.2 (Subtype.coe_ne_coe.2 ha0)
    have hy_top := _root_.IsDiscreteValuationRing.addVal_eq_top_iff.not.2 (Subtype.coe_ne_coe.2 hy0)
    have hle : _root_.IsDiscreteValuationRing.addVal B (a : B) ≤
        _root_.IsDiscreteValuationRing.addVal B (y : B) := by
      rw [← ENat.natCast_toNat ha_top, ← ENat.natCast_toNat hy_top]
      exact_mod_cast not_lt.1 (hmin ⟨y, hyI, hy0⟩ trivial)
    exact Ideal.mem_span_singleton.2 <| coe_dvd_coe_fixedPoints_subring_iff.1
      (_root_.IsDiscreteValuationRing.addVal_le_iff_dvd.1 hle)

/-- The fixed-point subalgebra of a DVR under any monoid action is a principal ideal ring. -/
instance instIsPrincipalIdealRingFixedPointsSubalgebra {A B G : Type*} [CommSemiring A]
    [CommRing B] [IsDomain B] [_root_.IsDiscreteValuationRing B] [Algebra A B] [Monoid G]
    [MulSemiringAction G B] [SMulCommClass G A B] :
    IsPrincipalIdealRing (FixedPoints.subalgebra A B G) :=
  IsPrincipalIdealRing.of_surjective (fixedPointsSubringEquivSubalgebra A B G).toRingHom
    (fixedPointsSubringEquivSubalgebra A B G).surjective

/-- If a DVR `B` is integral over `FixedPoints.subalgebra A B G` for a monoid `G`, then
`FixedPoints.subalgebra A B G` is a DVR. -/
theorem isDiscreteValuationRing_fixedPoints_subalgebra_of_isIntegral {A B G : Type*}
    [CommRing A] [CommRing B] [IsDomain B] [_root_.IsDiscreteValuationRing B] [Algebra A B]
    [Monoid G] [MulSemiringAction G B] [SMulCommClass G A B]
    [Algebra.IsIntegral (FixedPoints.subalgebra A B G) B] :
    _root_.IsDiscreteValuationRing (FixedPoints.subalgebra A B G) where
  not_a_field' hbot := _root_.IsDiscreteValuationRing.not_isField B <|
    (Algebra.IsIntegral.isField_iff_isField (R := FixedPoints.subalgebra A B G) (S := B)
      (FaithfulSMul.algebraMap_injective _ B)).mp (isField_iff_maximalIdeal_eq.2 hbot)
/-- The fixed-point subalgebra of a DVR under a finite group action is a DVR. -/
instance instIsDiscreteValuationRingFixedPointsSubalgebra {A B G : Type*} [CommRing A] [CommRing B]
    [IsDomain B] [_root_.IsDiscreteValuationRing B] [Algebra A B] [Group G] [Finite G]
    [MulSemiringAction G B] [SMulCommClass G A B] :
    _root_.IsDiscreteValuationRing (FixedPoints.subalgebra A B G) :=
  have := Algebra.IsInvariant.isIntegral (FixedPoints.subalgebra A B G) B G
  isDiscreteValuationRing_fixedPoints_subalgebra_of_isIntegral
/-- The fixed-point subring of a DVR under a finite group action is a DVR. -/
instance instIsDiscreteValuationRingFixedPointsSubring {B G : Type*} [CommRing B] [IsDomain B]
    [_root_.IsDiscreteValuationRing B] [Group G] [Finite G] [MulSemiringAction G B] :
    _root_.IsDiscreteValuationRing (FixedPoints.subring B G) :=
  _root_.IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
    (fixedPointsSubringEquivSubalgebra ℤ B G).symm

/-- When a DVR `B` lies locally over a local ring `A` whose maximal ideal has nonzero image in `B`,
`FixedPoints.subalgebra A B G` is a DVR for any monoid `G`. -/
theorem isDiscreteValuationRing_fixedPoints_subalgebra_of_map_maximalIdeal_ne_bot {A B G : Type*}
    [CommRing A] [IsLocalRing A] [CommRing B] [IsDomain B] [_root_.IsDiscreteValuationRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Monoid G] [MulSemiringAction G B]
    [SMulCommClass G A B] (h : (maximalIdeal A).map (algebraMap A B) ≠ ⊥) :
    _root_.IsDiscreteValuationRing (FixedPoints.subalgebra A B G) where
  not_a_field' hbot := h <| (Ideal.map_eq_bot_iff_le_ker _).2 fun a ha ↦ by
    have hmem := map_nonunit (algebraMap A (FixedPoints.subalgebra A B G)) a ha
    rw [hbot, Ideal.mem_bot] at hmem
    simp [IsScalarTower.algebraMap_apply A (FixedPoints.subalgebra A B G) B, hmem]
/-- When a DVR `B` lies locally and faithfully over a DVR `A`, `FixedPoints.subalgebra A B G` is a
DVR for any monoid `G`. -/
theorem isDiscreteValuationRing_fixedPoints_subalgebra_of_isDiscreteValuationRing {A B G : Type*}
    [CommRing A] [IsDomain A] [_root_.IsDiscreteValuationRing A] [CommRing B] [IsDomain B]
    [_root_.IsDiscreteValuationRing B] [Algebra A B] [IsLocalHom (algebraMap A B)]
    [FaithfulSMul A B] [Monoid G] [MulSemiringAction G B] [SMulCommClass G A B] :
    _root_.IsDiscreteValuationRing (FixedPoints.subalgebra A B G) :=
  isDiscreteValuationRing_fixedPoints_subalgebra_of_map_maximalIdeal_ne_bot
    (Ideal.map_ne_bot_of_ne_bot (_root_.IsDiscreteValuationRing.not_a_field A))

/-- If `integralClosure A L` is a DVR and `H ≤ Gal(L/K)`, then
`integralClosure A (fixedField H)` is a DVR. -/
instance instIsDiscreteValuationRingIntegralClosureFixedField {A K L : Type*} [CommRing A]
    [Field K] [Field L] [Algebra A K] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [_root_.IsDiscreteValuationRing (integralClosure A L)] {H : Subgroup (L ≃ₐ[K] L)} :
    _root_.IsDiscreteValuationRing (integralClosure A (fixedField H)) :=
  have : Algebra.IsIntegral (FixedPoints.subalgebra A (integralClosure A L) H)
      (integralClosure A L) := Algebra.IsIntegral.tower_top A
  have := isDiscreteValuationRing_fixedPoints_subalgebra_of_isIntegral
    (A := A) (B := integralClosure A L) (G := H)
  _root_.IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
    (fixedPointsSubalgebraIntegralClosureEquiv A H)

end TauCeti
