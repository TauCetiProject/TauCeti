/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import TauCeti.RingTheory.DiscreteValuationRing.Invariant
public import TauCeti.RingTheory.Invariant.Basic
public import TauCeti.RingTheory.IsGaloisGroup.IntegralClosure
public import TauCeti.RingTheory.LocalRing.FixedPoints

/-!
# Fixed-point subrings and subalgebras of discrete valuation rings

For any monoid action on a DVR `B`, minimal additive valuation makes `FixedPoints.subring B G` and
`FixedPoints.subalgebra A B G` PIDs. Under integrality (e.g. finite `G`) or over a local ring `A`
with `(maximalIdeal A).map (algebraMap A B) ≠ ⊥`, they are DVRs, transferring
`IsDiscreteValuationRing` to `integralClosure A (IntermediateField.fixedField H)`.
-/

public section
open IntermediateField IsLocalRing _root_.IsDiscreteValuationRing
namespace TauCeti
section
variable {B G : Type*} [CommRing B] [IsDomain B] [_root_.IsDiscreteValuationRing B]

section Monoid
variable [Monoid G] [MulSemiringAction G B]
/-- The fixed-point subring of a DVR under any monoid action is a principal ideal ring. -/
instance instIsPrincipalIdealRingFixedPointsSubring :
    IsPrincipalIdealRing (FixedPoints.subring B G) where
  principal I := by
    by_cases hI : I = ⊥; · exact ⟨0, by simp [hI]⟩
    obtain ⟨x₀, hx₀I, hx₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
    let f (z : {x : FixedPoints.subring B G // x ∈ I ∧ x ≠ 0}) := (addVal B (z.val : B)).toNat
    obtain ⟨⟨a, haI, ha0⟩, -, hmin⟩ :=
      (InvImage.wf f Nat.lt_wfRel.wf).has_min Set.univ ⟨⟨x₀, hx₀I, hx₀0⟩, trivial⟩
    refine ⟨a, le_antisymm (fun y hyI ↦ ?_) (Ideal.span_le.2 (Set.singleton_subset_iff.2 haI))⟩
    by_cases hy0 : y = 0; · simp [hy0]
    refine Ideal.mem_span_singleton.2 <| coe_dvd_coe_fixedPoints_subring_iff.1 <|
      addVal_le_iff_dvd.1 ?_
    rw [← ENat.natCast_toNat (addVal_eq_top_iff.not.2 (Subtype.coe_ne_coe.2 ha0)),
      ← ENat.natCast_toNat (addVal_eq_top_iff.not.2 (Subtype.coe_ne_coe.2 hy0))]
    exact_mod_cast not_lt.1 (hmin ⟨y, hyI, hy0⟩ trivial)
/-- The fixed-point subalgebra of a DVR under any monoid action is a principal ideal ring. -/
instance instIsPrincipalIdealRingFixedPointsSubalgebra {A : Type*} [CommSemiring A] [Algebra A B]
    [SMulCommClass G A B] : IsPrincipalIdealRing (FixedPoints.subalgebra A B G) :=
  IsPrincipalIdealRing.of_surjective (fixedPointsSubringEquivSubalgebra A B G).toRingHom
    (fixedPointsSubringEquivSubalgebra A B G).surjective
section FixedPointsDVR
variable {A : Type*} [CommRing A] [Algebra A B] [SMulCommClass G A B]
/-- If a DVR `B` is integral over `FixedPoints.subalgebra A B G` for a monoid `G`, then
`FixedPoints.subalgebra A B G` is a DVR. -/
theorem isDiscreteValuationRing_fixedPoints_subalgebra_of_isIntegral
    [Algebra.IsIntegral (FixedPoints.subalgebra A B G) B] :
    _root_.IsDiscreteValuationRing (FixedPoints.subalgebra A B G) where
  not_a_field' hbot := not_isField B <|
    (Algebra.IsIntegral.isField_iff_isField (R := FixedPoints.subalgebra A B G) (S := B)
      (FaithfulSMul.algebraMap_injective _ B)).mp (isField_iff_maximalIdeal_eq.2 hbot)
/-- When a DVR `B` lies locally over a local ring `A` whose maximal ideal has nonzero image in `B`,
`FixedPoints.subalgebra A B G` is a DVR for any monoid `G`. -/
theorem isDiscreteValuationRing_fixedPoints_subalgebra_of_map_maximalIdeal_ne_bot [IsLocalRing A]
    [IsLocalHom (algebraMap A B)] (h : (maximalIdeal A).map (algebraMap A B) ≠ ⊥) :
    _root_.IsDiscreteValuationRing (FixedPoints.subalgebra A B G) where
  not_a_field' hbot := h <| (Ideal.map_eq_bot_iff_le_ker _).2 fun a ha ↦ by
    have hmem := map_nonunit (algebraMap A (FixedPoints.subalgebra A B G)) a ha
    rw [hbot, Ideal.mem_bot] at hmem
    simp [IsScalarTower.algebraMap_apply A (FixedPoints.subalgebra A B G) B, hmem]
/-- When a DVR `B` lies locally and faithfully over a DVR `A`, `FixedPoints.subalgebra A B G` is a
DVR for any monoid `G`. -/
theorem isDiscreteValuationRing_fixedPoints_subalgebra_of_isDiscreteValuationRing [IsDomain A]
    [_root_.IsDiscreteValuationRing A] [IsLocalHom (algebraMap A B)] [FaithfulSMul A B] :
    _root_.IsDiscreteValuationRing (FixedPoints.subalgebra A B G) :=
  isDiscreteValuationRing_fixedPoints_subalgebra_of_map_maximalIdeal_ne_bot
    (Ideal.map_ne_bot_of_ne_bot (not_a_field A))
end FixedPointsDVR
end Monoid

section FiniteGroup
variable [Group G] [Finite G] [MulSemiringAction G B]
/-- The fixed-point subring of a DVR under a finite group action is a DVR. -/
instance instIsDiscreteValuationRingFixedPointsSubring :
    _root_.IsDiscreteValuationRing (FixedPoints.subring B G) :=
  RingEquivClass.isDiscreteValuationRing (fixedPointsSubringEquivSubalgebra ℤ B G).symm
end FiniteGroup
end

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
  RingEquivClass.isDiscreteValuationRing (fixedPointsSubalgebraIntegralClosureEquiv A H)

end TauCeti
