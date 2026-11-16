/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DiscreteValuationRing.FixedPoints
public import TauCeti.RingTheory.LocalRing.RamificationGroup
public import TauCeti.RingTheory.RamificationInertia.DiscreteValuationRing
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Flat.TorsionFree
import TauCeti.NumberTheory.RamificationInertia.SeparableDegree
import TauCeti.RingTheory.DiscreteValuationRing.Monogenic
import TauCeti.RingTheory.IsGaloisGroup.Dedekind
import TauCeti.RingTheory.KrullDimension.Basic
import TauCeti.RingTheory.KrullDimension.Integral
import TauCeti.RingTheory.LocalRing.ResidueField.Instances
import TauCeti.RingTheory.Valuation.AddValuation

/-!
# Inertia cardinality and Serre's lower-index quotient formula on discrete valuation rings

For a faithful finite Galois action `G` on a DVR `B` with invariant DVR `A` and separable residue
extension, `#G_0 = e(B / A)` (`natCard_ramificationGroup_zero`). More generally, when a finite
group `G` acts faithfully on a DVR `B` over a local ring `A` with separable residue extension (e.g.
perfect `ResidueField A` and `B` integral over `A`), `#G_0 = e(B / B^G)`
(`natCard_ramificationGroup_zero_fixedPoints`), and Serre's quotient formula
`e(B / B^H) · i_{G ⧸ H}(g H) = ∑ᶠ h : H, i_G(g h)` holds for finite `G` and normal `H ≤ G`
(`ramificationIdx_mul_lowerIndex_quotient_mk'_eq_finsum`), feeding
`TauCeti.RingTheory.DiscreteValuationRing.Herbrand`. Adapts
`TauCeti/NumberTheory/LocalField/LowerIndex.lean` and
`TauCeti/NumberTheory/LocalField/Herbrand/Quotient.lean`.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §1, Proposition 3 and §3, Lemma 4.
-/

public section
noncomputable section

open IsLocalRing

namespace TauCeti.IsLocalRing

/-- For a faithful finite Galois action `G` on a DVR `B` with invariant DVR `A` and separable
residue extension, `#G_0 = e(B / A)`. -/
theorem natCard_ramificationGroup_zero {A B G : Type*} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B]
    [IsLocalHom (algebraMap A B)] [Group G] [Finite G] [MulSemiringAction G B]
    [IsGaloisGroup G A B] [Algebra.IsSeparable (ResidueField A) (ResidueField B)] :
    Nat.card (ramificationGroup G B 0) = (maximalIdeal B).ramificationIdx A := by
  have _ : Algebra.IsIntegral A B := Algebra.IsInvariant.isIntegral A B G
  have _ : FiniteRingKrullDim A := FiniteRingKrullDim.of_ringKrullDim_eq_natCast (n := 1)
    (by simpa using IsDiscreteValuationRing.ringKrullDim_eq_one A)
  have _ : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).2 <|
    (algebraMap A B).injective_of_isIntegral_of_ringKrullDim_le
      (Algebra.isIntegral_def.1 inferInstance)
      (by simp [IsDiscreteValuationRing.ringKrullDim_eq_one])
  have _ : Module.Finite A B := TauCeti.IsGaloisGroup.moduleFinite G A B
  have _ := (isSeparable_residueField_iff (A := A) (B := B)).mp ‹_›
  rw [ramificationGroup_zero_eq_inertia,
    ← Ideal.ramificationIdxIn_eq_ramificationIdx (maximalIdeal A) (maximalIdeal B) G]
  exact Ideal.card_inertia_eq_ramificationIdxIn_of_isSeparable (G := G)
    (maximalIdeal A) (maximalIdeal B)

/-- For a finite group `G` acting faithfully on a DVR `B` over a local ring `A` with separable
residue extension, `#G_0 = e(B / B^G)`. -/
theorem natCard_ramificationGroup_zero_fixedPoints (A B G : Type*) [CommRing A] [IsLocalRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B]
    [IsLocalHom (algebraMap A B)] [Group G] [Finite G] [MulSemiringAction G B]
    [SMulCommClass G A B] [FaithfulSMul G B]
    [Algebra.IsSeparable (ResidueField A) (ResidueField B)] :
    Nat.card (ramificationGroup G B 0) =
      (maximalIdeal B).ramificationIdx (FixedPoints.subalgebra A B G) := by
  let _ : IsGaloisGroup G (FixedPoints.subalgebra A B G) B :=
    ⟨inferInstance, inferInstance, inferInstance⟩
  have _ : Algebra.IsSeparable (ResidueField (FixedPoints.subalgebra A B G)) (ResidueField B) :=
    Algebra.isSeparable_tower_top_of_isSeparable (ResidueField A) _ (ResidueField B)
  exact natCard_ramificationGroup_zero

section

variable (A B G : Type*) [CommRing A] [IsLocalRing A] [CommRing B] [IsDomain B]
  [IsDiscreteValuationRing B] [Algebra A B] [IsLocalHom (algebraMap A B)] [Group G] [Finite G]
  [MulSemiringAction G B] [SMulCommClass G A B] [FaithfulSMul G B]
  [Algebra.IsSeparable (ResidueField A) (ResidueField B)]

/-- **Serre's quotient formula for the lower index**: for normal `H ≤ G`,
`e(B / B^H) · i_{G ⧸ H}(g H) = ∑ᶠ h : H, i_G(g h)`. -/
theorem ramificationIdx_mul_lowerIndex_quotient_mk'_eq_finsum (H : Subgroup G) [H.Normal] (g : G) :
    ((maximalIdeal B).ramificationIdx (FixedPoints.subalgebra A B H) : ℕ∞) *
        lowerIndex (FixedPoints.subalgebra A B H) (QuotientGroup.mk' H g) =
      ∑ᶠ h : H, lowerIndex B (g * h) := by
  let _ := Fintype.ofFinite H
  set R₀ := FixedPoints.subalgebra A B G; set C := FixedPoints.subalgebra A B H
  have hle : R₀ ≤ C := fun _ hx h ↦ hx h.1
  let _ : Algebra R₀ C := (Subalgebra.inclusion hle).toRingHom.toAlgebra
  have _ : IsScalarTower R₀ C B :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by simp [RingHom.algebraMap_toAlgebra]
  have _ : IsLocalHom (algebraMap R₀ C) := by
    have hloc : IsLocalHom (algebraMap R₀ B) := inferInstance
    rw [IsScalarTower.algebraMap_eq R₀ C B] at hloc; exact isLocalHom_of_comp _ (algebraMap C B)
  have _ : FaithfulSMul R₀ C :=
    (faithfulSMul_iff_algebraMap_injective R₀ C).2 (Subalgebra.inclusion_injective hle)
  let _ : IsGaloisGroup G R₀ B := ⟨‹_›, inferInstance, inferInstance⟩
  have _ : Module.Finite R₀ B := TauCeti.IsGaloisGroup.moduleFinite G R₀ B
  have _ : Module.Finite R₀ C :=
    Module.Finite.of_injective (IsScalarTower.toAlgHom R₀ C B).toLinearMap Subtype.val_injective
  have _ : Algebra.IsSeparable (ResidueField R₀) (ResidueField B) :=
    Algebra.isSeparable_tower_top_of_isSeparable (ResidueField A) (ResidueField R₀) (ResidueField B)
  have _ : Algebra.IsSeparable (ResidueField R₀) (ResidueField C) :=
    Algebra.isSeparable_tower_bot_of_isSeparable (ResidueField R₀) (ResidueField C) (ResidueField B)
  obtain ⟨x, hx⟩ := TauCeti.IsDiscreteValuationRing.exists_adjoin_eq_top (R := R₀) (S := B)
  obtain ⟨y, hy⟩ := TauCeti.IsDiscreteValuationRing.exists_adjoin_eq_top (R := R₀) (S := C)
  have key : IsDiscreteValuationRing.addVal B (g • (y : B) - (y : B)) =
      IsDiscreteValuationRing.addVal B ((g • MulSemiringAction.charpoly H x).eval x) :=
    (IsDiscreteValuationRing.addVal_eq_iff_associated _ _).2 <| associated_of_dvd_dvd
      (TauCeti.MulSemiringAction.smul_sub_dvd_eval_smul_charpoly H hy g x)
      (dvd_sub_comm.1 (TauCeti.MulSemiringAction.eval_smul_charpoly_dvd_sub_smul H hx y.2 g))
  rw [finsum_eq_sum_of_fintype, lowerIndex_eq_addVal_of_adjoin_singleton_eq_top hy, ← nsmul_eq_mul,
    ← TauCeti.IsDiscreteValuationRing.addVal_algebraMap (S := C) (T := B)]
  simp [C, key, TauCeti.MulSemiringAction.eval_smul_charpoly,
    lowerIndex_eq_addVal_of_adjoin_singleton_eq_top hx, mul_smul, Subgroup.smul_def,
    AddValuation.map_sub_swap]
/-- If `g` maximizes `lowerIndex` in `g H` with `i_G(g) = j`, then
`e(B / B^H) · i_{G ⧸ H}(g H) = ∑ k ∈ range j, #H_k`. -/
theorem ramificationIdx_mul_lowerIndex_quotient_mk'_eq_sum_card (H : Subgroup G) [H.Normal]
    (g : G) {j : ℕ} (hj : lowerIndex B g = j)
    (hg : ∀ h : H, lowerIndex B (g * h) ≤ lowerIndex B g) :
    ((maximalIdeal B).ramificationIdx (FixedPoints.subalgebra A B H) : ℕ∞) *
        lowerIndex (FixedPoints.subalgebra A B H) (QuotientGroup.mk' H g) =
      ∑ k ∈ Finset.range j, (Nat.card (ramificationGroup H B k) : ℕ∞) := by
  let _ := Fintype.ofFinite H
  rw [ramificationIdx_mul_lowerIndex_quotient_mk'_eq_finsum A B G H g, finsum_eq_sum_of_fintype]
  simp_rw [lowerIndex_mul_of_forall_le g hg, hj]
  exact sum_min_lowerIndex_natCast (G := H) (S := B) j
end

/-- For a faithful action of `G` on a DVR `B` over `A` and a finite normal subgroup `H ≤ G`,
`i_{G ⧸ H}(g H) = ⊤` if and only if `g ∈ H`. -/
theorem lowerIndex_quotient_mk'_eq_top_iff (A B G : Type*) [CommRing A] [CommRing B] [IsDomain B]
    [IsDiscreteValuationRing B] [Algebra A B] [Group G] [MulSemiringAction G B]
    [SMulCommClass G A B] [FaithfulSMul G B] (H : Subgroup G) [H.Normal] [Finite H] (g : G) :
    lowerIndex (FixedPoints.subalgebra A B H) (QuotientGroup.mk' H g) = ⊤ ↔ g ∈ H := by
  rw [lowerIndex_eq_top_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
/-- If `g` maximizes `lowerIndex` in `g H` and `lowerIndex B g ≠ ⊤`, then
`lowerIndex B^H (QuotientGroup.mk' H g) ≠ ⊤`. -/
theorem lowerIndex_quotient_mk'_ne_top (A B G : Type*) [CommRing A] [CommRing B] [IsDomain B]
    [IsDiscreteValuationRing B] [Algebra A B] [Group G] [MulSemiringAction G B]
    [SMulCommClass G A B] [FaithfulSMul G B] (H : Subgroup G) [H.Normal] [Finite H] (g : G)
    (hj : lowerIndex B g ≠ ⊤) (hg : ∀ h : H, lowerIndex B (g * h) ≤ lowerIndex B g) :
    lowerIndex (FixedPoints.subalgebra A B H) (QuotientGroup.mk' H g) ≠ ⊤ := by
  rw [ne_eq, lowerIndex_quotient_mk'_eq_top_iff]
  exact fun hgH ↦ hj <| top_le_iff.1 <| by simpa using hg ⟨g⁻¹, H.inv_mem hgH⟩

end TauCeti.IsLocalRing
