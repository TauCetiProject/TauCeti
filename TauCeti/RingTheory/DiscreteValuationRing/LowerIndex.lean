/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DiscreteValuationRing.FixedPoints
public import TauCeti.RingTheory.LocalRing.RamificationGroup
public import TauCeti.RingTheory.RamificationInertia.DiscreteValuationRing
import Mathlib.RingTheory.Flat.TorsionFree
import TauCeti.NumberTheory.RamificationInertia.SeparableDegree
import TauCeti.RingTheory.DiscreteValuationRing.Monogenic
import TauCeti.RingTheory.Invariant.Minpoly
import TauCeti.RingTheory.IsGaloisGroup.Dedekind
import TauCeti.RingTheory.LocalRing.ResidueField.Instances
import TauCeti.RingTheory.Valuation.AddValuation

/-!
# Inertia cardinality and Serre's lower-index quotient formula on discrete valuation rings

For a faithful finite Galois action `G` on a DVR `B` with invariant DVR `A` and separable residue
extension, `#G_0 = e(B / A)` (`natCard_ramificationGroup_zero`). More generally, when `G` acts
faithfully on a DVR `B` over a local ring `A` with separable residue extension (e.g. perfect
`ResidueField A` and `B` integral over `A`), `#H_0 = e(B / B^H)`
(`natCard_ramificationGroup_zero_fixedPoints`) for finite `H ≤ G`, and Serre's quotient formula
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
  have _ : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).2
    ((RingHom.injective_iff_ker_eq_bot _).2 <| Classical.byContradiction fun hne ↦ by
      have _ := RingHom.ker_isPrime (algebraMap A B)
      have hmax : ((⊥ : Ideal B).under A).IsMaximal := by
        rw [Ideal.under_def, ← RingHom.ker_eq_comap_bot]
        exact Ideal.isMaximal_of_isPrime_of_ne_bot _ hne
      exact IsDiscreteValuationRing.not_a_field B
        (eq_maximalIdeal (Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := A) ⊥ hmax)).symm)
  have _ : Module.Finite A B := TauCeti.IsGaloisGroup.moduleFinite G A B
  have _ := (isSeparable_residueField_iff (A := A) (B := B)).mp ‹_›
  rw [ramificationGroup_zero_eq_inertia,
    ← Ideal.ramificationIdxIn_eq_ramificationIdx (maximalIdeal A) (maximalIdeal B) G]
  exact Ideal.card_inertia_eq_ramificationIdxIn_of_isSeparable (G := G)
    (maximalIdeal A) (maximalIdeal B)

/-- For finite `H ≤ G` acting faithfully on a DVR `B` over a local ring `A` with separable residue
extension, `#H_0 = e(B / B^H)`. -/
theorem natCard_ramificationGroup_zero_fixedPoints (A B G : Type*) [CommRing A] [IsLocalRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B]
    [IsLocalHom (algebraMap A B)] [Group G] [MulSemiringAction G B] [SMulCommClass G A B]
    [FaithfulSMul G B] [Algebra.IsSeparable (ResidueField A) (ResidueField B)]
    (H : Subgroup G) [Finite H] : Nat.card (ramificationGroup H B 0) =
      (maximalIdeal B).ramificationIdx (FixedPoints.subalgebra A B H) := by
  let _ : IsGaloisGroup H (FixedPoints.subalgebra A B H) B :=
    ⟨inferInstance, inferInstance, inferInstance⟩
  have _ : Algebra.IsSeparable (ResidueField (FixedPoints.subalgebra A B H)) (ResidueField B) :=
    Algebra.isSeparable_tower_top_of_isSeparable (ResidueField A) _ (ResidueField B)
  exact natCard_ramificationGroup_zero

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
  have _ : IsScalarTower R₀ C B := IsScalarTower.of_algebraMap_eq' rfl
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
  let e : C →ₐ[R₀] FixedPoints.subalgebra R₀ B H :=
    { toFun z := ⟨z.1, z.2⟩, map_one' := rfl, map_mul' _ _ := rfl,
      map_zero' := rfl, map_add' _ _ := rfl, commutes' _ := rfl }
  have hy' : Algebra.adjoin R₀ {e y} = ⊤ := by
    rw [← Set.image_singleton, ← AlgHom.map_adjoin, hy, Algebra.map_top]
    exact e.range_eq_top.2 fun z ↦ ⟨⟨z.1, z.2⟩, rfl⟩
  have key : IsDiscreteValuationRing.addVal B (g • (y : B) - (y : B)) =
      IsDiscreteValuationRing.addVal B ((g • MulSemiringAction.charpoly H x).eval x) :=
    (IsDiscreteValuationRing.addVal_eq_iff_associated _ _).2 <| associated_of_dvd_dvd
      (TauCeti.MulSemiringAction.smul_sub_dvd_eval_smul_charpoly H hy' g x)
      (dvd_sub_comm.1 (TauCeti.MulSemiringAction.eval_smul_charpoly_dvd_sub_smul H hx y.2 g))
  rw [finsum_eq_sum_of_fintype, lowerIndex_eq_addVal_of_adjoin_singleton_eq_top hy, ← nsmul_eq_mul,
    ← TauCeti.IsDiscreteValuationRing.addVal_algebraMap (S := C) (T := B), map_sub,
    Subalgebra.algebraMap_apply, Subalgebra.algebraMap_apply, QuotientGroup.mk'_apply,
    TauCeti.coe_quotient_smul_fixedPoints_subalgebra, key,
    TauCeti.MulSemiringAction.eval_smul_charpoly, AddValuation.map_prod]
  refine Finset.sum_congr rfl fun h _ ↦ ?_
  rw [lowerIndex_eq_addVal_of_adjoin_singleton_eq_top hx, mul_smul, Subgroup.smul_def,
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

/-- If `g` maximizes `lowerIndex` in `g H` and `lowerIndex B g ≠ ⊤`, then
`lowerIndex B^H (QuotientGroup.mk' H g) ≠ ⊤`. -/
theorem lowerIndex_quotient_mk'_ne_top (H : Subgroup G) [H.Normal] (g : G)
    (hj : lowerIndex B g ≠ ⊤) (hg : ∀ h : H, lowerIndex B (g * h) ≤ lowerIndex B g) :
    lowerIndex (FixedPoints.subalgebra A B H) (QuotientGroup.mk' H g) ≠ ⊤ := by
  obtain ⟨j, hj⟩ := ENat.ne_top_iff_exists.1 hj; intro htop
  have hsum := ramificationIdx_mul_lowerIndex_quotient_mk'_eq_sum_card A B G H g hj.symm hg
  have he : ((maximalIdeal B).ramificationIdx (FixedPoints.subalgebra A B H) : ℕ∞) ≠ 0 := by
    rw [← natCard_ramificationGroup_zero_fixedPoints A B G H]
    exact Nat.cast_ne_zero.2 Nat.card_pos.ne'
  rw [htop, ENat.mul_top he, ← Nat.cast_sum] at hsum; exact ENat.natCast_ne_top _ hsum.symm

end TauCeti.IsLocalRing
