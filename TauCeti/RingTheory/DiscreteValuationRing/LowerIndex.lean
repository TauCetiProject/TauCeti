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
import TauCeti.RingTheory.IsGaloisGroup.Dedekind
import TauCeti.RingTheory.Valuation.AddValuation

/-!
# Inertia cardinality and Serre's lower-index quotient formula on discrete valuation rings

Let a finite group `G` act faithfully on a discrete valuation ring `B` over a local ring `A` with
separable residue extension `ResidueField B / ResidueField A` (which holds whenever `ResidueField A`
is perfect and `ResidueField B / ResidueField A` is algebraic, e.g. when `B` is integral over `A`).
We prove `#G_0 = e(B / A)` (`natCard_ramificationGroup_zero`), `#H_0 = e(B / B^H)`
(`natCard_ramificationGroup_zero_fixedPoints`), and Serre's quotient formula
`e(B / B^H) · i_{G ⧸ H}(g H) = ∑ᶠ h : H, i_G(g h)` for a normal subgroup `H ≤ G`
(`ramificationIdx_mul_lowerIndex_quotient_mk'_eq_finsum`).
-/

public section
noncomputable section

open IsLocalRing Polynomial

namespace TauCeti.IsLocalRing

/-- For a faithful finite Galois group action `G` on a discrete valuation ring `B` with invariant
ring a discrete valuation ring `A` and separable residue extension, `#G_0 = e(B / A)`. -/
theorem natCard_ramificationGroup_zero {A B G : Type*} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B]
    [IsLocalHom (algebraMap A B)] [Group G] [Finite G] [MulSemiringAction G B]
    [IsGaloisGroup G A B] [Algebra.IsSeparable (ResidueField A) (ResidueField B)] :
    Nat.card (ramificationGroup G B 0) = (maximalIdeal B).ramificationIdx A := by
  have _ : Algebra.IsIntegral A B := Algebra.IsInvariant.isIntegral A B G
  have _ : FaithfulSMul A B := by
    refine (faithfulSMul_iff_algebraMap_injective A B).2 ((RingHom.injective_iff_ker_eq_bot _).2 ?_)
    by_contra hne
    have _ := RingHom.ker_isPrime (algebraMap A B)
    have hmax : ((⊥ : Ideal B).under A).IsMaximal := by
      rw [Ideal.under_def, ← RingHom.ker_eq_comap_bot]
      exact Ideal.isMaximal_of_isPrime_of_ne_bot _ hne
    exact IsDiscreteValuationRing.not_a_field B
      (eq_maximalIdeal (Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := A) ⊥ hmax)).symm
  have _ : Module.Finite A B := IsGaloisGroup.moduleFinite G A B
  have _ : Algebra.IsSeparable (A ⧸ maximalIdeal A) (B ⧸ maximalIdeal B) :=
    inferInstanceAs (Algebra.IsSeparable (ResidueField A) (ResidueField B))
  rw [ramificationGroup_zero_eq_inertia,
    ← Ideal.ramificationIdxIn_eq_ramificationIdx (maximalIdeal A) (maximalIdeal B) G]
  exact Ideal.card_inertia_eq_ramificationIdxIn_of_isSeparable (G := G)
    (maximalIdeal A) (maximalIdeal B)

/-- For a finite subgroup `H ≤ G` acting faithfully on a discrete valuation ring `B` over a local
ring `A` with separable residue extension, `#H_0 = e(B / B^H)`. -/
theorem natCard_ramificationGroup_zero_fixedPoints (A B G : Type*) [CommRing A] [IsLocalRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B]
    [IsLocalHom (algebraMap A B)] [Group G] [MulSemiringAction G B] [SMulCommClass G A B]
    [FaithfulSMul G B] [Algebra.IsSeparable (ResidueField A) (ResidueField B)]
    (H : Subgroup G) [Finite H] :
    Nat.card (ramificationGroup H B 0) =
      (maximalIdeal B).ramificationIdx (FixedPoints.subalgebra A B H) := by
  let _ : IsGaloisGroup H (FixedPoints.subalgebra A B H) B :=
    ⟨inferInstance, inferInstance, inferInstance⟩
  have _ : Algebra.IsSeparable (ResidueField (FixedPoints.subalgebra A B H)) (ResidueField B) :=
    Algebra.isSeparable_tower_top_of_isSeparable (ResidueField A) _ (ResidueField B)
  exact natCard_ramificationGroup_zero

section Quotient

variable (A B G : Type*) [CommRing A] [IsLocalRing A] [CommRing B] [IsDomain B]
  [IsDiscreteValuationRing B] [Algebra A B] [IsLocalHom (algebraMap A B)] [Group G] [Finite G]
  [MulSemiringAction G B] [SMulCommClass G A B] [FaithfulSMul G B]
  [Algebra.IsSeparable (ResidueField A) (ResidueField B)]

omit [IsLocalRing A] [IsDiscreteValuationRing B] [IsLocalHom (algebraMap A B)] [Finite G]
  [FaithfulSMul G B] [Algebra.IsSeparable (ResidueField A) (ResidueField B)] in
private theorem smul_sub_dvd_eval_smul_charpoly {A B G R₀ : Type*} [CommRing A] [CommRing B]
    [IsDomain B] [Algebra A B] [Group G] [MulSemiringAction G B] [SMulCommClass G A B]
    [CommRing R₀] (H : Subgroup G) [H.Normal] [Fintype H]
    [Algebra R₀ (FixedPoints.subalgebra A B H)]
    [SMulCommClass (G ⧸ H) R₀ (FixedPoints.subalgebra A B H)]
    {y : FixedPoints.subalgebra A B H} (hy : Algebra.adjoin R₀ {y} = ⊤) (g : G) (x : B) :
    g • (y : B) - (y : B) ∣ (g • MulSemiringAction.charpoly H x).eval x := by
  set P := MulSemiringAction.charpoly H x
  rw [← sub_zero ((g • P).eval x), ← MulSemiringAction.eval_charpoly H x, ← eval_sub,
    eval_eq_sum_range]
  refine Finset.dvd_sum fun n _ ↦ Dvd.dvd.mul_right ?_ _
  have hdvd := TauCeti.smul_sub_dvd_smul_sub_of_adjoin_singleton_eq_top hy (QuotientGroup.mk' H g)
    ⟨P.coeff n, MulSemiringAction.smul_coeff_charpoly x n⟩
  rw [← TauCeti.dvd_coe_fixedPoints_subalgebra_iff] at hdvd
  simpa only [AddSubgroupClass.coe_sub, QuotientGroup.mk'_apply,
    TauCeti.coe_quotient_smul_fixedPoints_subalgebra, coeff_sub,
    AddMonoidAlgebra.coeff_smul_apply] using hdvd

omit [IsLocalRing A] [IsDiscreteValuationRing B] [IsLocalHom (algebraMap A B)] [Finite G]
  [Algebra.IsSeparable (ResidueField A) (ResidueField B)] in
private theorem eval_smul_charpoly_dvd_sub_smul {A B G R₀ : Type*} [CommRing A] [CommRing B]
    [IsDomain B] [Algebra A B] [Group G] [MulSemiringAction G B] [SMulCommClass G A B]
    [FaithfulSMul G B] [CommRing R₀] [Algebra R₀ B] [SMulCommClass G R₀ B]
    (H : Subgroup G) [Fintype H] {x : B} (hx : Algebra.adjoin R₀ {x} = ⊤)
    (y : FixedPoints.subalgebra A B H) (g : G) :
    (g • MulSemiringAction.charpoly H x).eval x ∣ (y : B) - g • (y : B) := by
  obtain ⟨q, hq⟩ : ∃ q : R₀[X], aeval x q = (y : B) := by
    rw [← AlgHom.mem_range, ← Algebra.adjoin_singleton_eq_range_aeval, hx]; exact Algebra.mem_top
  set Q : B[X] := q.map (algebraMap R₀ B) - C (y : B)
  have hQ : ∀ h : H, Q.eval ((h : G) • x) = 0 := fun h ↦ by
    rw [eval_sub, eval_C, eval_map_algebraMap, Polynomial.aeval_smul, hq, ← Subgroup.smul_def,
      y.2 h, sub_self]
  have hinj : Function.Injective (fun h : H ↦ h • x) :=
    (TauCeti.smul_left_injective_of_adjoin_singleton_eq_top (G := G) hx).comp H.subtype_injective
  obtain ⟨r, hr⟩ := TauCeti.MulSemiringAction.charpoly_dvd hinj hQ
  have hgQ : g • Q = q.map (algebraMap R₀ B) - C (g • (y : B)) := by
    have hmap : (MulSemiringAction.toRingHom G B g).comp (algebraMap R₀ B) = algebraMap R₀ B :=
      RingHom.ext fun r₀ ↦ smul_algebraMap g r₀
    rw [smul_sub, smul_C, smul_eq_map, Polynomial.map_map, hmap]
  exact ⟨(g • r).eval x, by
    rw [← eval_mul, ← smul_mul', ← hr, hgQ, eval_sub, eval_C, eval_map_algebraMap, hq]⟩

/-- **Serre's quotient formula for the lower index** on discrete valuation rings: for a normal
subgroup `H ≤ G`, `e(B / B^H) · i_{G ⧸ H}(g H) = ∑ᶠ h : H, i_G(g h)`. -/
theorem ramificationIdx_mul_lowerIndex_quotient_mk'_eq_finsum (H : Subgroup G) [H.Normal] (g : G) :
    ((maximalIdeal B).ramificationIdx (FixedPoints.subalgebra A B H) : ℕ∞) *
        lowerIndex (FixedPoints.subalgebra A B H) (QuotientGroup.mk' H g) =
      ∑ᶠ h : H, lowerIndex B (g * h) := by
  let _ := Fintype.ofFinite H
  set R₀ := FixedPoints.subalgebra A B G
  set C := FixedPoints.subalgebra A B H
  have hle : R₀ ≤ C := fun _ hx h ↦ hx h.1
  let _ : Algebra R₀ C := (Subalgebra.inclusion hle).toRingHom.toAlgebra
  have _ : IsScalarTower R₀ C B := IsScalarTower.of_algebraMap_eq' rfl
  have _ : IsLocalHom (algebraMap R₀ C) := by
    have hloc : IsLocalHom (algebraMap R₀ B) := inferInstance
    rw [IsScalarTower.algebraMap_eq R₀ C B] at hloc
    exact isLocalHom_of_comp _ (algebraMap C B)
  have _ : FaithfulSMul R₀ C :=
    (faithfulSMul_iff_algebraMap_injective R₀ C).2 (Subalgebra.inclusion_injective hle)
  have _ : SMulCommClass (G ⧸ H) R₀ C :=
    TauCeti.smulCommClass_quotient_fixedPoints_subalgebra A B G H
  let _ : IsGaloisGroup G R₀ B := ⟨inferInstance, inferInstance, inferInstance⟩
  have _ : Module.Finite R₀ B := IsGaloisGroup.moduleFinite G R₀ B
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
      (smul_sub_dvd_eval_smul_charpoly H hy g x)
      (dvd_sub_comm.1 (eval_smul_charpoly_dvd_sub_smul H hx y g))
  rw [finsum_eq_sum_of_fintype, lowerIndex_eq_addVal_of_adjoin_singleton_eq_top hy, ← nsmul_eq_mul,
    ← TauCeti.IsDiscreteValuationRing.addVal_algebraMap (S := C) (T := B), map_sub,
    Subalgebra.algebraMap_apply, Subalgebra.algebraMap_apply, QuotientGroup.mk'_apply,
    TauCeti.coe_quotient_smul_fixedPoints_subalgebra, key,
    TauCeti.MulSemiringAction.eval_smul_charpoly, AddValuation.map_prod]
  refine Finset.sum_congr rfl fun h _ ↦ ?_
  rw [lowerIndex_eq_addVal_of_adjoin_singleton_eq_top hx, mul_smul, Subgroup.smul_def,
    AddValuation.map_sub_swap]

/-- If `g` has maximal lower index `j` in its coset `g H`, then
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

/-- If `g` has finite maximal lower index in `g H`, then `i_{G ⧸ H}(g H) ≠ ⊤`. -/
theorem lowerIndex_quotient_mk'_ne_top (H : Subgroup G) [H.Normal] (g : G)
    (hj : lowerIndex B g ≠ ⊤) (hg : ∀ h : H, lowerIndex B (g * h) ≤ lowerIndex B g) :
    lowerIndex (FixedPoints.subalgebra A B H) (QuotientGroup.mk' H g) ≠ ⊤ := by
  obtain ⟨j, hj⟩ := ENat.ne_top_iff_exists.1 hj
  intro htop
  have hsum := ramificationIdx_mul_lowerIndex_quotient_mk'_eq_sum_card A B G H g hj.symm hg
  have he : ((maximalIdeal B).ramificationIdx (FixedPoints.subalgebra A B H) : ℕ∞) ≠ 0 := by
    rw [← natCard_ramificationGroup_zero_fixedPoints A B G H]
    exact Nat.cast_ne_zero.2 Nat.card_pos.ne'
  rw [htop, ENat.mul_top he, ← Nat.cast_sum] at hsum
  exact ENat.natCast_ne_top _ hsum.symm

end Quotient

end TauCeti.IsLocalRing
