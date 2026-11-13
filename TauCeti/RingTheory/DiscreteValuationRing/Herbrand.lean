/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DiscreteValuationRing.FixedPoints
public import TauCeti.RingTheory.IsGaloisGroup.IntegralClosure
public import TauCeti.RingTheory.LocalRing.Herbrand
public import TauCeti.RingTheory.RamificationInertia.DiscreteValuationRing
import Mathlib.RingTheory.Flat.TorsionFree
import TauCeti.NumberTheory.RamificationInertia.SeparableDegree
import TauCeti.RingTheory.DiscreteValuationRing.Monogenic
import TauCeti.RingTheory.Valuation.AddValuation

/-!
# Herbrand's theorem and transitivity of Herbrand functions on discrete valuation rings

Let a finite group `G` act faithfully on a discrete valuation ring `B` over a local ring `A`, and
assume the residue extension `ResidueField B / ResidueField A` is separable (which holds whenever
`ResidueField A` is perfect, in particular finite or algebraically closed). No completeness or
finiteness of the residue field is required.

For a normal subgroup `H ≤ G`, the invariant ring `B^H = FixedPoints.subalgebra A B H` is a
discrete valuation ring (`TauCeti.instIsDiscreteValuationRingFixedPointsSubalgebra`), `G ⧸ H` acts
faithfully on `B^H` (`TauCeti.instFaithfulSMulQuotientFixedPointsSubalgebra`), and both `B` and
`B^H` are monogenic over `B^G = FixedPoints.subalgebra A B G`
(`TauCeti.IsDiscreteValuationRing.exists_adjoin_eq_top`). Evaluating the `H`-orbit polynomial of a
generator of `B` over `B^G` proves Serre's quotient formula for the lower index:

`e(B / B^H) · i_{G ⧸ H}(g H) = ∑_{h ∈ H} i_G(g h)`.

From this we deduce:

* **Herbrand's lemma** (`TauCeti.IsLocalRing.ramificationGroupReal_quotient_herbrandFun`):
  `(G ⧸ H)_{φ_H(u)} = (G_u).map (QuotientGroup.mk' H)` for every `u : ℝ`.
* **Transitivity of the Herbrand functions** (`TauCeti.IsLocalRing.herbrandFun_tower`,
  `TauCeti.IsLocalRing.inverseHerbrandFun_tower`, `TauCeti.IsLocalRing.herbrandOrderIso_tower`,
  `TauCeti.IsLocalRing.psiNat_tower`): `φ_G = φ_{G ⧸ H} ∘ φ_H` and `ψ_G = ψ_H ∘ ψ_{G ⧸ H}`.
* **Herbrand's theorem** (`TauCeti.IsLocalRing.upperRamificationGroup_quotient_eq_map`):
  `(G ⧸ H)^v = (G^v).map (QuotientGroup.mk' H)` for every `v : ℝ`.
* **Upper filtration of a normal subgroup and breaks in a tower**
  (`TauCeti.IsLocalRing.subgroupOf_upperRamificationGroup_eq_inverseHerbrandFun`,
  `TauCeti.IsLocalRing.upperJump_iff_upperJump_quotient_or_upperJump_inverseHerbrandFun`).
* **Field-theoretic Galois fixed-field transport**
  (`TauCeti.IsLocalRing.map_normalAutEquivQuotient_upperRamificationGroup`,
  `TauCeti.IsLocalRing.map_restrictNormalHom_upperRamificationGroup_integralClosure`) via
  `IsGalois.normalAutEquivQuotient H` when `B = integralClosure A L`.

The proofs adapt `TauCeti.NumberTheory.LocalField.LowerIndex` and
`TauCeti.NumberTheory.LocalField.Herbrand.{Quotient,Tower,UpperQuotient}` from nonarchimedean local
fields to discrete valuation rings with separable residue extension.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §1 Proposition 3 and §3 Lemmas 4–5,
  Propositions 14–15.
* J.-P. Serre, *Sur les corps locaux à corps résiduel algébriquement clos*, Bull. Soc. Math.
  France 89 (1961), n° 3.1, pp. 127–128.
-/

public section
noncomputable section

open IsLocalRing Polynomial

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

namespace TauCeti.IsLocalRing

section InertiaCard

private theorem moduleFinite_of_isGaloisGroup
    {A B G : Type*} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsNoetherianRing A]
    [CommRing B] [IsDomain B] [IsIntegrallyClosed B] [Algebra A B] [FaithfulSMul A B]
    [Group G] [Finite G] [MulSemiringAction G B] [IsGaloisGroup G A B] :
    Module.Finite A B := by
  let _ := IsFractionRing.mulSemiringAction G B (FractionRing B)
  have _ := IsGaloisGroup.isGalois G (FractionRing A) (FractionRing B)
  have _ := IsGaloisGroup.finiteDimensional G (FractionRing A) (FractionRing B)
  have _ := Algebra.IsInvariant.isIntegral A B G
  exact IsIntegralClosure.finite A (FractionRing A) (FractionRing B) B

/-- For a faithful finite Galois group action `G` on a discrete valuation ring `B` with invariant
ring a discrete valuation ring `A` and separable residue extension, the order of the zeroth
ramification group `G_0` equals the ramification index of `B` over `A`. -/
theorem natCard_ramificationGroup_zero
    {A B G : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)]
    [Group G] [Finite G] [MulSemiringAction G B] [IsGaloisGroup G A B]
    [Algebra.IsSeparable (ResidueField A) (ResidueField B)] :
    Nat.card (ramificationGroup G B 0) = (maximalIdeal B).ramificationIdx A := by
  have hint : Algebra.IsIntegral A B := Algebra.IsInvariant.isIntegral A B G
  have hfaith : FaithfulSMul A B := by
    refine (faithfulSMul_iff_algebraMap_injective A B).2 ((RingHom.injective_iff_ker_eq_bot _).2 ?_)
    by_contra hne
    have _ := RingHom.ker_isPrime (algebraMap A B)
    have hmax : (RingHom.ker (algebraMap A B)).IsMaximal :=
      Ideal.isMaximal_of_isPrime_of_ne_bot _ hne
    let _ : Field (A ⧸ RingHom.ker (algebraMap A B)) := Ideal.Quotient.field _
    let f : (A ⧸ RingHom.ker (algebraMap A B)) →+* B :=
      RingHom.kerLift (algebraMap A B)
    let _ : Algebra (A ⧸ RingHom.ker (algebraMap A B)) B := f.toAlgebra
    have : IsScalarTower A (A ⧸ RingHom.ker (algebraMap A B)) B :=
      IsScalarTower.of_algebraMap_eq' rfl
    have hint' : Algebra.IsIntegral (A ⧸ RingHom.ker (algebraMap A B)) B := .tower_top A
    exact IsDiscreteValuationRing.not_isField B
      ((hint'.isField_iff_isField (RingHom.kerLift_injective _)).mp (Field.toIsField _))
  have _ : Module.Finite A B := moduleFinite_of_isGaloisGroup (G := G)
  have _ : Module.IsTorsionFree A B := FaithfulSMul.to_isTorsionFree A B
  have _ : Algebra.IsSeparable (A ⧸ maximalIdeal A) (B ⧸ maximalIdeal B) :=
    inferInstanceAs (Algebra.IsSeparable (ResidueField A) (ResidueField B))
  rw [ramificationGroup_zero_eq_inertia,
    ← Ideal.ramificationIdxIn_eq_ramificationIdx (maximalIdeal A) (maximalIdeal B) G]
  exact Ideal.card_inertia_eq_ramificationIdxIn_of_isSeparable (G := G)
    (maximalIdeal A) (maximalIdeal B)

end InertiaCard

section LowerIndex

variable {B G : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
  [Group G] [MulSemiringAction G B]

/-- The lower index of an element of a subgroup `H ≤ G` agrees with its lower index in `G`. -/
@[simp]
theorem lowerIndex_coe_subgroup (H : Subgroup G) (h : H) :
    lowerIndex B (h : G) = lowerIndex B h := by
  simp only [lowerIndex_def, Subgroup.smul_def]

/-- If `g` has maximal lower index in its coset `g H`, then `i_G(g h) = min (i_H(h), i_G(g))` for
every `h ∈ H`. -/
theorem lowerIndex_mul_of_forall_le (H : Subgroup G) (g : G)
    (hg : ∀ h : H, lowerIndex B (g * h) ≤ lowerIndex B g) (h : H) :
    lowerIndex B (g * h) = min (lowerIndex B h) (lowerIndex B g) := by
  rw [← lowerIndex_coe_subgroup H h]
  have h₁ := min_le_lowerIndex_mul (S := B) g (h : G)
  have h₂ := min_le_lowerIndex_mul (S := B) g⁻¹ (g * h)
  rw [inv_mul_cancel_left, lowerIndex_inv, min_eq_right (hg h)] at h₂
  exact le_antisymm (le_min h₂ (hg h)) (min_comm (lowerIndex B g) _ ▸ h₁)

/-- Every coset `g H` of a finite subgroup `H ≤ G` contains an element of largest lower index. -/
theorem exists_forall_lowerIndex_mul_le (H : Subgroup G) [Finite H] (g : G) :
    ∃ h₀ : H, ∀ h : H, lowerIndex B (g * h₀ * h) ≤ lowerIndex B (g * h₀) := by
  let _ := Fintype.ofFinite H
  obtain ⟨h₀, -, hh₀⟩ := Finset.exists_max_image (Finset.univ : Finset H)
    (fun h : H ↦ lowerIndex B (g * h)) Finset.univ_nonempty
  refine ⟨h₀, fun h ↦ ?_⟩
  simpa [Subgroup.coe_mul, mul_assoc] using hh₀ (h₀ * h) (Finset.mem_univ _)

end LowerIndex

section Quotient

variable {A B G : Type*} [CommRing A] [IsLocalRing A]
  [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
  [Algebra A B] [IsLocalHom (algebraMap A B)]
  [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B] [FaithfulSMul G B]
  [Algebra.IsSeparable (ResidueField A) (ResidueField B)]

omit [IsLocalRing A] [IsDiscreteValuationRing B] [IsLocalHom (algebraMap A B)] [Finite G]
  [FaithfulSMul G B] [Algebra.IsSeparable (ResidueField A) (ResidueField B)] in
private theorem smul_sub_dvd_eval_smul_charpoly {R₀ : Type*} [CommRing R₀]
    (H : Subgroup G) [H.Normal] [Fintype H]
    [Algebra R₀ (FixedPoints.subalgebra A B H)]
    [SMulCommClass (G ⧸ H) R₀ (FixedPoints.subalgebra A B H)]
    {y : FixedPoints.subalgebra A B H} (hy : Algebra.adjoin R₀ {y} = ⊤) (g : G) (x : B) :
    g • (y : B) - (y : B) ∣ (g • MulSemiringAction.charpoly H x).eval x := by
  set P := MulSemiringAction.charpoly H x
  rw [← sub_zero ((g • P).eval x), ← MulSemiringAction.eval_charpoly H x, ← eval_sub,
    eval_eq_sum_range]
  refine Finset.dvd_sum fun n _ ↦ Dvd.dvd.mul_right ?_ _
  let w : FixedPoints.subalgebra A B H := ⟨P.coeff n, MulSemiringAction.smul_coeff_charpoly x n⟩
  have hdvd := TauCeti.smul_sub_dvd_smul_sub_of_adjoin_singleton_eq_top hy
    (QuotientGroup.mk' H g) w
  rw [← TauCeti.dvd_coe_fixedPoints_subalgebra_iff] at hdvd
  simpa only [AddSubgroupClass.coe_sub, TauCeti.coe_quotient_mk'_smul_subalgebra, coeff_sub,
    AddMonoidAlgebra.coeff_smul_apply] using hdvd

omit [IsLocalRing A] [IsDiscreteValuationRing B] [IsLocalHom (algebraMap A B)] [Finite G]
  [Algebra.IsSeparable (ResidueField A) (ResidueField B)] in
private theorem eval_smul_charpoly_dvd_sub_smul {R₀ : Type*} [CommRing R₀] [Algebra R₀ B]
    [SMulCommClass G R₀ B] (H : Subgroup G) [Fintype H]
    {x : B} (hx : Algebra.adjoin R₀ {x} = ⊤) (y : FixedPoints.subalgebra A B H) (g : G) :
    (g • MulSemiringAction.charpoly H x).eval x ∣ (y : B) - g • (y : B) := by
  obtain ⟨q, hq⟩ : ∃ q : R₀[X], aeval x q = (y : B) := by
    rw [← AlgHom.mem_range, ← Algebra.adjoin_singleton_eq_range_aeval, hx]
    exact Algebra.mem_top
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
  refine ⟨(g • r).eval x, ?_⟩
  rw [← eval_mul, ← smul_mul', ← hr, hgQ, eval_sub, eval_C, eval_map_algebraMap, hq]

/-- **Serre's quotient formula for the lower index** on discrete valuation rings. For a normal
subgroup `H ≤ G` with invariant ring `B^H = FixedPoints.subalgebra A B H` and any `g : G`,
`e(B / B^H) · i_{G ⧸ H}(g H) = ∑_{h ∈ H} i_G(g h)`. -/
theorem ramificationIdx_mul_lowerIndex_quotient_mk_eq_sum (H : Subgroup G) [H.Normal] (g : G) :
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
    ⟨Quotient.ind fun g' r c ↦ Subtype.ext <| by
      -- Both sides coerce to `B`, where `R₀` is fixed by `G`.
      change g' • ((r : B) * (c : B)) = (r : B) * (g' • (c : B))
      rw [smul_mul', r.2 g']⟩
  have _ : FaithfulSMul R₀ B :=
    (faithfulSMul_iff_algebraMap_injective R₀ B).2 Subtype.val_injective
  have _ : FaithfulSMul C B :=
    (faithfulSMul_iff_algebraMap_injective C B).2 Subtype.val_injective
  let _ : IsGaloisGroup G R₀ B := ⟨inferInstance, inferInstance, inferInstance⟩
  have _ : Module.Finite R₀ B := moduleFinite_of_isGaloisGroup (G := G)
  have _ : Module.Finite R₀ C := Module.Finite.of_injective
    (IsScalarTower.toAlgHom R₀ C B).toLinearMap Subtype.val_injective
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
  rw [finsum_eq_sum_of_fintype, lowerIndex_eq_addVal_of_adjoin_singleton_eq_top hy,
    ← nsmul_eq_mul, ← TauCeti.IsDiscreteValuationRing.addVal_algebraMap (S := C) (T := B),
    map_sub, Subalgebra.algebraMap_apply, Subalgebra.algebraMap_apply,
    TauCeti.coe_quotient_mk'_smul_subalgebra, key, TauCeti.MulSemiringAction.eval_smul_charpoly,
    AddValuation.map_prod]
  refine Finset.sum_congr rfl fun h _ ↦ ?_
  rw [lowerIndex_eq_addVal_of_adjoin_singleton_eq_top hx, mul_smul, Subgroup.smul_def,
    AddValuation.map_sub_swap]

private theorem ramificationIdx_mul_lowerIndex_quotient_mk_eq_sum_card
    (H : Subgroup G) [H.Normal] (g : G) {j : ℕ} (hj : lowerIndex B g = j)
    (hg : ∀ h : H, lowerIndex B (g * h) ≤ lowerIndex B g) :
    ((maximalIdeal B).ramificationIdx (FixedPoints.subalgebra A B H) : ℕ∞) *
        lowerIndex (FixedPoints.subalgebra A B H) (QuotientGroup.mk' H g) =
      ∑ k ∈ Finset.range j, (Nat.card (ramificationGroup H B k) : ℕ∞) := by
  let _ := Fintype.ofFinite H
  rw [ramificationIdx_mul_lowerIndex_quotient_mk_eq_sum (A := A) H g, finsum_eq_sum_of_fintype]
  simp_rw [lowerIndex_mul_of_forall_le H g hg, hj]
  exact sum_min_lowerIndex_natCast (G := H) (S := B) j

private theorem lowerIndex_quotient_mk_ne_top (H : Subgroup G) [H.Normal] (g : G)
    (hj : lowerIndex B g ≠ ⊤) (hg : ∀ h : H, lowerIndex B (g * h) ≤ lowerIndex B g) :
    lowerIndex (FixedPoints.subalgebra A B H) (QuotientGroup.mk' H g) ≠ ⊤ := by
  obtain ⟨j, hj⟩ := ENat.ne_top_iff_exists.1 hj
  intro htop
  have hsum := ramificationIdx_mul_lowerIndex_quotient_mk_eq_sum_card (A := A) H g hj.symm hg
  let _ : IsGaloisGroup H (FixedPoints.subalgebra A B H) B :=
    ⟨inferInstance, inferInstance, inferInstance⟩
  have _ : Algebra.IsSeparable (ResidueField (FixedPoints.subalgebra A B H)) (ResidueField B) :=
    Algebra.isSeparable_tower_top_of_isSeparable (ResidueField A) _ (ResidueField B)
  have he : ((maximalIdeal B).ramificationIdx (FixedPoints.subalgebra A B H) : ℕ∞) ≠ 0 := by
    rw [← natCard_ramificationGroup_zero (A := FixedPoints.subalgebra A B H) (B := B) (G := H)]
    exact Nat.cast_ne_zero.2 Nat.card_pos.ne'
  rw [htop, ENat.mul_top he, ← Nat.cast_sum] at hsum
  exact ENat.natCast_ne_top _ hsum.symm

/-- **Serre's lemma on the lower index of a quotient.** If `g` has maximal lower index in its coset
`g H` and `i_G(g) = j` is finite, then `φ_H(j - 1) = i_{G ⧸ H}(g H) - 1`. -/
theorem herbrandFun_lowerIndex_sub_one (A : Type*) [CommRing A] [IsLocalRing A] [Algebra A B]
    [IsLocalHom (algebraMap A B)] [SMulCommClass G A B]
    [Algebra.IsSeparable (ResidueField A) (ResidueField B)]
    (H : Subgroup G) [H.Normal] (g : G) {j : ℕ}
    (hj : lowerIndex B g = j) (hg : ∀ h : H, lowerIndex B (g * h) ≤ lowerIndex B g) :
    herbrandFun H B ((j : ℝ) - 1) =
      ((lowerIndex (FixedPoints.subalgebra A B H) (QuotientGroup.mk' H g)).toNat : ℝ) - 1 := by
  have hsum := ramificationIdx_mul_lowerIndex_quotient_mk_eq_sum_card (A := A) H g hj hg
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1
    (lowerIndex_quotient_mk_ne_top (A := A) H g (hj ▸ ENat.natCast_ne_top j) hg)
  let _ : IsGaloisGroup H (FixedPoints.subalgebra A B H) B :=
    ⟨inferInstance, inferInstance, inferInstance⟩
  have _ : Algebra.IsSeparable (ResidueField (FixedPoints.subalgebra A B H)) (ResidueField B) :=
    Algebra.isSeparable_tower_top_of_isSeparable (ResidueField A) _ (ResidueField B)
  rw [← hn, ← Nat.cast_mul, ← Nat.cast_sum, Nat.cast_inj,
    ← natCard_ramificationGroup_zero (A := FixedPoints.subalgebra A B H) (B := B) (G := H)] at hsum
  rw [← hn, ENat.toNat_natCast]
  have h0 : (Nat.card (ramificationGroup H B 0) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  rcases j with _ | m
  · rw [herbrandFun_eq_self_of_mem_Icc H B (by norm_num) (by norm_num)]
    simp only [Finset.range_zero, Finset.sum_empty, mul_eq_zero, Nat.card_pos.ne', false_or] at hsum
    simp [hsum]
  · have hm : ((m + 1 : ℕ) : ℝ) - 1 = m := by push_cast; ring
    rw [hm, herbrandFun_natCast, div_eq_iff h0]
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (Nat.add_one_pos m), Nat.cast_zero,
      zero_add, Finset.Ico_add_one_right_eq_Icc] at hsum
    have hsumR : (Nat.card (ramificationGroup H B 0) : ℝ) * n =
        Nat.card (ramificationGroup H B 0) +
          ∑ i ∈ Finset.Icc 1 m, (Nat.card (ramificationGroup H B i) : ℝ) := by
      exact_mod_cast hsum
    linear_combination -hsumR

private theorem quotient_mk_mem_ramificationGroupReal_herbrandFun_iff
    (H : Subgroup G) [H.Normal] (g : G)
    (hg : ∀ h : H, lowerIndex B (g * h) ≤ lowerIndex B g) (u : ℝ) :
    QuotientGroup.mk' H g ∈
        ramificationGroupReal (G ⧸ H) (FixedPoints.subalgebra A B H) (herbrandFun H B u) ↔
      g ∈ ramificationGroupReal G B u := by
  rcases eq_or_ne (lowerIndex B g) ⊤ with htop | htop
  · rw [lowerIndex_eq_top_iff] at htop
    subst htop
    rw [map_one]
    exact iff_of_true (one_mem _) (one_mem _)
  obtain ⟨j, hj⟩ := ENat.ne_top_iff_exists.1 htop
  rw [mem_ramificationGroupReal_iff_of_lowerIndex_eq
      (ENat.natCast_toNat (lowerIndex_quotient_mk_ne_top (A := A) H g htop hg)).symm,
    ← herbrandFun_lowerIndex_sub_one A H g hj.symm hg,
    mem_ramificationGroupReal_iff_of_lowerIndex_eq hj.symm]
  exact (herbrandFun_strictMono H B).le_iff_le

/-- **Herbrand's lemma.** For a normal subgroup `H ≤ G`, the lower ramification group of `G ⧸ H`
acting on `FixedPoints.subalgebra A B H` at `φ_H(u)` is the image of `G_u` under `G → G ⧸ H`. -/
@[simp]
theorem ramificationGroupReal_quotient_herbrandFun (H : Subgroup G) [H.Normal] (u : ℝ) :
    ramificationGroupReal (G ⧸ H) (FixedPoints.subalgebra A B H) (herbrandFun H B u) =
      (ramificationGroupReal G B u).map (QuotientGroup.mk' H) := by
  have hmk : ∀ (g : G) (h : H), QuotientGroup.mk' H (g * h) = QuotientGroup.mk' H g := fun g h ↦ by
    rw [map_mul, QuotientGroup.mk'_apply H (h : G), (QuotientGroup.eq_one_iff _).2 h.2, mul_one]
  ext q
  rw [Subgroup.mem_map]
  constructor
  · intro hq
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective H q
    obtain ⟨h₀, hh₀⟩ := exists_forall_lowerIndex_mul_le (B := B) H g
    refine ⟨g * h₀, ?_, hmk g h₀⟩
    rwa [← quotient_mk_mem_ramificationGroupReal_herbrandFun_iff (A := A) H (g * h₀) hh₀, hmk]
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨h₀, hh₀⟩ := exists_forall_lowerIndex_mul_le (B := B) H g
    rw [← hmk g h₀, quotient_mk_mem_ramificationGroupReal_herbrandFun_iff (A := A) H (g * h₀) hh₀]
    rw [ramificationGroupReal_def, mem_ramificationGroup_iff_le_lowerIndex] at hg ⊢
    exact hg.trans (by simpa [mul_inv_cancel_right] using hh₀ h₀⁻¹)

/-- Herbrand's lemma read at `v = φ_H(u)`: `(G ⧸ H)_v = (G_{ψ_H(v)}).map (QuotientGroup.mk' H)`. -/
theorem ramificationGroupReal_quotient_eq_map_inverseHerbrandFun
    (H : Subgroup G) [H.Normal] (v : ℝ) :
    ramificationGroupReal (G ⧸ H) (FixedPoints.subalgebra A B H) v =
      (ramificationGroupReal G B (inverseHerbrandFun H B v)).map (QuotientGroup.mk' H) := by
  rw [← ramificationGroupReal_quotient_herbrandFun (A := A), herbrandFun_inverseHerbrandFun]

/-! ### Counting form and transitivity of the Herbrand functions -/

/-- **Herbrand's lemma in counting form**: `#(G ⧸ H)_{φ_H(u)} · #H_u = #G_u`. -/
theorem natCard_ramificationGroupReal_quotient_herbrandFun_mul
    (H : Subgroup G) [H.Normal] (u : ℝ) :
    Nat.card (ramificationGroupReal (G ⧸ H) (FixedPoints.subalgebra A B H) (herbrandFun H B u)) *
        Nat.card (ramificationGroupReal H B u) =
      Nat.card (ramificationGroupReal G B u) := by
  rw [ramificationGroupReal_quotient_herbrandFun, ← MonoidHom.domRestrict_range]
  have hker : ((QuotientGroup.mk' H).domRestrict (ramificationGroupReal G B u)).ker =
      H.subgroupOf (ramificationGroupReal G B u) := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.domRestrict_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hcard : Nat.card (H.subgroupOf (ramificationGroupReal G B u)) =
      Nat.card (ramificationGroupReal H B u) := by
    rw [← subgroupOf_ramificationGroupReal G B H u, ← Subgroup.card_subtype,
      ← Subgroup.card_subtype, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      inf_comm]
  rw [← hcard, ← hker, mul_comm]
  exact Subgroup.card_ker_mul_card_range _

private theorem natCard_ramificationGroup_quotient_zero_mul (H : Subgroup G) [H.Normal] :
    Nat.card (ramificationGroup (G ⧸ H) (FixedPoints.subalgebra A B H) 0) *
        Nat.card (ramificationGroup H B 0) =
      Nat.card (ramificationGroup G B 0) := by
  have h := natCard_ramificationGroupReal_quotient_herbrandFun_mul (A := A) (B := B) H 0
  rwa [herbrandFun_zero, ← Int.cast_zero, ramificationGroupReal_intCast,
    ramificationGroupReal_intCast, ramificationGroupReal_intCast] at h

omit [CommRing A] [IsLocalRing A] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B]
  [IsLocalHom (algebraMap A B)] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B]
  [FaithfulSMul G B] [Algebra.IsSeparable (ResidueField A) (ResidueField B)] in
private theorem ramificationGroupReal_eq_of_mem_Ioc {K : Type*} [Group K] {S : Type*}
    [CommRing S] [IsLocalRing S] [MulSemiringAction K S] {m : ℕ} {u t : ℝ} (h₂ : u ≤ m + 1)
    (ht₁ : (m : ℝ) < t) (ht₂ : t ≤ u) :
    ramificationGroupReal K S t = ramificationGroupReal K S u := by
  rw [ramificationGroupReal_eq_of_sub_one_lt_of_le K S (i := m + 1)
      (by push_cast; linarith) (by push_cast; linarith),
    ramificationGroupReal_eq_of_sub_one_lt_of_le K S (i := m + 1)
      (by push_cast; linarith) (by push_cast; linarith)]

private theorem herbrandFun_tower_step (H : Subgroup G) [H.Normal] (m : ℕ) {u : ℝ}
    (h₁ : (m : ℝ) ≤ u) (h₂ : u ≤ m + 1)
    (hm : herbrandFun G B m =
      herbrandFun (G ⧸ H) (FixedPoints.subalgebra A B H) (herbrandFun H B m)) :
    herbrandFun G B u =
      herbrandFun (G ⧸ H) (FixedPoints.subalgebra A B H) (herbrandFun H B u) := by
  set C := FixedPoints.subalgebra A B H
  have hQ : ∀ t : ℝ, herbrandFun H B m < t → t ≤ herbrandFun H B u →
      ramificationGroupReal (G ⧸ H) C t =
        ramificationGroupReal (G ⧸ H) C (herbrandFun H B u) := fun t ht₁ ht₂ ↦ by
    have hs₁ : (m : ℝ) < inverseHerbrandFun H B t := by
      simpa only [inverseHerbrandFun_herbrandFun] using inverseHerbrandFun_strictMono H B ht₁
    have hs₂ : inverseHerbrandFun H B t ≤ u := by
      simpa only [inverseHerbrandFun_herbrandFun] using
        (inverseHerbrandFun_strictMono H B).monotone ht₂
    rw [ramificationGroupReal_quotient_eq_map_inverseHerbrandFun,
      ramificationGroupReal_quotient_herbrandFun,
      ramificationGroupReal_eq_of_mem_Ioc h₂ hs₁ hs₂]
  have hsubG := herbrandFun_sub_of_forall_eq G B h₁ fun _ ↦ ramificationGroupReal_eq_of_mem_Ioc h₂
  have hsubH := herbrandFun_sub_of_forall_eq H B h₁ fun _ ↦ ramificationGroupReal_eq_of_mem_Ioc h₂
  have hsubQ := herbrandFun_sub_of_forall_eq (G ⧸ H) C
    ((herbrandFun_strictMono H B).monotone h₁) hQ
  have hcard : (Nat.card (ramificationGroupReal (G ⧸ H) C (herbrandFun H B u)) : ℝ) *
      Nat.card (ramificationGroupReal H B u) = Nat.card (ramificationGroupReal G B u) := by
    exact_mod_cast natCard_ramificationGroupReal_quotient_herbrandFun_mul (A := A) H u
  have hcard₀ : (Nat.card (ramificationGroup (G ⧸ H) C 0) : ℝ) *
      Nat.card (ramificationGroup H B 0) = Nat.card (ramificationGroup G B 0) := by
    exact_mod_cast natCard_ramificationGroup_quotient_zero_mul (A := A) H
  have hslope : (Nat.card (ramificationGroupReal G B u) : ℝ) /
      Nat.card (ramificationGroup G B 0) =
        (Nat.card (ramificationGroupReal H B u) / Nat.card (ramificationGroup H B 0)) *
          (Nat.card (ramificationGroupReal (G ⧸ H) C (herbrandFun H B u)) /
            Nat.card (ramificationGroup (G ⧸ H) C 0)) := by
    rw [div_mul_div_comm, ← hcard, ← hcard₀,
      mul_comm (Nat.card (ramificationGroupReal H B u) : ℝ),
      mul_comm (Nat.card (ramificationGroup H B 0) : ℝ)]
  rw [hslope] at hsubG
  rw [hsubH] at hsubQ
  linear_combination hsubG - hsubQ + hm

private theorem herbrandFun_tower_of_mem_Icc (H : Subgroup G) [H.Normal] (m : ℕ) :
    ∀ {u : ℝ}, (m : ℝ) ≤ u → u ≤ m + 1 →
      herbrandFun G B u =
        herbrandFun (G ⧸ H) (FixedPoints.subalgebra A B H) (herbrandFun H B u) := by
  induction m with
  | zero => exact fun h₁ h₂ ↦ herbrandFun_tower_step (A := A) H 0 h₁ h₂ (by simp)
  | succ k ih =>
    exact fun h₁ h₂ ↦ herbrandFun_tower_step (A := A) H (k + 1) h₁ h₂
      (ih (by push_cast; linarith) (by push_cast; linarith))

/-- **Transitivity of the Herbrand function** for a normal subgroup `H ≤ G`:
`φ_G(u) = φ_{G ⧸ H}(φ_H(u))` for every real `u`. -/
theorem herbrandFun_tower (A : Type*) [CommRing A] [IsLocalRing A] [Algebra A B]
    [IsLocalHom (algebraMap A B)] [SMulCommClass G A B]
    [Algebra.IsSeparable (ResidueField A) (ResidueField B)]
    (H : Subgroup G) [H.Normal] (u : ℝ) :
    herbrandFun G B u =
      herbrandFun (G ⧸ H) (FixedPoints.subalgebra A B H) (herbrandFun H B u) := by
  set C := FixedPoints.subalgebra A B H
  rcases lt_trichotomy u (-1) with hu | rfl | hu
  · have hH : herbrandFun H B u ≤ -1 :=
      le_of_not_ge fun h ↦ hu.not_ge ((neg_one_le_herbrandFun_iff H B).1 h)
    rw [herbrandFun_of_le_neg_one G B hu.le, herbrandFun_of_le_neg_one (G ⧸ H) C hH,
      herbrandFun_of_le_neg_one H B hu.le]
    have hG : (Nat.card (G ⧸ H) : ℝ) * Nat.card H = Nat.card G := by
      rw [mul_comm, ← H.index_eq_card]
      exact_mod_cast H.card_mul_index
    have h0 : (Nat.card (ramificationGroup (G ⧸ H) C 0) : ℝ) *
        Nat.card (ramificationGroup H B 0) = Nat.card (ramificationGroup G B 0) := by
      exact_mod_cast natCard_ramificationGroup_quotient_zero_mul (A := A) H
    have hslope : (Nat.card G : ℝ) / Nat.card (ramificationGroup G B 0) =
        (Nat.card H / Nat.card (ramificationGroup H B 0)) *
          (Nat.card (G ⧸ H) / Nat.card (ramificationGroup (G ⧸ H) C 0)) := by
      rw [div_mul_div_comm, ← hG, ← h0, mul_comm (Nat.card H : ℝ),
        mul_comm (Nat.card (ramificationGroup H B 0) : ℝ)]
    rw [hslope]
    ring
  · simp
  · rcases le_or_gt u 0 with hu0 | hu0
    · rw [herbrandFun_eq_self_of_mem_Icc H B hu.le hu0,
        herbrandFun_eq_self_of_mem_Icc (G ⧸ H) C hu.le hu0,
        herbrandFun_eq_self_of_mem_Icc G B hu.le hu0]
    · exact herbrandFun_tower_of_mem_Icc (A := A) H ⌊u⌋₊
        (Nat.floor_le hu0.le) (Nat.lt_floor_add_one u).le

/-- **Transitivity of the inverse Herbrand function** for a normal subgroup `H ≤ G`:
`ψ_G(v) = ψ_H(ψ_{G ⧸ H}(v))` for every real `v`. -/
theorem inverseHerbrandFun_tower (A : Type*) [CommRing A] [IsLocalRing A] [Algebra A B]
    [IsLocalHom (algebraMap A B)] [SMulCommClass G A B]
    [Algebra.IsSeparable (ResidueField A) (ResidueField B)]
    (H : Subgroup G) [H.Normal] (v : ℝ) :
    inverseHerbrandFun G B v =
      inverseHerbrandFun H B
        (inverseHerbrandFun (G ⧸ H) (FixedPoints.subalgebra A B H) v) := by
  apply (herbrandFun_strictMono G B).injective
  rw [herbrandFun_inverseHerbrandFun, herbrandFun_tower A H,
    herbrandFun_inverseHerbrandFun, herbrandFun_inverseHerbrandFun]

/-- **Transitivity of the bundled Herbrand order isomorphisms** on `[-1, ∞)`. -/
theorem herbrandOrderIso_tower (A : Type*) [CommRing A] [IsLocalRing A] [Algebra A B]
    [IsLocalHom (algebraMap A B)] [SMulCommClass G A B]
    [Algebra.IsSeparable (ResidueField A) (ResidueField B)]
    (H : Subgroup G) [H.Normal] :
    herbrandOrderIso G B =
      (herbrandOrderIso H B).trans
        (herbrandOrderIso (G ⧸ H) (FixedPoints.subalgebra A B H)) :=
  OrderIso.ext <| funext fun u ↦ Subtype.ext <| by
    simp only [OrderIso.trans_apply, coe_herbrandOrderIso_apply]
    exact herbrandFun_tower A (B := B) H (u : ℝ)

/-- **Transitivity of the integral inverse Herbrand function**: `ψℕ_G = ψℕ_H ∘ ψℕ_{G ⧸ H}`. -/
theorem psiNat_tower (A : Type*) [CommRing A] [IsLocalRing A] [Algebra A B]
    [IsLocalHom (algebraMap A B)] [SMulCommClass G A B]
    [Algebra.IsSeparable (ResidueField A) (ResidueField B)]
    (H : Subgroup G) [H.Normal] :
    psiNat G B = psiNat H B ∘ psiNat (G ⧸ H) (FixedPoints.subalgebra A B H) :=
  funext fun n ↦ Nat.cast_injective (R := ℝ) <| by
    rw [Function.comp_apply, coe_psiNat, coe_psiNat, coe_psiNat, inverseHerbrandFun_tower A H]

/-! ### Herbrand's theorem in the upper numbering and breaks in a tower -/

/-- **Herbrand's theorem.** For a normal subgroup `H ≤ G`, the upper ramification group of `G ⧸ H`
acting on `FixedPoints.subalgebra A B H` at `v` is the image of `G^v` under `G → G ⧸ H`:
`(G ⧸ H)^v = G^v H / H`. -/
@[simp]
theorem upperRamificationGroup_quotient_eq_map (H : Subgroup G) [H.Normal] (v : ℝ) :
    upperRamificationGroup (G ⧸ H) (FixedPoints.subalgebra A B H) v =
      (upperRamificationGroup G B v).map (QuotientGroup.mk' H) := by
  rw [upperRamificationGroup_def, upperRamificationGroup_def, inverseHerbrandFun_tower A H,
    ramificationGroupReal_quotient_eq_map_inverseHerbrandFun]

/-- **Upper filtration of a normal subgroup**: `H ∩ G^v = H^{ψ_{G ⧸ H}(v)}`. -/
theorem subgroupOf_upperRamificationGroup_eq_inverseHerbrandFun
    (A : Type*) [CommRing A] [IsLocalRing A] [Algebra A B]
    [IsLocalHom (algebraMap A B)] [SMulCommClass G A B]
    [Algebra.IsSeparable (ResidueField A) (ResidueField B)]
    (H : Subgroup G) [H.Normal] (v : ℝ) :
    (upperRamificationGroup G B v).subgroupOf H =
      upperRamificationGroup H B
        (inverseHerbrandFun (G ⧸ H) (FixedPoints.subalgebra A B H) v) := by
  rw [subgroupOf_upperRamificationGroup, inverseHerbrandFun_tower A H,
    herbrandFun_inverseHerbrandFun]

/-- Every upper break of `G ⧸ H` on `B^H` is an upper break of `G` on `B`. -/
theorem UpperJump.of_quotient {H : Subgroup G} [H.Normal] {v : ℝ}
    (hv : UpperJump (G ⧸ H) (FixedPoints.subalgebra A B H) v) :
    UpperJump G B v :=
  (upperJump_iff G B v).2 fun w hvw ↦
    lt_of_le_of_ne (upperRamificationGroup_antitone G B hvw.le) fun heq ↦
      ((upperJump_iff _ _ v).1 hv w hvw).ne <| by
        rw [upperRamificationGroup_quotient_eq_map, heq,
          ← upperRamificationGroup_quotient_eq_map (A := A)]

/-- If `ψ_{G ⧸ H}(v)` is an upper break of a normal subgroup `H ≤ G` on `B`, then `v` is an upper
break of `G` on `B`. -/
theorem UpperJump.of_inverseHerbrandFun {H : Subgroup G} [H.Normal] {v : ℝ}
    (hv : UpperJump H B (inverseHerbrandFun (G ⧸ H) (FixedPoints.subalgebra A B H) v)) :
    UpperJump G B v :=
  (upperJump_iff G B v).2 fun w hvw ↦
    lt_of_le_of_ne (upperRamificationGroup_antitone G B hvw.le) fun heq ↦ by
      have hlt := (upperJump_iff H B _).1 hv _
        (inverseHerbrandFun_strictMono (G ⧸ H) (FixedPoints.subalgebra A B H) hvw)
      rw [← subgroupOf_upperRamificationGroup_eq_inverseHerbrandFun A H,
        ← subgroupOf_upperRamificationGroup_eq_inverseHerbrandFun A H, heq] at hlt
      exact hlt.ne rfl

/-- **Upper breaks in a quotient tower**: `v` is an upper break of `G` if and only if `v` is an
upper break of `G ⧸ H` on `B^H` or `ψ_{G ⧸ H}(v)` is an upper break of `H` on `B`. -/
theorem upperJump_iff_upperJump_quotient_or_upperJump_inverseHerbrandFun
    (A : Type*) [CommRing A] [IsLocalRing A] [Algebra A B]
    [IsLocalHom (algebraMap A B)] [SMulCommClass G A B]
    [Algebra.IsSeparable (ResidueField A) (ResidueField B)]
    (H : Subgroup G) [H.Normal] (v : ℝ) :
    UpperJump G B v ↔
      UpperJump (G ⧸ H) (FixedPoints.subalgebra A B H) v ∨
        UpperJump H B (inverseHerbrandFun (G ⧸ H) (FixedPoints.subalgebra A B H) v) := by
  constructor
  · intro hv
    refine or_iff_not_imp_left.2 fun hQ ↦ (upperJump_iff H B _).2 fun x hx ↦ ?_
    simp only [upperJump_iff, not_forall] at hQ
    obtain ⟨w₀, hvw₀, hlt⟩ := hQ
    have hw₀ : upperRamificationGroup (G ⧸ H) (FixedPoints.subalgebra A B H) w₀ =
        upperRamificationGroup (G ⧸ H) (FixedPoints.subalgebra A B H) v :=
      (upperRamificationGroup_antitone (G ⧸ H) _ hvw₀.le).eq_of_not_lt hlt
    set w := min w₀ (herbrandFun (G ⧸ H) (FixedPoints.subalgebra A B H) x)
    have hvw : v < w := lt_min hvw₀ <| by
      simpa only [herbrandFun_inverseHerbrandFun] using
        herbrandFun_strictMono (G ⧸ H) (FixedPoints.subalgebra A B H) hx
    have hw : upperRamificationGroup (G ⧸ H) (FixedPoints.subalgebra A B H) w =
        upperRamificationGroup (G ⧸ H) (FixedPoints.subalgebra A B H) v :=
      le_antisymm (upperRamificationGroup_antitone (G ⧸ H) _ hvw.le)
        (hw₀ ▸ upperRamificationGroup_antitone (G ⧸ H) _ (min_le_left _ _))
    have hxw : inverseHerbrandFun (G ⧸ H) (FixedPoints.subalgebra A B H) w ≤ x := by
      simpa only [inverseHerbrandFun_herbrandFun] using
        (inverseHerbrandFun_strictMono (G ⧸ H) (FixedPoints.subalgebra A B H)).monotone
          (min_le_right w₀ (herbrandFun (G ⧸ H) (FixedPoints.subalgebra A B H) x))
    refine (upperRamificationGroup_antitone H B hxw).trans_lt ?_
    rw [← subgroupOf_upperRamificationGroup_eq_inverseHerbrandFun A H,
      ← subgroupOf_upperRamificationGroup_eq_inverseHerbrandFun A H]
    refine lt_of_le_of_ne (Subgroup.comap_mono (upperRamificationGroup_antitone G B hvw.le))
      fun heq ↦ ((upperJump_iff G B v).1 hv w hvw).not_ge fun σ hσ ↦ ?_
    obtain ⟨τ, hτ, hτσ⟩ : QuotientGroup.mk' H σ ∈
        (upperRamificationGroup G B w).map (QuotientGroup.mk' H) := by
      rw [← upperRamificationGroup_quotient_eq_map (A := A), hw,
        upperRamificationGroup_quotient_eq_map]
      exact Subgroup.mem_map_of_mem _ hσ
    have hmemH : τ⁻¹ * σ ∈ H := QuotientGroup.eq.1 hτσ
    have hρw : (⟨τ⁻¹ * σ, hmemH⟩ : H) ∈ (upperRamificationGroup G B w).subgroupOf H := by
      rw [heq, Subgroup.mem_subgroupOf]
      exact mul_mem (inv_mem (upperRamificationGroup_antitone G B hvw.le hτ)) hσ
    rw [Subgroup.mem_subgroupOf] at hρw
    simpa only [mul_inv_cancel_left] using mul_mem hτ hρw
  · rintro (hQ | hH)
    · exact hQ.of_quotient
    · exact hH.of_inverseHerbrandFun

end Quotient

section IntegralClosureFixedField

open _root_.IntermediateField

/-- The `A`-subalgebra of `H`-fixed elements of `integralClosure A L` is ring-isomorphic to
`integralClosure A (IntermediateField.fixedField H)`. -/
def fixedPointsSubalgebraIntegralClosureEquiv {A K L : Type*} [CommRing A] [Field K] [Field L]
    [Algebra A K] [Algebra K L] [Algebra A L] [IsScalarTower A K L] (H : Subgroup (L ≃ₐ[K] L)) :
    FixedPoints.subalgebra A (integralClosure A L) H ≃+*
      integralClosure A (fixedField H) where
  toFun x := ⟨⟨(x.1 : L), fun h ↦ congrArg Subtype.val (x.2 h)⟩, by
    have _ : IsScalarTower A (fixedField H) L := IsScalarTower.of_algebraMap_eq' rfl
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom A (fixedField H) L)
      (fixedField H).val.injective).mp x.1.2⟩
  invFun y := ⟨⟨(y.1 : L), by
    have _ : IsScalarTower A (fixedField H) L := IsScalarTower.of_algebraMap_eq' rfl
    exact y.2.map (IsScalarTower.toAlgHom A (fixedField H) L)⟩,
    fun h ↦ Subtype.ext (y.1.2 h)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

/-- If `integralClosure A L` is a local ring, then `integralClosure A (fixedField H)` is also a
local ring for every subgroup `H ≤ Gal(L/K)`. -/
instance instIsLocalRingIntegralClosureFixedField {A K L : Type*} [CommRing A] [Field K] [Field L]
    [Algebra A K] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [IsLocalRing (integralClosure A L)] (H : Subgroup (L ≃ₐ[K] L)) :
    IsLocalRing (integralClosure A (fixedField H)) :=
  (fixedPointsSubalgebraIntegralClosureEquiv (A := A) H).isLocalRing

/-- If `integralClosure A L` is a discrete valuation ring and `H ≤ Gal(L/K)` is a finite subgroup,
then `integralClosure A (fixedField H)` is also a discrete valuation ring. -/
instance instIsDiscreteValuationRingIntegralClosureFixedField {A K L : Type*} [CommRing A]
    [Field K] [Field L] [Algebra A K] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [IsDiscreteValuationRing (integralClosure A L)]
    (H : Subgroup (L ≃ₐ[K] L)) [Finite H] :
    IsDiscreteValuationRing (integralClosure A (fixedField H)) :=
  let e := fixedPointsSubalgebraIntegralClosureEquiv (A := A) H
  have : IsPrincipalIdealRing (integralClosure A (fixedField H)) :=
    IsPrincipalIdealRing.of_surjective e.toRingHom e.surjective
  { not_a_field' := fun hbot ↦
      IsDiscreteValuationRing.not_isField
        (FixedPoints.subalgebra A (integralClosure A L) H)
        (e.toMulEquiv.isField (isField_iff_maximalIdeal_eq.2 hbot)) }

variable {A K L : Type*} [CommRing A] [IsIntegrallyClosed A] [IsLocalRing A]
  [Field K] [Field L] [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [FiniteDimensional K L] [IsGalois K L]

/-- **Herbrand's theorem for Galois fixed fields.** When `integralClosure A L` is a discrete
valuation ring lying locally over `A` with separable residue extension and `H ≤ Gal(L/K)` is normal,
`IsGalois.normalAutEquivQuotient H` maps the quotient image of `Gal(L/K)^v` onto
`Gal(L^H / K)^v`. -/
theorem map_normalAutEquivQuotient_upperRamificationGroup
    [IsDiscreteValuationRing (integralClosure A L)]
    [IsLocalHom (algebraMap A (integralClosure A L))]
    [Algebra.IsSeparable (ResidueField A) (ResidueField (integralClosure A L))]
    (H : Subgroup (L ≃ₐ[K] L)) [H.Normal] (v : ℝ) :
    ((upperRamificationGroup (L ≃ₐ[K] L) (integralClosure A L) v).map
        (QuotientGroup.mk' H)).map (IsGalois.normalAutEquivQuotient H).toMonoidHom =
      upperRamificationGroup (fixedField H ≃ₐ[K] fixedField H)
        (integralClosure A (fixedField H)) v := by
  have _ : IsGaloisGroup (L ≃ₐ[K] L) A (integralClosure A L) :=
    IsGaloisGroup.of_isIntegralClosure (L ≃ₐ[K] L) A (integralClosure A L) K L
  have _ : FaithfulSMul (L ≃ₐ[K] L) (integralClosure A L) := IsGaloisGroup.faithful A
  rw [← upperRamificationGroup_quotient_eq_map (A := A) H v]
  let e := fixedPointsSubalgebraIntegralClosureEquiv (A := A) H
  let φ := IsGalois.normalAutEquivQuotient H
  have hram : ∀ i : ℤ,
      ramificationGroup ((L ≃ₐ[K] L) ⧸ H)
          (FixedPoints.subalgebra A (integralClosure A L) H) i =
        (ramificationGroup (fixedField H ≃ₐ[K] fixedField H)
          (integralClosure A (fixedField H)) i).comap φ.toMonoidHom :=
    ramificationGroup_eq_comap_of_comap_maximalIdeal_pow φ.toMonoidHom (e : _ →+* _)
      (Quotient.ind fun σ x ↦ Subtype.ext <| Subtype.ext <|
        (AlgEquiv.restrictNormalHom_apply (fixedField H) σ (e x).1).symm)
      (fun n ↦ by
        rw [Ideal.comap_coe, ← Ideal.map_symm e, Ideal.map_pow, map_ringEquiv_maximalIdeal])
      (fun _ y ↦ ⟨e.symm y, by simp⟩)
  rw [upperRamificationGroup_eq_comap_of_ramificationGroup_eq_comap φ hram v]
  exact Subgroup.map_comap_eq_self_of_surjective φ.surjective _

/-- Restriction `Gal(L/K) →* Gal(L^H / K)` maps `Gal(L/K)^v` onto `Gal(L^H / K)^v`. -/
@[simp]
theorem map_restrictNormalHom_upperRamificationGroup_integralClosure
    [IsDiscreteValuationRing (integralClosure A L)]
    [IsLocalHom (algebraMap A (integralClosure A L))]
    [Algebra.IsSeparable (ResidueField A) (ResidueField (integralClosure A L))]
    (H : Subgroup (L ≃ₐ[K] L)) [H.Normal] (v : ℝ) :
    (upperRamificationGroup (L ≃ₐ[K] L) (integralClosure A L) v).map
        (AlgEquiv.restrictNormalHom (fixedField H)) =
      upperRamificationGroup (fixedField H ≃ₐ[K] fixedField H)
        (integralClosure A (fixedField H)) v := by
  have hcomp : (IsGalois.normalAutEquivQuotient H).toMonoidHom.comp (QuotientGroup.mk' H) =
      AlgEquiv.restrictNormalHom (fixedField H) :=
    MonoidHom.ext (IsGalois.normalAutEquivQuotient_apply H)
  rw [← hcomp, ← Subgroup.map_map, map_normalAutEquivQuotient_upperRamificationGroup (A := A)]

end IntegralClosureFixedField

end TauCeti.IsLocalRing
