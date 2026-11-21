/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DiscreteValuationRing.LowerIndex
public import TauCeti.RingTheory.IntegralClosure.Map
public import TauCeti.RingTheory.LocalRing.Herbrand.IntegralClosure

/-!
# Herbrand's theorem and transitivity of Herbrand functions on discrete valuation rings

For a faithful finite action of `G` on a DVR `B` over a local ring `A` with separable residue
extension (no completeness or residue-finiteness), we prove Herbrand's lemma
(`ramificationGroupReal_quotient_herbrandFun`), transitivity (`herbrandFun_tower`,
`inverseHerbrandFun_tower`, `herbrandOrderIso_tower`, `psiNat_tower`), Herbrand's theorem
(`upperRamificationGroup_quotient_eq_map`), upper breaks in quotients,
`TauCeti.instIsDiscreteValuationRingIntegralClosureFixedField`, and Galois tower transport, adapting
`NumberTheory/LocalField/Herbrand/{Quotient,Tower,UpperQuotient}.lean`.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §3, Lemmas 4–5 and Propositions 14–15.
* J.-P. Serre, *Sur les corps locaux à corps résiduel algébriquement clos*, Bull. Soc. Math.
  France 89 (1961), n° 3.1, pp. 127–128.
-/

public section
noncomputable section
open IsLocalRing
namespace TauCeti.IsLocalRing

section Quotient
variable (A B G : Type*) [CommRing A] [IsLocalRing A] [CommRing B] [IsDomain B]
  [IsDiscreteValuationRing B] [Algebra A B] [IsLocalHom (algebraMap A B)] [Group G] [Finite G]
  [MulSemiringAction G B] [SMulCommClass G A B] [FaithfulSMul G B]
  [Algebra.IsSeparable (ResidueField A) (ResidueField B)] (H : Subgroup G) [H.Normal]
/-- **Serre's lemma on the lower index of a quotient**: if `g` maximizes `lowerIndex` in `g H` and
`i_G(g) = j`, then `φ_H(j - 1) = i_{G ⧸ H}(g H) - 1`. -/
theorem herbrandFun_lowerIndex_sub_one (g : G) {j : ℕ} (hj : lowerIndex B g = j)
    (hg : ∀ h : H, lowerIndex B (g * h) ≤ lowerIndex B g) :
    herbrandFun H B ((j : ℝ) - 1) =
      ((lowerIndex (FixedPoints.subalgebra A B H) (QuotientGroup.mk' H g)).toNat : ℝ) - 1 := by
  have hsum := ramificationIdx_mul_lowerIndex_quotient_mk'_eq_sum_card A B G H g hj hg
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1
    (lowerIndex_quotient_mk'_ne_top A B G H g (hj ▸ ENat.natCast_ne_top j) hg)
  rw [← hn, ← Nat.cast_mul, ← Nat.cast_sum, Nat.cast_inj,
    ← natCard_ramificationGroup_zero_fixedPoints A B H] at hsum
  rw [← hn, ENat.toNat_natCast]
  rcases j with _ | m
  · rw [herbrandFun_eq_self_of_neg_one_le_of_nonpos H B (by norm_num) (by norm_num)]
    simp only [Finset.range_zero, Finset.sum_empty, mul_eq_zero, Nat.card_pos.ne', false_or] at hsum
    simp [hsum]
  · rw [(by push_cast; ring : ((m + 1 : ℕ) : ℝ) - 1 = m), herbrandFun_natCast,
      div_eq_iff (Nat.cast_ne_zero.2 Nat.card_pos.ne')]
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (Nat.add_one_pos m), Nat.cast_zero,
      zero_add, Finset.Ico_add_one_right_eq_Icc] at hsum
    linear_combination -(by exact_mod_cast hsum : (Nat.card (ramificationGroup H B 0) : ℝ) * n =
      Nat.card (ramificationGroup H B 0) +
        ∑ i ∈ Finset.Icc 1 m, (Nat.card (ramificationGroup H B i) : ℝ))
private theorem quotient_mk_mem_ramificationGroupReal_herbrandFun_iff (g : G)
    (hg : ∀ h : H, lowerIndex B (g * h) ≤ lowerIndex B g) (u : ℝ) :
    QuotientGroup.mk' H g ∈
        ramificationGroupReal (G ⧸ H) (FixedPoints.subalgebra A B H) (herbrandFun H B u) ↔
      g ∈ ramificationGroupReal G B u := by
  rcases eq_or_ne (lowerIndex B g) ⊤ with htop | htop
  · obtain rfl := lowerIndex_eq_top_iff.1 htop; simp [one_mem]
  obtain ⟨j, hj⟩ := ENat.ne_top_iff_exists.1 htop
  rw [mem_ramificationGroupReal_iff_of_lowerIndex_eq
      (ENat.natCast_toNat (lowerIndex_quotient_mk'_ne_top A B G H g htop hg)).symm,
    ← herbrandFun_lowerIndex_sub_one A B G H g hj.symm hg,
    mem_ramificationGroupReal_iff_of_lowerIndex_eq hj.symm, herbrandFun_le_herbrandFun_iff]
/-- **Herbrand's lemma**: `(G ⧸ H)_{φ_H(u)} = (G_u).map (QuotientGroup.mk' H)` for normal `H`. -/
theorem ramificationGroupReal_quotient_herbrandFun (u : ℝ) :
    ramificationGroupReal (G ⧸ H) (FixedPoints.subalgebra A B H) (herbrandFun H B u) =
      (ramificationGroupReal G B u).map (QuotientGroup.mk' H) := by
  have hmk (g : G) (h : H) : QuotientGroup.mk' H (g * h) = QuotientGroup.mk' H g := by
    simp [QuotientGroup.mk'_apply, h.property]
  ext q; rw [Subgroup.mem_map]; refine ⟨fun hq ↦ ?_, fun ⟨g, hg, hq⟩ ↦ ?_⟩
  · obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective H q
    obtain ⟨h₀, hh₀_mem, hh₀⟩ := Subgroup.exists_mem_forall_lowerIndex_mul_le (S := B) H g
    exact ⟨g * h₀, (quotient_mk_mem_ramificationGroupReal_herbrandFun_iff A B G H (g * h₀)
      (fun h ↦ hh₀ h h.property) u).1 (hmk g ⟨h₀, hh₀_mem⟩ ▸ hq), hmk g ⟨h₀, hh₀_mem⟩⟩
  · obtain ⟨h₀, hh₀_mem, hh₀⟩ := Subgroup.exists_mem_forall_lowerIndex_mul_le (S := B) H g
    rw [← hq, ← hmk g ⟨h₀, hh₀_mem⟩,
      quotient_mk_mem_ramificationGroupReal_herbrandFun_iff A B G H _ (fun h ↦ hh₀ h h.property),
      ramificationGroupReal_def, mem_ramificationGroup_iff_le_lowerIndex]
    rw [ramificationGroupReal_def, mem_ramificationGroup_iff_le_lowerIndex] at hg
    exact hg.trans (by simpa [mul_inv_cancel_right] using hh₀ h₀⁻¹ (H.inv_mem hh₀_mem))
/-- For normal `H ≤ G`, `(G ⧸ H)_v = (G_{ψ_H(v)}).map (QuotientGroup.mk' H)`. -/
theorem ramificationGroupReal_quotient_eq_map_inverseHerbrandFun (v : ℝ) :
    ramificationGroupReal (G ⧸ H) (FixedPoints.subalgebra A B H) v =
      (ramificationGroupReal G B (inverseHerbrandFun H B v)).map (QuotientGroup.mk' H) := by
  rw [← ramificationGroupReal_quotient_herbrandFun A B G, herbrandFun_inverseHerbrandFun]
/-- **Herbrand's lemma in counting form**: `#(G ⧸ H)_{φ_H(u)} · #H_u = #G_u`. -/
theorem natCard_ramificationGroupReal_quotient_herbrandFun_mul (u : ℝ) :
    Nat.card (ramificationGroupReal (G ⧸ H) (FixedPoints.subalgebra A B H) (herbrandFun H B u)) *
        Nat.card (ramificationGroupReal H B u) = Nat.card (ramificationGroupReal G B u) := by
  rw [ramificationGroupReal_quotient_herbrandFun, ← MonoidHom.domRestrict_range, mul_comm,
    ← Subgroup.card_ker_mul_card_range ((QuotientGroup.mk' H).domRestrict
      (ramificationGroupReal G B u))]
  congr 1; rw [← subgroupOf_ramificationGroupReal G B H u, ← Subgroup.card_subtype,
    ← Subgroup.card_subtype, (by ext; simp [Subgroup.mem_subgroupOf] :
      ((QuotientGroup.mk' H).domRestrict (ramificationGroupReal G B u)).ker =
        H.subgroupOf (ramificationGroupReal G B u)),
    Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype, inf_comm]
private theorem natCard_ramificationGroup_quotient_zero_mul :
    Nat.card (ramificationGroup (G ⧸ H) (FixedPoints.subalgebra A B H) 0) *
        Nat.card (ramificationGroup H B 0) = Nat.card (ramificationGroup G B 0) := by
  have h := natCard_ramificationGroupReal_quotient_herbrandFun_mul A B G H 0
  rwa [herbrandFun_zero, ← Int.cast_zero, ramificationGroupReal_intCast,
    ramificationGroupReal_intCast, ramificationGroupReal_intCast] at h
private theorem herbrandFun_tower_of_natCast_le (m : ℕ) :
    ∀ {u : ℝ}, (m : ℝ) ≤ u → u ≤ m + 1 → herbrandFun G B u =
      herbrandFun (G ⧸ H) (FixedPoints.subalgebra A B H) (herbrandFun H B u) := by
  set C := FixedPoints.subalgebra A B H
  have step (k : ℕ) {u : ℝ} (h₁ : (k : ℝ) ≤ u) (h₂ : u ≤ k + 1)
      (hk : herbrandFun G B k = herbrandFun (G ⧸ H) C (herbrandFun H B k)) :
      herbrandFun G B u = herbrandFun (G ⧸ H) C (herbrandFun H B u) := by
    have hG {t : ℝ} (ht₁ : (k : ℝ) < t) (ht₂ : t ≤ u) :
        ramificationGroupReal G B t = ramificationGroupReal G B u :=
      ramificationGroupReal_eq_of_mem_Ioc (m := k) ⟨by simpa, by push_cast; linarith⟩
        ⟨by push_cast; linarith, by push_cast; linarith⟩
    have hsubG := herbrandFun_sub_of_forall_eq G B h₁ fun _ ↦ hG
    have hsubH := herbrandFun_sub_of_forall_eq H B h₁ (H := ramificationGroupReal H B u)
      fun t ht₁ ht₂ ↦ by simp only [← subgroupOf_ramificationGroupReal G B H, hG ht₁ ht₂]
    have hsubQ := herbrandFun_sub_of_forall_eq (G ⧸ H) C ((herbrandFun_le_herbrandFun_iff H B).2 h₁)
      (H := ramificationGroupReal (G ⧸ H) C (herbrandFun H B u)) fun t ht₁ ht₂ ↦ by
        rw [ramificationGroupReal_quotient_eq_map_inverseHerbrandFun,
          ramificationGroupReal_quotient_herbrandFun,
          hG ((lt_inverseHerbrandFun_iff H B).2 ht₁) ((inverseHerbrandFun_le_iff H B).2 ht₂)]
    have hslope : (Nat.card (ramificationGroupReal G B u) : ℝ) / Nat.card (ramificationGroup G B 0)
        = (Nat.card (ramificationGroupReal H B u) / Nat.card (ramificationGroup H B 0)) *
          (Nat.card (ramificationGroupReal (G ⧸ H) C (herbrandFun H B u)) /
            Nat.card (ramificationGroup (G ⧸ H) C 0)) := by
      rw [div_mul_div_comm, mul_comm (Nat.card (ramificationGroupReal H B u) : ℝ),
        mul_comm (Nat.card (ramificationGroup H B 0) : ℝ), ← Nat.cast_mul, ← Nat.cast_mul,
        natCard_ramificationGroupReal_quotient_herbrandFun_mul,
        natCard_ramificationGroup_quotient_zero_mul]
    rw [hslope] at hsubG; rw [hsubH] at hsubQ; linear_combination hsubG - hsubQ + hk
  induction m with
  | zero => exact fun h₁ h₂ ↦ step 0 h₁ h₂ (by simp)
  | succ k ih => exact fun h₁ h₂ ↦ step (k + 1) h₁ h₂ (ih (by push_cast; linarith) (by simp))
/-- **Transitivity of the Herbrand function**: `φ_G(u) = φ_{G ⧸ H}(φ_H(u))` for normal `H ≤ G`. -/
theorem herbrandFun_tower (u : ℝ) :
    herbrandFun G B u = herbrandFun (G ⧸ H) (FixedPoints.subalgebra A B H) (herbrandFun H B u) := by
  set C := FixedPoints.subalgebra A B H
  rcases le_or_gt u (-1) with hu | hu
  · rw [herbrandFun_of_le_neg_one G B hu,
      herbrandFun_of_le_neg_one (G ⧸ H) C ((herbrandFun_le_neg_one_iff H B).2 hu),
      herbrandFun_of_le_neg_one H B hu]
    have hslope : (Nat.card G : ℝ) / Nat.card (ramificationGroup G B 0) =
        (Nat.card H / Nat.card (ramificationGroup H B 0)) *
          (Nat.card (G ⧸ H) / Nat.card (ramificationGroup (G ⧸ H) C 0)) := by
      rw [div_mul_div_comm, mul_comm (Nat.card (ramificationGroup H B 0) : ℝ), ← Nat.cast_mul,
        ← Nat.cast_mul, ← H.index_eq_card, H.card_mul_index,
        natCard_ramificationGroup_quotient_zero_mul]
    rw [hslope]; ring
  · rcases le_or_gt u 0 with hu0 | hu0
    · rw [herbrandFun_eq_self_of_neg_one_le_of_nonpos H B hu.le hu0,
        herbrandFun_eq_self_of_neg_one_le_of_nonpos (G ⧸ H) C hu.le hu0,
        herbrandFun_eq_self_of_neg_one_le_of_nonpos G B hu.le hu0]
    · exact herbrandFun_tower_of_natCast_le A B G H ⌊u⌋₊ (Nat.floor_le hu0.le)
        (Nat.lt_floor_add_one u).le
/-- **Transitivity of the inverse Herbrand function**: `ψ_G(v) = ψ_H(ψ_{G ⧸ H}(v))`. -/
theorem inverseHerbrandFun_tower (v : ℝ) : inverseHerbrandFun G B v =
    inverseHerbrandFun H B (inverseHerbrandFun (G ⧸ H) (FixedPoints.subalgebra A B H) v) := by
  rw [← herbrandFun_inj G B, herbrandFun_inverseHerbrandFun, herbrandFun_tower A B G H,
    herbrandFun_inverseHerbrandFun, herbrandFun_inverseHerbrandFun]
/-- **Transitivity of the bundled Herbrand order isomorphisms** on `[-1, ∞)`. -/
theorem herbrandOrderIso_tower : herbrandOrderIso G B =
    (herbrandOrderIso H B).trans (herbrandOrderIso (G ⧸ H) (FixedPoints.subalgebra A B H)) :=
  OrderIso.ext <| funext fun u ↦ Subtype.ext <| by simpa using herbrandFun_tower A B G H u
/-- **Transitivity of the integral inverse Herbrand function**: `ψℕ_G = ψℕ_H ∘ ψℕ_{G ⧸ H}`. -/
theorem psiNat_tower :
    psiNat G B = psiNat H B ∘ psiNat (G ⧸ H) (FixedPoints.subalgebra A B H) :=
  funext fun _ ↦ Nat.cast_injective (R := ℝ) <| by simp [inverseHerbrandFun_tower A B G H]
/-- **Herbrand's theorem**: `(G ⧸ H)^v = (G^v).map (QuotientGroup.mk' H)` for normal `H ≤ G`. -/
theorem upperRamificationGroup_quotient_eq_map (v : ℝ) :
    upperRamificationGroup (G ⧸ H) (FixedPoints.subalgebra A B H) v =
      (upperRamificationGroup G B v).map (QuotientGroup.mk' H) := by
  rw [upperRamificationGroup_def, upperRamificationGroup_def, inverseHerbrandFun_tower A B G H,
    ramificationGroupReal_quotient_eq_map_inverseHerbrandFun]
/-- **Upper filtration of a normal subgroup**: `H ∩ G^v = H^{ψ_{G ⧸ H}(v)}`. -/
theorem subgroupOf_upperRamificationGroup_eq_upperRamificationGroup_inverseHerbrandFun (v : ℝ) :
    (upperRamificationGroup G B v).subgroupOf H =
      upperRamificationGroup H B (inverseHerbrandFun (G ⧸ H) (FixedPoints.subalgebra A B H) v) := by
  rw [subgroupOf_upperRamificationGroup, inverseHerbrandFun_tower A B G H,
    herbrandFun_inverseHerbrandFun]
variable {A B G H} in
/-- An upper break of `G ⧸ H` on `B^H` is an upper break of `G` on `B`. -/
theorem UpperJump.of_quotient {v : ℝ} (hv : UpperJump (G ⧸ H) (FixedPoints.subalgebra A B H) v) :
    UpperJump G B v := by
  rw [upperJump_iff] at hv ⊢; intro w hvw
  refine lt_of_le_of_ne (upperRamificationGroup_antitone G B hvw.le) fun heq ↦ (hv w hvw).ne ?_
  rw [upperRamificationGroup_quotient_eq_map, heq, ← upperRamificationGroup_quotient_eq_map A B G]
variable {A B G H} in
/-- If `ψ_{G ⧸ H}(v)` is an upper break of `H` on `B`, then `v` is an upper break of `G` on `B`. -/
theorem UpperJump.of_inverseHerbrandFun {v : ℝ}
    (hv : UpperJump H B (inverseHerbrandFun (G ⧸ H) (FixedPoints.subalgebra A B H) v)) :
    UpperJump G B v := by
  rw [upperJump_iff] at hv ⊢; intro w hvw
  refine lt_of_le_of_ne (upperRamificationGroup_antitone G B hvw.le) fun heq ↦
    (hv _ (inverseHerbrandFun_strictMono (G ⧸ H) (FixedPoints.subalgebra A B H) hvw)).ne ?_
  rw [← subgroupOf_upperRamificationGroup_eq_upperRamificationGroup_inverseHerbrandFun A B G H,
    ← subgroupOf_upperRamificationGroup_eq_upperRamificationGroup_inverseHerbrandFun A B G H, heq]
/-- **Upper breaks in a quotient**: `UpperJump G B v` iff `UpperJump (G ⧸ H) B^H v` or
`UpperJump H B (ψ_{G ⧸ H}(v))`. -/
theorem upperJump_iff_upperJump_quotient_or_upperJump_inverseHerbrandFun (v : ℝ) :
    UpperJump G B v ↔ UpperJump (G ⧸ H) (FixedPoints.subalgebra A B H) v ∨
      UpperJump H B (inverseHerbrandFun (G ⧸ H) (FixedPoints.subalgebra A B H) v) := by
  let C := FixedPoints.subalgebra A B H
  refine ⟨fun hv ↦ or_iff_not_imp_left.2 fun hQ ↦ ?_,
    fun h ↦ h.elim UpperJump.of_quotient UpperJump.of_inverseHerbrandFun⟩
  rw [upperJump_iff] at hv ⊢; intro x hx
  simp only [upperJump_iff, not_forall] at hQ; obtain ⟨w₀, hvw₀, hlt⟩ := hQ
  have hw₀ := (upperRamificationGroup_antitone (G ⧸ H) C hvw₀.le).eq_of_not_lt hlt
  set w := min w₀ (herbrandFun (G ⧸ H) C x)
  have hvw : v < w := lt_min hvw₀ ((inverseHerbrandFun_lt_iff (G ⧸ H) C).1 hx)
  have hw : upperRamificationGroup (G ⧸ H) C w = upperRamificationGroup (G ⧸ H) C v :=
    le_antisymm (upperRamificationGroup_antitone (G ⧸ H) C hvw.le)
      (hw₀ ▸ upperRamificationGroup_antitone (G ⧸ H) C (min_le_left _ _))
  refine (upperRamificationGroup_antitone H B
    ((inverseHerbrandFun_le_iff (G ⧸ H) C).2 (min_le_right w₀ _))).trans_lt ?_
  rw [← subgroupOf_upperRamificationGroup_eq_upperRamificationGroup_inverseHerbrandFun A B G H,
    ← subgroupOf_upperRamificationGroup_eq_upperRamificationGroup_inverseHerbrandFun A B G H]
  refine lt_of_le_of_ne (Subgroup.comap_mono (upperRamificationGroup_antitone G B hvw.le))
    fun heq ↦ (QuotientGroup.strictMono_comap_prod_map H (hv w hvw)).ne (Prod.ext heq ?_)
  simpa only [← upperRamificationGroup_quotient_eq_map A B G] using hw
end Quotient

open _root_.IntermediateField
variable (A : Type*) {K L : Type*} [CommRing A] [Field K] [Field L] [Algebra A K] [Algebra K L]
  [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L] [IsGalois K L]
  [IsLocalRing A] [FaithfulSMul (L ≃ₐ[K] L) (integralClosure A L)]
  [IsDiscreteValuationRing (integralClosure A L)]
  [IsLocalHom (algebraMap A (integralClosure A L))]
  [Algebra.IsSeparable (ResidueField A) (ResidueField (integralClosure A L))]
/-- **Herbrand's theorem for Galois fixed fields**: `IsGalois.normalAutEquivQuotient H` maps
`(Gal(L/K)^v).map (QuotientGroup.mk' H)` onto `Gal(fixedField H / K)^v`. -/
@[simp] theorem map_normalAutEquivQuotient_map_mk'_upperRamificationGroup_integralClosure
    (H : Subgroup (L ≃ₐ[K] L)) [H.Normal] (v : ℝ) :
    ((upperRamificationGroup (L ≃ₐ[K] L) (integralClosure A L) v).map
        (QuotientGroup.mk' H)).map (IsGalois.normalAutEquivQuotient H : _ →* _) =
      upperRamificationGroup (fixedField H ≃ₐ[K] fixedField H)
        (integralClosure A (fixedField H)) v := by
  rw [← upperRamificationGroup_quotient_eq_map A (integralClosure A L) (L ≃ₐ[K] L) H v,
    upperRamificationGroup_fixedPoints_integralClosure_eq_comap A H v]
  exact Subgroup.map_comap_eq_self_of_surjective (IsGalois.normalAutEquivQuotient H).surjective _
variable (E : Type*) [Field E] [Algebra K E] [Algebra E L] [Algebra A E] [IsScalarTower A K E]
  [IsScalarTower K E L] [Normal K E]
/-- **Transitivity of `herbrandFun` in a field tower `L / E / K`** (`L / K` finite Galois, `E / K`
normal): `φ_{L/K}(u) = φ_{E/K}(φ_{L/E}(u))`. -/
theorem herbrandFun_integralClosure_tower (u : ℝ) :
    haveI := IsScalarTower.to₁₃₄ A K E L; haveI := isLocalRing_integralClosure_of_tower A E L
    herbrandFun (L ≃ₐ[K] L) (integralClosure A L) u =
      herbrandFun (E ≃ₐ[K] E) (integralClosure A E)
        (herbrandFun (L ≃ₐ[E] L) (integralClosure A L) u) := by
  let _ := IsScalarTower.to₁₃₄ A K E L; let _ := isLocalRing_integralClosure_of_tower A E L
  have := IsGalois.tower_bot_of_normal K E L
  rw [herbrandFun_tower A (integralClosure A L) (L ≃ₐ[K] L) (TauCeti.embeddingSubgroup K E L) u,
    ← herbrandFun_eq_of_smul_eq
      (φ := (TauCeti.algEquivEquivEmbeddingSubgroup K E L : (L ≃ₐ[E] L) →* _))
      (TauCeti.algEquivEquivEmbeddingSubgroup K E L).bijective
      (fun _ _ ↦ (TauCeti.algEquivEquivEmbeddingSubgroup_smul_integralClosure _ _).symm) u,
    herbrandFun_fixedPoints_integralClosure A (TauCeti.embeddingSubgroup K E L),
    (TauCeti.equivFixedFieldEmbeddingSubgroup K E L).herbrandFun_integralClosure_eq_of_algEquiv]
/-- **Transitivity of `inverseHerbrandFun` in a field tower `L / E / K`** (`L / K` finite Galois,
`E / K` normal): `ψ_{L/K}(v) = ψ_{L/E}(ψ_{E/K}(v))`. -/
theorem inverseHerbrandFun_integralClosure_tower (v : ℝ) :
    haveI := IsScalarTower.to₁₃₄ A K E L; haveI := isLocalRing_integralClosure_of_tower A E L
    inverseHerbrandFun (L ≃ₐ[K] L) (integralClosure A L) v =
      inverseHerbrandFun (L ≃ₐ[E] L) (integralClosure A L)
        (inverseHerbrandFun (E ≃ₐ[K] E) (integralClosure A E) v) := by
  let _ := IsScalarTower.to₁₃₄ A K E L; let _ := isLocalRing_integralClosure_of_tower A E L
  have _ := Module.Finite.left K E L; have _ := Module.Finite.right K E L
  rw [← herbrandFun_inj (L ≃ₐ[K] L) (integralClosure A L), herbrandFun_inverseHerbrandFun,
    herbrandFun_integralClosure_tower A E, herbrandFun_inverseHerbrandFun,
    herbrandFun_inverseHerbrandFun]
/-- **Upper filtration of `Gal(L/E)` in a field tower `L / E / K`**: pulling `Gal(L/K)^v` back along
`AlgEquiv.restrictScalarsHom K` gives `Gal(L/E)^{ψ_{E/K}(v)}`. -/
@[simp] theorem comap_restrictScalarsHom_upperRamificationGroup_integralClosure (v : ℝ) :
    haveI := IsScalarTower.to₁₃₄ A K E L; haveI := isLocalRing_integralClosure_of_tower A E L
    (upperRamificationGroup (L ≃ₐ[K] L) (integralClosure A L) v).comap
        (AlgEquiv.restrictScalarsHom (S := E) K) =
      upperRamificationGroup (L ≃ₐ[E] L) (integralClosure A L)
        (inverseHerbrandFun (E ≃ₐ[K] E) (integralClosure A E) v) := by
  let _ := IsScalarTower.to₁₃₄ A K E L; let _ := isLocalRing_integralClosure_of_tower A E L
  rw [upperRamificationGroup_def, upperRamificationGroup_def,
    inverseHerbrandFun_integralClosure_tower A E v, ramificationGroupReal_def,
    ramificationGroupReal_def]
  exact (ramificationGroup_eq_comap_of_smul_eq (e := AlgEquiv.restrictScalarsHom (S := E) K)
    (fun _ _ ↦ by simp) _).symm
/-- **Image of `Gal(L/E)^{ψ_{E/K}(v)}` in `Gal(L/K)`** in a field tower `L / E / K`. -/
theorem map_restrictScalarsHom_upperRamificationGroup_integralClosure (v : ℝ) :
    haveI := IsScalarTower.to₁₃₄ A K E L; haveI := isLocalRing_integralClosure_of_tower A E L
    (upperRamificationGroup (L ≃ₐ[E] L) (integralClosure A L)
        (inverseHerbrandFun (E ≃ₐ[K] E) (integralClosure A E) v)).map
        (AlgEquiv.restrictScalarsHom (S := E) K) =
      (AlgEquiv.restrictScalarsHom (S := E) K).range ⊓
        upperRamificationGroup (L ≃ₐ[K] L) (integralClosure A L) v := by
  let _ := IsScalarTower.to₁₃₄ A K E L; let _ := isLocalRing_integralClosure_of_tower A E L
  rw [← comap_restrictScalarsHom_upperRamificationGroup_integralClosure A E v,
    Subgroup.map_comap_eq]
/-- **Herbrand's theorem for normal subextensions** in a field tower `L / E / K` (`L / K` finite
Galois, `E / K` normal): `AlgEquiv.restrictNormalHom E` maps `Gal(L/K)^v` onto `Gal(E/K)^v`. -/
@[simp] theorem map_restrictNormalHom_upperRamificationGroup_integralClosure (v : ℝ) :
    haveI := IsScalarTower.to₁₃₄ A K E L; haveI := isLocalRing_integralClosure_of_tower A E L
    (upperRamificationGroup (L ≃ₐ[K] L) (integralClosure A L) v).map
        (AlgEquiv.restrictNormalHom E) =
      upperRamificationGroup (E ≃ₐ[K] E) (integralClosure A E) v := by
  let _ := IsScalarTower.to₁₃₄ A K E L; let _ := isLocalRing_integralClosure_of_tower A E L
  have := IsGalois.tower_bot_of_normal K E L
  let eK := TauCeti.equivFixedFieldEmbeddingSubgroup K E L
  apply Subgroup.map_injective (f := MonoidHom.ofClass eK.autCongr)
    (by simpa using eK.autCongr.injective)
  rw [Subgroup.map_map,
    TauCeti.autCongr_equivFixedFieldEmbeddingSubgroup_comp_restrictNormalHom K E L,
    ← Subgroup.map_map,
    map_normalAutEquivQuotient_map_mk'_upperRamificationGroup_integralClosure A _ v,
    eK.upperRamificationGroup_integralClosure_eq_comap_autCongr v,
    Subgroup.map_comap_eq_self_of_surjective (by simpa using eK.autCongr.surjective)]
/-- **Upper breaks in a field tower `L / E / K`** (`L / K` finite Galois, `E / K` normal):
`v` is an upper break of `Gal(L/K)` iff it is one of `Gal(E/K)` or `ψ_{E/K}(v)` is one of
`Gal(L/E)`. -/
theorem upperJump_integralClosure_tower_iff (v : ℝ) :
    haveI := IsScalarTower.to₁₃₄ A K E L; haveI := isLocalRing_integralClosure_of_tower A E L
    UpperJump (L ≃ₐ[K] L) (integralClosure A L) v ↔
      UpperJump (E ≃ₐ[K] E) (integralClosure A E) v ∨
        UpperJump (L ≃ₐ[E] L) (integralClosure A L)
          (inverseHerbrandFun (E ≃ₐ[K] E) (integralClosure A E) v) := by
  let _ := IsScalarTower.to₁₃₄ A K E L; let _ := isLocalRing_integralClosure_of_tower A E L
  have := IsGalois.tower_bot_of_normal K E L
  rw [upperJump_iff_upperJump_quotient_or_upperJump_inverseHerbrandFun A (integralClosure A L)
      (L ≃ₐ[K] L) (TauCeti.embeddingSubgroup K E L) v,
    upperJump_fixedPoints_integralClosure_iff A (TauCeti.embeddingSubgroup K E L),
    ← (TauCeti.equivFixedFieldEmbeddingSubgroup K E L).upperJump_integralClosure_iff_of_algEquiv,
    ← upperJump_iff_of_smul_eq (S := integralClosure A L)
      (φ := (TauCeti.algEquivEquivEmbeddingSubgroup K E L : (L ≃ₐ[E] L) →* _))
      (TauCeti.algEquivEquivEmbeddingSubgroup K E L).bijective
      (fun _ _ ↦ (TauCeti.algEquivEquivEmbeddingSubgroup_smul_integralClosure _ _).symm),
    inverseHerbrandFun_fixedPoints_integralClosure A (TauCeti.embeddingSubgroup K E L),
    (TauCeti.equivFixedFieldEmbeddingSubgroup K E
      L).inverseHerbrandFun_integralClosure_eq_of_algEquiv]

end TauCeti.IsLocalRing

namespace TauCeti

/-- If `integralClosure A L` is a DVR and `H ≤ Gal(L/K)`, then
`integralClosure A (fixedField H)` is a DVR. -/
instance instIsDiscreteValuationRingIntegralClosureFixedField {A K L : Type*} [CommRing A]
    [Field K] [Field L] [Algebra A K] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [_root_.IsDiscreteValuationRing (integralClosure A L)] {H : Subgroup (L ≃ₐ[K] L)} :
    _root_.IsDiscreteValuationRing (integralClosure A (IntermediateField.fixedField H)) :=
  have : Algebra.IsIntegral (FixedPoints.subalgebra A (integralClosure A L) H)
      (integralClosure A L) := Algebra.IsIntegral.tower_top A
  have := isDiscreteValuationRing_fixedPoints_subalgebra_of_isIntegral
    (A := A) (B := integralClosure A L) (G := H)
  _root_.IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
    (fixedPointsSubalgebraIntegralClosureEquiv A H)

end TauCeti
