/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DiscreteValuationRing.LowerIndex
public import TauCeti.RingTheory.IntegralClosure.Map
public import TauCeti.RingTheory.IsGaloisGroup.IntegralClosure
public import TauCeti.RingTheory.LocalRing.Herbrand
import TauCeti.FieldTheory.Galois.Restriction

/-!
# Herbrand's theorem and transitivity of Herbrand functions on discrete valuation rings

Let a finite group `G` act faithfully on a discrete valuation ring `B` over a local ring `A` with
separable residue extension `ResidueField B / ResidueField A` (which holds whenever `ResidueField A`
is perfect and `ResidueField B / ResidueField A` is algebraic, e.g. when `B` is integral over `A`,
such as `A = B^G`). No completeness or finiteness of the residue field is required. From Serre's
lower-index quotient formula we deduce Herbrand's lemma
(`ramificationGroupReal_quotient_herbrandFun`), transitivity of the Herbrand functions
(`herbrandFun_tower`, `inverseHerbrandFun_tower`, `herbrandOrderIso_tower`, `psiNat_tower`),
Herbrand's theorem (`upperRamificationGroup_quotient_eq_map`), the upper filtration and break
decomposition in a tower, and Galois fixed-field and subextension transport on integral closures.
The quotient, transitivity, and upper-break arguments adapt
`TauCeti/NumberTheory/LocalField/Herbrand/Quotient.lean`,
`TauCeti/NumberTheory/LocalField/Herbrand/Tower.lean`, and
`TauCeti/NumberTheory/LocalField/Herbrand/UpperQuotient.lean`.

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
  [Algebra.IsSeparable (ResidueField A) (ResidueField B)]

/-- **Serre's lemma on the lower index of a quotient.** If `g` has maximal lower index in `g H` and
`i_G(g) = j` is finite, then `φ_H(j - 1) = i_{G ⧸ H}(g H) - 1`. -/
theorem herbrandFun_lowerIndex_sub_one (H : Subgroup G) [H.Normal] (g : G) {j : ℕ}
    (hj : lowerIndex B g = j) (hg : ∀ h : H, lowerIndex B (g * h) ≤ lowerIndex B g) :
    herbrandFun H B ((j : ℝ) - 1) =
      ((lowerIndex (FixedPoints.subalgebra A B H) (QuotientGroup.mk' H g)).toNat : ℝ) - 1 := by
  have hsum := ramificationIdx_mul_lowerIndex_quotient_mk'_eq_sum_card A B G H g hj hg
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1
    (lowerIndex_quotient_mk'_ne_top A B G H g (hj ▸ ENat.natCast_ne_top j) hg)
  rw [← hn, ← Nat.cast_mul, ← Nat.cast_sum, Nat.cast_inj,
    ← natCard_ramificationGroup_zero_fixedPoints A B G H] at hsum
  rw [← hn, ENat.toNat_natCast]
  have h0 : (Nat.card (ramificationGroup H B 0) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  rcases j with _ | m
  · rw [herbrandFun_eq_self_of_mem_Icc H B (by norm_num) (by norm_num)]
    simp only [Finset.range_zero, Finset.sum_empty, mul_eq_zero, Nat.card_pos.ne', false_or] at hsum
    simp [hsum]
  · rw [(by push_cast; ring : ((m + 1 : ℕ) : ℝ) - 1 = m), herbrandFun_natCast, div_eq_iff h0]
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (Nat.add_one_pos m), Nat.cast_zero,
      zero_add, Finset.Ico_add_one_right_eq_Icc] at hsum
    have hsumR : (Nat.card (ramificationGroup H B 0) : ℝ) * n = Nat.card (ramificationGroup H B 0) +
        ∑ i ∈ Finset.Icc 1 m, (Nat.card (ramificationGroup H B i) : ℝ) := by exact_mod_cast hsum
    linear_combination -hsumR

private theorem quotient_mk_mem_ramificationGroupReal_herbrandFun_iff (H : Subgroup G) [H.Normal]
    (g : G) (hg : ∀ h : H, lowerIndex B (g * h) ≤ lowerIndex B g) (u : ℝ) :
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

/-- **Herbrand's lemma.** For a normal subgroup `H ≤ G`, the lower ramification group of `G ⧸ H`
acting on `FixedPoints.subalgebra A B H` at `φ_H(u)` is `(G_u).map (QuotientGroup.mk' H)`. -/
@[simp] theorem ramificationGroupReal_quotient_herbrandFun (H : Subgroup G) [H.Normal] (u : ℝ) :
    ramificationGroupReal (G ⧸ H) (FixedPoints.subalgebra A B H) (herbrandFun H B u) =
      (ramificationGroupReal G B u).map (QuotientGroup.mk' H) := by
  have hmk (g : G) (h : H) : QuotientGroup.mk' H (g * h) = QuotientGroup.mk' H g := by
    rw [map_mul, QuotientGroup.mk'_apply H (h : G), (QuotientGroup.eq_one_iff _).2 h.2, mul_one]
  ext q; rw [Subgroup.mem_map]; refine ⟨fun hq ↦ ?_, ?_⟩
  · obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective H q
    obtain ⟨h₀, hh₀⟩ := exists_forall_lowerIndex_mul_le B H g
    exact ⟨g * h₀, (quotient_mk_mem_ramificationGroupReal_herbrandFun_iff A B G H (g * h₀)
      hh₀ u).1 (hmk g h₀ ▸ hq), hmk g h₀⟩
  · rintro ⟨g, hg, rfl⟩; obtain ⟨h₀, hh₀⟩ := exists_forall_lowerIndex_mul_le B H g
    rw [← hmk g h₀, quotient_mk_mem_ramificationGroupReal_herbrandFun_iff A B G H (g * h₀) hh₀]
    rw [ramificationGroupReal_def, mem_ramificationGroup_iff_le_lowerIndex] at hg ⊢
    exact hg.trans (by simpa [mul_inv_cancel_right] using hh₀ h₀⁻¹)

theorem ramificationGroupReal_quotient_eq_map_inverseHerbrandFun (H : Subgroup G) [H.Normal]
    (v : ℝ) : ramificationGroupReal (G ⧸ H) (FixedPoints.subalgebra A B H) v =
      (ramificationGroupReal G B (inverseHerbrandFun H B v)).map (QuotientGroup.mk' H) := by
  rw [← ramificationGroupReal_quotient_herbrandFun A B G, herbrandFun_inverseHerbrandFun]

/-- **Herbrand's lemma in counting form**: `#(G ⧸ H)_{φ_H(u)} · #H_u = #G_u`. -/
theorem natCard_ramificationGroupReal_quotient_herbrandFun_mul (H : Subgroup G) [H.Normal] (u : ℝ) :
    Nat.card (ramificationGroupReal (G ⧸ H) (FixedPoints.subalgebra A B H) (herbrandFun H B u)) *
        Nat.card (ramificationGroupReal H B u) = Nat.card (ramificationGroupReal G B u) := by
  rw [ramificationGroupReal_quotient_herbrandFun, ← MonoidHom.domRestrict_range]
  have hker : ((QuotientGroup.mk' H).domRestrict (ramificationGroupReal G B u)).ker =
      H.subgroupOf (ramificationGroupReal G B u) := by
    ext x; simp [Subgroup.mem_subgroupOf]
  have hcard : Nat.card (H.subgroupOf (ramificationGroupReal G B u)) =
      Nat.card (ramificationGroupReal H B u) := by
    rw [← subgroupOf_ramificationGroupReal G B H u, ← Subgroup.card_subtype,
      ← Subgroup.card_subtype, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      inf_comm]
  rw [← hcard, ← hker, mul_comm]; exact Subgroup.card_ker_mul_card_range _

private theorem natCard_ramificationGroup_quotient_zero_mul (H : Subgroup G) [H.Normal] :
    Nat.card (ramificationGroup (G ⧸ H) (FixedPoints.subalgebra A B H) 0) *
        Nat.card (ramificationGroup H B 0) = Nat.card (ramificationGroup G B 0) := by
  have h := natCard_ramificationGroupReal_quotient_herbrandFun_mul A B G H 0
  rwa [herbrandFun_zero, ← Int.cast_zero, ramificationGroupReal_intCast,
    ramificationGroupReal_intCast, ramificationGroupReal_intCast] at h

private theorem herbrandFun_tower_step (H : Subgroup G) [H.Normal] (m : ℕ) {u : ℝ}
    (h₁ : (m : ℝ) ≤ u) (h₂ : u ≤ m + 1) (hm : herbrandFun G B m =
      herbrandFun (G ⧸ H) (FixedPoints.subalgebra A B H) (herbrandFun H B m)) :
    herbrandFun G B u =
      herbrandFun (G ⧸ H) (FixedPoints.subalgebra A B H) (herbrandFun H B u) := by
  set C := FixedPoints.subalgebra A B H
  have hsubG := herbrandFun_sub_of_forall_eq G B h₁ fun _ ↦ ramificationGroupReal_eq_of_mem_Ioc h₂
  have hsubH := herbrandFun_sub_of_forall_eq H B h₁ fun _ ↦ ramificationGroupReal_eq_of_mem_Ioc h₂
  have hsubQ := herbrandFun_sub_of_forall_eq (G ⧸ H) C
    ((herbrandFun_le_herbrandFun_iff H B).2 h₁)
    (H := ramificationGroupReal (G ⧸ H) C (herbrandFun H B u)) fun t ht₁ ht₂ ↦ by
      rw [ramificationGroupReal_quotient_eq_map_inverseHerbrandFun,
        ramificationGroupReal_quotient_herbrandFun,
        ramificationGroupReal_eq_of_mem_Ioc h₂ ((lt_inverseHerbrandFun_iff H B).2 ht₁)
          ((inverseHerbrandFun_le_iff H B).2 ht₂)]
  have hslope : (Nat.card (ramificationGroupReal G B u) : ℝ) / Nat.card (ramificationGroup G B 0) =
      (Nat.card (ramificationGroupReal H B u) / Nat.card (ramificationGroup H B 0)) *
        (Nat.card (ramificationGroupReal (G ⧸ H) C (herbrandFun H B u)) /
          Nat.card (ramificationGroup (G ⧸ H) C 0)) := by
    rw [div_mul_div_comm, mul_comm (Nat.card (ramificationGroupReal H B u) : ℝ),
      mul_comm (Nat.card (ramificationGroup H B 0) : ℝ)]; congr 1
    · exact_mod_cast (natCard_ramificationGroupReal_quotient_herbrandFun_mul A B G H u).symm
    · exact_mod_cast (natCard_ramificationGroup_quotient_zero_mul A B G H).symm
  rw [hslope] at hsubG; rw [hsubH] at hsubQ; linear_combination hsubG - hsubQ + hm

private theorem herbrandFun_tower_of_mem_Icc (H : Subgroup G) [H.Normal] (m : ℕ) :
    ∀ {u : ℝ}, (m : ℝ) ≤ u → u ≤ m + 1 → herbrandFun G B u =
      herbrandFun (G ⧸ H) (FixedPoints.subalgebra A B H) (herbrandFun H B u) := by
  induction m with
  | zero => exact fun h₁ h₂ ↦ herbrandFun_tower_step A B G H 0 h₁ h₂ (by simp)
  | succ k ih =>
    exact fun h₁ h₂ ↦ herbrandFun_tower_step A B G H (k + 1) h₁ h₂
      (ih (by push_cast; linarith) (by push_cast; linarith))

/-- **Transitivity of the Herbrand function** for a normal subgroup `H ≤ G`:
`φ_G(u) = φ_{G ⧸ H}(φ_H(u))` for every real `u`. -/
theorem herbrandFun_tower (H : Subgroup G) [H.Normal] (u : ℝ) :
    herbrandFun G B u =
      herbrandFun (G ⧸ H) (FixedPoints.subalgebra A B H) (herbrandFun H B u) := by
  set C := FixedPoints.subalgebra A B H
  rcases lt_trichotomy u (-1) with hu | rfl | hu
  · rw [herbrandFun_of_le_neg_one G B hu.le,
      herbrandFun_of_le_neg_one (G ⧸ H) C ((herbrandFun_le_neg_one_iff H B).2 hu.le),
      herbrandFun_of_le_neg_one H B hu.le]
    have hslope : (Nat.card G : ℝ) / Nat.card (ramificationGroup G B 0) =
        (Nat.card H / Nat.card (ramificationGroup H B 0)) *
          (Nat.card (G ⧸ H) / Nat.card (ramificationGroup (G ⧸ H) C 0)) := by
      rw [div_mul_div_comm, mul_comm (Nat.card H : ℝ),
        mul_comm (Nat.card (ramificationGroup H B 0) : ℝ)]; congr 1
      · rw [mul_comm, ← H.index_eq_card]; exact_mod_cast H.card_mul_index.symm
      · exact_mod_cast (natCard_ramificationGroup_quotient_zero_mul A B G H).symm
    rw [hslope]; ring
  · simp
  · rcases le_or_gt u 0 with hu0 | hu0
    · rw [herbrandFun_eq_self_of_mem_Icc H B hu.le hu0,
        herbrandFun_eq_self_of_mem_Icc (G ⧸ H) C hu.le hu0,
        herbrandFun_eq_self_of_mem_Icc G B hu.le hu0]
    · exact herbrandFun_tower_of_mem_Icc A B G H ⌊u⌋₊ (Nat.floor_le hu0.le)
        (Nat.lt_floor_add_one u).le

/-- **Transitivity of the inverse Herbrand function**: `ψ_G(v) = ψ_H(ψ_{G ⧸ H}(v))`. -/
theorem inverseHerbrandFun_tower (H : Subgroup G) [H.Normal] (v : ℝ) :
    inverseHerbrandFun G B v =
      inverseHerbrandFun H B (inverseHerbrandFun (G ⧸ H) (FixedPoints.subalgebra A B H) v) := by
  rw [← herbrandFun_inj G B, herbrandFun_inverseHerbrandFun, herbrandFun_tower A B G H,
    herbrandFun_inverseHerbrandFun, herbrandFun_inverseHerbrandFun]

/-- **Transitivity of the bundled Herbrand order isomorphisms** on `[-1, ∞)`. -/
theorem herbrandOrderIso_tower (H : Subgroup G) [H.Normal] :
    herbrandOrderIso G B =
      (herbrandOrderIso H B).trans (herbrandOrderIso (G ⧸ H) (FixedPoints.subalgebra A B H)) :=
  OrderIso.ext <| funext fun u ↦ Subtype.ext <| by
    simp only [OrderIso.trans_apply, coe_herbrandOrderIso_apply]; exact herbrandFun_tower A B G H u

/-- **Transitivity of the integral inverse Herbrand function**: `ψℕ_G = ψℕ_H ∘ ψℕ_{G ⧸ H}`. -/
theorem psiNat_tower (H : Subgroup G) [H.Normal] :
    psiNat G B = psiNat H B ∘ psiNat (G ⧸ H) (FixedPoints.subalgebra A B H) :=
  funext fun n ↦ Nat.cast_injective (R := ℝ) <| by
    rw [Function.comp_apply, coe_psiNat, coe_psiNat, coe_psiNat, inverseHerbrandFun_tower A B G H]

/-- **Herbrand's theorem**: `(G ⧸ H)^v = (G^v).map (QuotientGroup.mk' H)` for normal `H ≤ G`. -/
@[simp] theorem upperRamificationGroup_quotient_eq_map (H : Subgroup G) [H.Normal] (v : ℝ) :
    upperRamificationGroup (G ⧸ H) (FixedPoints.subalgebra A B H) v =
      (upperRamificationGroup G B v).map (QuotientGroup.mk' H) := by
  rw [upperRamificationGroup_def, upperRamificationGroup_def, inverseHerbrandFun_tower A B G H,
    ramificationGroupReal_quotient_eq_map_inverseHerbrandFun]

/-- **Upper filtration of a normal subgroup**: `H ∩ G^v = H^{ψ_{G ⧸ H}(v)}`. -/
theorem subgroupOf_upperRamificationGroup_eq_upperRamificationGroup_inverseHerbrandFun
    (H : Subgroup G) [H.Normal] (v : ℝ) :
    (upperRamificationGroup G B v).subgroupOf H =
      upperRamificationGroup H B (inverseHerbrandFun (G ⧸ H) (FixedPoints.subalgebra A B H) v) := by
  rw [subgroupOf_upperRamificationGroup, inverseHerbrandFun_tower A B G H,
    herbrandFun_inverseHerbrandFun]

variable {A B G} in
theorem UpperJump.of_quotient {H : Subgroup G} [H.Normal] {v : ℝ}
    (hv : UpperJump (G ⧸ H) (FixedPoints.subalgebra A B H) v) : UpperJump G B v :=
  (upperJump_iff G B v).2 fun w hvw ↦
    lt_of_le_of_ne (upperRamificationGroup_antitone G B hvw.le) fun heq ↦
      ((upperJump_iff _ _ v).1 hv w hvw).ne <| by
        rw [upperRamificationGroup_quotient_eq_map, heq,
          ← upperRamificationGroup_quotient_eq_map A B G]

variable {A B G} in
theorem UpperJump.of_inverseHerbrandFun {H : Subgroup G} [H.Normal] {v : ℝ}
    (hv : UpperJump H B (inverseHerbrandFun (G ⧸ H) (FixedPoints.subalgebra A B H) v)) :
    UpperJump G B v :=
  (upperJump_iff G B v).2 fun w hvw ↦
    lt_of_le_of_ne (upperRamificationGroup_antitone G B hvw.le) fun heq ↦ by
      have hlt := (upperJump_iff H B _).1 hv _
        (inverseHerbrandFun_strictMono (G ⧸ H) (FixedPoints.subalgebra A B H) hvw)
      rw [← subgroupOf_upperRamificationGroup_eq_upperRamificationGroup_inverseHerbrandFun A B G H,
        ← subgroupOf_upperRamificationGroup_eq_upperRamificationGroup_inverseHerbrandFun A B G H,
        heq] at hlt; exact hlt.ne rfl

/-- **Upper breaks in a quotient tower**: `v` is an upper break of `G` if and only if `v` is an
upper break of `G ⧸ H` on `B^H` or `ψ_{G ⧸ H}(v)` is an upper break of `H` on `B`. -/
theorem upperJump_iff_upperJump_quotient_or_upperJump_inverseHerbrandFun
    (H : Subgroup G) [H.Normal] (v : ℝ) :
    UpperJump G B v ↔ UpperJump (G ⧸ H) (FixedPoints.subalgebra A B H) v ∨
      UpperJump H B (inverseHerbrandFun (G ⧸ H) (FixedPoints.subalgebra A B H) v) := by
  let C := FixedPoints.subalgebra A B H
  refine ⟨fun hv ↦ or_iff_not_imp_left.2 fun hQ ↦ (upperJump_iff H B _).2 fun x hx ↦ ?_,
    fun h ↦ h.elim UpperJump.of_quotient UpperJump.of_inverseHerbrandFun⟩
  simp only [upperJump_iff, not_forall] at hQ; obtain ⟨w₀, hvw₀, hlt⟩ := hQ
  have hw₀ : upperRamificationGroup (G ⧸ H) C w₀ = upperRamificationGroup (G ⧸ H) C v :=
    (upperRamificationGroup_antitone (G ⧸ H) C hvw₀.le).eq_of_not_lt hlt
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
    fun heq ↦ (QuotientGroup.strictMono_comap_prod_map H
      ((upperJump_iff G B v).1 hv w hvw)).ne (Prod.ext heq ?_)
  dsimp only
  rw [← upperRamificationGroup_quotient_eq_map A B G, hw, upperRamificationGroup_quotient_eq_map]

end Quotient

section IntegralClosureFixedField

open _root_.IntermediateField

variable (A : Type*) {K L : Type*} [CommRing A] [Field K] [Field L] [Algebra A K] [Algebra K L]
  [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L] [IsGalois K L]

/-- `IsGalois.normalAutEquivQuotient H` pulls back lower ramification groups from
`integralClosure A (fixedField H)` to `FixedPoints.subalgebra A (integralClosure A L) H`. -/
theorem ramificationGroup_fixedPoints_integralClosure_eq_comap [IsLocalRing (integralClosure A L)]
    (H : Subgroup (L ≃ₐ[K] L)) [H.Normal] (i : ℤ) :
    ramificationGroup ((L ≃ₐ[K] L) ⧸ H) (FixedPoints.subalgebra A (integralClosure A L) H) i =
      (ramificationGroup (fixedField H ≃ₐ[K] fixedField H)
        (integralClosure A (fixedField H)) i).comap (IsGalois.normalAutEquivQuotient H : _ →* _) :=
  ramificationGroup_eq_comap_of_ringEquiv
    (e := (TauCeti.fixedPointsSubalgebraIntegralClosureEquiv A H).toRingEquiv)
    (TauCeti.fixedPointsSubalgebraIntegralClosureEquiv_smul A H) i

theorem herbrandFun_fixedPoints_integralClosure [IsLocalRing (integralClosure A L)]
    (H : Subgroup (L ≃ₐ[K] L)) [H.Normal] (u : ℝ) :
    herbrandFun ((L ≃ₐ[K] L) ⧸ H) (FixedPoints.subalgebra A (integralClosure A L) H) u =
      herbrandFun (fixedField H ≃ₐ[K] fixedField H) (integralClosure A (fixedField H)) u :=
  herbrandFun_eq_of_ramificationGroup_eq_comap (IsGalois.normalAutEquivQuotient H).bijective
    (ramificationGroup_fixedPoints_integralClosure_eq_comap A H) u

theorem inverseHerbrandFun_fixedPoints_integralClosure [IsLocalRing (integralClosure A L)]
    (H : Subgroup (L ≃ₐ[K] L)) [H.Normal] (v : ℝ) :
    inverseHerbrandFun ((L ≃ₐ[K] L) ⧸ H) (FixedPoints.subalgebra A (integralClosure A L) H) v =
      inverseHerbrandFun (fixedField H ≃ₐ[K] fixedField H) (integralClosure A (fixedField H)) v :=
  inverseHerbrandFun_eq_of_ramificationGroup_eq_comap (IsGalois.normalAutEquivQuotient H).bijective
    (ramificationGroup_fixedPoints_integralClosure_eq_comap A H) v

omit [IsGalois K L] in
private theorem faithfulSMul_integralClosure [IsFractionRing A K] :
    FaithfulSMul (L ≃ₐ[K] L) (integralClosure A L) := by
  have _ : IsDomain A := (IsFractionRing.injective A K).isDomain _
  have _ := integralClosure.isFractionRing_of_finite_extension (A := A) K L
  exact ⟨fun h ↦ eq_of_smul_eq_smul fun y : L ↦ by
    obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (integralClosure A L) y
    simp only [smul_div₀', ← algebraMap.coe_smul', h]⟩

/-- **Herbrand's theorem for Galois fixed fields.** For a finite Galois extension `L / K` over the
fraction field `K` of a local domain `A` such that `integralClosure A L` is a DVR lying locally over
`A` with separable residue extension, and a normal subgroup `H ≤ Gal(L/K)`,
`IsGalois.normalAutEquivQuotient H` maps `(Gal(L/K)^v).map (QuotientGroup.mk' H)` onto
`Gal(L^H / K)^v`. -/
@[simp] theorem map_normalAutEquivQuotient_upperRamificationGroup [IsLocalRing A]
    [IsFractionRing A K] [IsDiscreteValuationRing (integralClosure A L)]
    [IsLocalHom (algebraMap A (integralClosure A L))]
    [Algebra.IsSeparable (ResidueField A) (ResidueField (integralClosure A L))]
    (H : Subgroup (L ≃ₐ[K] L)) [H.Normal] (v : ℝ) :
    ((upperRamificationGroup (L ≃ₐ[K] L) (integralClosure A L) v).map
        (QuotientGroup.mk' H)).map (IsGalois.normalAutEquivQuotient H : _ →* _) =
      upperRamificationGroup (fixedField H ≃ₐ[K] fixedField H)
        (integralClosure A (fixedField H)) v := by
  have _ := faithfulSMul_integralClosure (K := K) (L := L) A
  rw [← upperRamificationGroup_quotient_eq_map A (integralClosure A L) (L ≃ₐ[K] L) H v,
    upperRamificationGroup_eq_comap_of_ramificationGroup_eq_comap
      (IsGalois.normalAutEquivQuotient H).bijective
      (ramificationGroup_fixedPoints_integralClosure_eq_comap A H) v]
  exact Subgroup.map_comap_eq_self_of_surjective (IsGalois.normalAutEquivQuotient H).surjective _

section Tower

variable (E : Type*) [Field E] [Algebra K E] [Algebra E L] [Algebra A E] [IsScalarTower A K E]
  [IsScalarTower K E L] [IsScalarTower A E L] [IsGalois K E] [IsLocalRing A] [IsFractionRing A K]
  [IsDiscreteValuationRing (integralClosure A L)] [IsLocalHom (algebraMap A (integralClosure A L))]
  [Algebra.IsSeparable (ResidueField A) (ResidueField (integralClosure A L))]

/-- **Transitivity of `herbrandFun` in a Galois field tower.** For a finite Galois tower `K / E / L`
over the fraction field `K` of a local domain `A` such that `integralClosure A L` is a DVR lying
locally over `A` with separable residue extension, `φ_{L/K}(u) = φ_{E/K}(φ_{L/E}(u))`. -/
theorem herbrandFun_integralClosure_tower (u : ℝ) :
    haveI := TauCeti.isLocalRing_integralClosure_of_injective
      (f := IsScalarTower.toAlgHom A E L) fun _ _ h ↦ (algebraMap E L).injective h
    herbrandFun (L ≃ₐ[K] L) (integralClosure A L) u =
      herbrandFun (E ≃ₐ[K] E) (integralClosure A E)
        (herbrandFun (L ≃ₐ[E] L) (integralClosure A L) u) := by
  let _ := TauCeti.isLocalRing_integralClosure_of_injective
    (f := IsScalarTower.toAlgHom A E L) fun _ _ h ↦ (algebraMap E L).injective h
  have _ := faithfulSMul_integralClosure (K := K) (L := L) A
  let ι := IsScalarTower.toAlgHom K E L; let H := ι.fieldRange.fixingSubgroup
  have _ : IsGalois K ι.fieldRange := IsGalois.of_algEquiv ι.equivFieldRange
  let eK := ι.equivFieldRange.trans (equivOfEq (IsGalois.fixedField_fixingSubgroup _).symm)
  have hrng : (AlgEquiv.restrictScalarsHom (S := E) K).range = H := by
    rw [AlgEquiv.range_restrictScalarsHom_eq_ker_restrictNormalHom K E L,
      ← AlgHom.restrictNormalHom_toAlgHom (F := K), AlgHom.ker_restrictNormalHom]
  let φH : (L ≃ₐ[E] L) ≃* H :=
    (MulEquiv.ofBijective (AlgEquiv.restrictScalarsHom (S := E) K).rangeRestrict
      ⟨fun _ _ h ↦ AlgEquiv.restrictScalarsHom_injective K (congrArg Subtype.val h),
        MonoidHom.rangeRestrict_surjective _⟩).trans (MulEquiv.subgroupCongr hrng)
  rw [herbrandFun_tower A (integralClosure A L) (L ≃ₐ[K] L) H u,
    ← herbrandFun_eq_of_smul_eq (φ := (φH : (L ≃ₐ[E] L) →* H)) φH.bijective (fun _ _ ↦ rfl) u,
    herbrandFun_fixedPoints_integralClosure A H, herbrandFun_integralClosure_eq_of_algEquiv eK]

/-- **Transitivity of `inverseHerbrandFun` in a Galois field tower.** Under the hypotheses of
`herbrandFun_integralClosure_tower`, `ψ_{L/K}(v) = ψ_{L/E}(ψ_{E/K}(v))`. -/
theorem inverseHerbrandFun_integralClosure_tower (v : ℝ) :
    haveI := TauCeti.isLocalRing_integralClosure_of_injective
      (f := IsScalarTower.toAlgHom A E L) fun _ _ h ↦ (algebraMap E L).injective h
    inverseHerbrandFun (L ≃ₐ[K] L) (integralClosure A L) v =
      inverseHerbrandFun (L ≃ₐ[E] L) (integralClosure A L)
        (inverseHerbrandFun (E ≃ₐ[K] E) (integralClosure A E) v) := by
  let _ := TauCeti.isLocalRing_integralClosure_of_injective
    (f := IsScalarTower.toAlgHom A E L) fun _ _ h ↦ (algebraMap E L).injective h
  have _ : FiniteDimensional K E := Module.Finite.left K E L
  have _ : FiniteDimensional E L := Module.Finite.right K E L
  rw [← herbrandFun_inj (L ≃ₐ[K] L) (integralClosure A L), herbrandFun_inverseHerbrandFun,
    herbrandFun_integralClosure_tower A E, herbrandFun_inverseHerbrandFun,
    herbrandFun_inverseHerbrandFun]

/-- **Upper filtration of `Gal(L/E)` in a Galois field tower.** Under the hypotheses of
`herbrandFun_integralClosure_tower`, pulling `Gal(L/K)^v` back along restriction of scalars gives
`Gal(L/E)^{ψ_{E/K}(v)}`. -/
@[simp] theorem comap_restrictScalarsHom_upperRamificationGroup_integralClosure (v : ℝ) :
    haveI := TauCeti.isLocalRing_integralClosure_of_injective
      (f := IsScalarTower.toAlgHom A E L) fun _ _ h ↦ (algebraMap E L).injective h
    (upperRamificationGroup (L ≃ₐ[K] L) (integralClosure A L) v).comap
        (AlgEquiv.restrictScalarsHom (S := E) K) =
      upperRamificationGroup (L ≃ₐ[E] L) (integralClosure A L)
        (inverseHerbrandFun (E ≃ₐ[K] E) (integralClosure A E) v) := by
  let _ := TauCeti.isLocalRing_integralClosure_of_injective
    (f := IsScalarTower.toAlgHom A E L) fun _ _ h ↦ (algebraMap E L).injective h
  rw [upperRamificationGroup_def, upperRamificationGroup_def,
    inverseHerbrandFun_integralClosure_tower A E v, ramificationGroupReal_def,
    ramificationGroupReal_def]
  exact (ramificationGroup_eq_comap_of_smul_eq (e := AlgEquiv.restrictScalarsHom (S := E) K)
    (fun _ _ ↦ rfl) _).symm

theorem map_restrictScalarsHom_upperRamificationGroup_integralClosure (v : ℝ) :
    haveI := TauCeti.isLocalRing_integralClosure_of_injective
      (f := IsScalarTower.toAlgHom A E L) fun _ _ h ↦ (algebraMap E L).injective h
    (upperRamificationGroup (L ≃ₐ[E] L) (integralClosure A L)
        (inverseHerbrandFun (E ≃ₐ[K] E) (integralClosure A E) v)).map
        (AlgEquiv.restrictScalarsHom (S := E) K) =
      (AlgEquiv.restrictScalarsHom (S := E) K).range ⊓
        upperRamificationGroup (L ≃ₐ[K] L) (integralClosure A L) v := by
  let _ := TauCeti.isLocalRing_integralClosure_of_injective
    (f := IsScalarTower.toAlgHom A E L) fun _ _ h ↦ (algebraMap E L).injective h
  rw [← comap_restrictScalarsHom_upperRamificationGroup_integralClosure A E v,
    Subgroup.map_comap_eq]

omit [IsScalarTower A E L] in
/-- **Herbrand's theorem for Galois subextensions.** For a finite Galois tower `K / E / L` over the
fraction field `K` of a local domain `A` such that `integralClosure A L` is a DVR lying locally over
`A` with separable residue extension, restriction `Gal(L/K) →* Gal(E/K)` maps `Gal(L/K)^v` onto
`Gal(E/K)^v`. -/
@[simp] theorem map_restrictNormalHom_upperRamificationGroup_integralClosure (v : ℝ) :
    haveI := TauCeti.isLocalRing_integralClosure_of_injective
      (f := (IsScalarTower.toAlgHom K E L).restrictScalars A)
      fun _ _ h ↦ (algebraMap E L).injective h
    (upperRamificationGroup (L ≃ₐ[K] L) (integralClosure A L) v).map
        (AlgEquiv.restrictNormalHom E) =
      upperRamificationGroup (E ≃ₐ[K] E) (integralClosure A E) v := by
  let _ := TauCeti.isLocalRing_integralClosure_of_injective
    (f := (IsScalarTower.toAlgHom K E L).restrictScalars A)
    fun _ _ h ↦ (algebraMap E L).injective h
  let ι := IsScalarTower.toAlgHom K E L; let H := ι.fieldRange.fixingSubgroup
  have _ : IsGalois K ι.fieldRange := IsGalois.of_algEquiv ι.equivFieldRange
  let eK := ι.equivFieldRange.trans (equivOfEq (IsGalois.fixedField_fixingSubgroup _).symm)
  have heK (x : E) : ((eK x : fixedField H) : L) = algebraMap E L x := by simp [eK, ι]
  have hcomp :
      MonoidHom.comp (eK.autCongr : (E ≃ₐ[K] E) →* (fixedField H ≃ₐ[K] fixedField H))
        (AlgEquiv.restrictNormalHom E) =
      MonoidHom.comp (IsGalois.normalAutEquivQuotient H) (QuotientGroup.mk' H) := by
    ext σ y
    simp only [MonoidHom.comp_apply, MonoidHom.coe_ofClass, QuotientGroup.mk'_apply,
      IsGalois.normalAutEquivQuotient_apply, AlgEquiv.autCongr_apply, AlgEquiv.trans_apply, heK,
      AlgEquiv.restrictNormalHom_apply_eq_restrictNormal, AlgEquiv.restrictNormal_commutes]
    rw [← heK, eK.apply_symm_apply]; exact (σ.restrictNormal_commutes _ y).symm
  apply Subgroup.map_injective
    (f := (eK.autCongr : (E ≃ₐ[K] E) →* (fixedField H ≃ₐ[K] fixedField H))) eK.autCongr.injective
  rw [Subgroup.map_map, hcomp, ← Subgroup.map_map,
    map_normalAutEquivQuotient_upperRamificationGroup A H v,
    upperRamificationGroup_integralClosure_eq_comap_autCongr eK v,
    Subgroup.map_comap_eq_self_of_surjective eK.autCongr.surjective]

end Tower

end IntegralClosureFixedField

end TauCeti.IsLocalRing
