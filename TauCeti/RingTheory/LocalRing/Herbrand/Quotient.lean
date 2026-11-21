/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import TauCeti.RingTheory.DiscreteValuationRing.Invariant
public import TauCeti.RingTheory.LocalRing.Herbrand.Basic
import TauCeti.RingTheory.DiscreteValuationRing.LowerIndex
import TauCeti.RingTheory.IsGaloisGroup.IntegralClosure

/-!
# Herbrand's theorem, transitivity, and quotient compatibility of the upper numbering

Let a finite group `G` act faithfully by `A`-algebra automorphisms on a discrete valuation ring `B`
with invariant ring a discrete valuation ring `A` and separable residue extension
`ResidueField A → ResidueField B`. For any normal subgroup `H` of `G`, the fixed subalgebra
`C = FixedPoints.subalgebra A B H` is automatically a discrete valuation ring
(`TauCeti.FixedPoints.isDiscreteValuationRing_subalgebra`) on which `G ⧸ H` acts faithfully with
invariant ring `A`.

Under these hypotheses — without assuming completeness of `A` or finiteness of the residue field —
this file proves **Herbrand's theorem** on the lower and upper filtrations and **transitivity of
the Herbrand functions** from the lower-index quotient formulas in
`TauCeti/RingTheory/DiscreteValuationRing/LowerIndex.lean`:

* `(G/H)_{φ_H(u)} = G_u H / H` for every `u : ℝ`;
* `φ_G(u) = φ_{G/H}(φ_H(u))` and `ψ_G(v) = ψ_H(ψ_{G/H}(v))` for every `u, v : ℝ`;
* `(G/H)^v = G^v H / H` and `H ∩ G^v = H^{ψ_{G/H}(v)}` for every `v : ℝ`;
* `v` is an upper jump of `G` if and only if `v` is an upper jump of `G ⧸ H` or `ψ_{G/H}(v)` is an
  upper jump of `H`.

We also deduce the field-theoretic form for a finite Galois extension `L/K` of fraction fields of
discrete valuation rings with normal subgroup `H ≤ Gal(L/K)` and fixed field `E = L^H`, identifying
the quotient action on `FixedPoints.subalgebra A (integralClosure A L) H` with the action of
`Gal(E/K)` on `integralClosure A E` along `IsGalois.normalAutEquivQuotient H` and
`TauCeti.fixedPointsIntegralClosureEquiv`.

These results generalize the nonarchimedean local-field development in
`TauCeti/NumberTheory/LocalField/Herbrand/{Quotient,Tower,UpperQuotient}.lean` to arbitrary
discrete valuation rings with separable residue extensions.

## Main results

* `TauCeti.IsLocalRing.herbrandFun_lowerIndex_sub_one`: Serre's lemma
  `φ_H(i_G(σ) - 1) = i_{G/H}(σ H) - 1` for `σ` maximizing the lower index in its coset.
* `TauCeti.IsLocalRing.map_quotientMk'_ramificationGroupReal`: Herbrand's theorem on the lower
  filtration, `(G_u).map (QuotientGroup.mk' H) = (G ⧸ H)_{φ_H(u)}`.
* `TauCeti.IsLocalRing.natCard_ramificationGroupReal_quotient_herbrandFun_mul`: counting form
  `#(G ⧸ H)_{φ_H(u)} · #H_u = #G_u`.
* `TauCeti.IsLocalRing.herbrandFun_tower`: transitivity `φ_G = φ_{G ⧸ H} ∘ φ_H` on `ℝ`.
* `TauCeti.IsLocalRing.inverseHerbrandFun_tower`, `TauCeti.IsLocalRing.herbrandOrderIso_tower`,
  `TauCeti.IsLocalRing.psiNat_tower`: transitivity of `ψ`, `herbrandOrderIso`, and `ψℕ`.
* `TauCeti.IsLocalRing.upperRamificationGroup_quotient_eq_map`: Herbrand's theorem in the upper
  numbering, `(G ⧸ H)^v = (G^v).map (QuotientGroup.mk' H)`.
* `TauCeti.IsLocalRing.subgroupOf_upperRamificationGroup_of_normal`:
  `H ∩ G^v = H^{ψ_{G ⧸ H}(v)}`.
* `TauCeti.IsLocalRing.upperJump_iff_quotient_or_subgroup`: characterization of upper jumps in a
  quotient.
* `TauCeti.IsLocalRing.herbrandFun_fixedField_tower`,
  `TauCeti.IsLocalRing.inverseHerbrandFun_fixedField_tower`,
  `TauCeti.IsLocalRing.subgroupOf_upperRamificationGroup_fixedField`,
  `TauCeti.IsLocalRing.upperRamificationGroup_fixedField_eq_map`,
  `TauCeti.IsLocalRing.map_restrictNormalHom_upperRamificationGroup`: field-theoretic form through
  `IsGalois.normalAutEquivQuotient`.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §1 Proposition 3 and §3 Lemmas 4–5,
  Propositions 14–15.
* J.-P. Serre, *Sur les corps locaux à corps résiduel algébriquement clos*, Bull. Soc. Math.
  France 89 (1961), n° 3.1, Propositions 3–4.
-/

public section
noncomputable section

open IsLocalRing

namespace TauCeti.IsLocalRing

section Quotient

variable (A B : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B]
  [IsLocalHom (algebraMap A B)]
  [Algebra.IsSeparable (ResidueField A) (ResidueField B)]
  (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B]
  [Algebra.IsInvariant A B G] [FaithfulSMul G B]
  (H : Subgroup G) [H.Normal]

/-- **Serre's lemma on the lower index of a quotient.** If `σ` maximizes `lowerIndex B` in its
coset `σ H` and `i_G(σ) = j` is finite, then `φ_H(j - 1) = i_{G/H}(σ H) - 1`. -/
theorem herbrandFun_lowerIndex_sub_one (σ : G) {j : ℕ}
    (hj : lowerIndex B σ = j)
    (hσ : ∀ τ : H, lowerIndex B (σ * (τ : G)) ≤ lowerIndex B σ) :
    herbrandFun H B ((j : ℝ) - 1) =
      ((lowerIndex (FixedPoints.subalgebra A B H) (σ : G ⧸ H)).toNat : ℝ) - 1 := by
  have hsum := natCard_ramificationGroup_zero_mul_lowerIndex_mk_eq_sum_card A B G H σ hj hσ
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1
    (lowerIndex_mk_ne_top A B G H σ (hj ▸ ENat.natCast_ne_top j) fun τ hτ ↦ hσ ⟨τ, hτ⟩)
  rw [← hn, ← Nat.cast_mul, ← Nat.cast_sum, Nat.cast_inj] at hsum
  rw [← hn, ENat.toNat_natCast]
  have h0 : (Nat.card (ramificationGroup H B 0) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := ramificationGroup H B 0)).ne'
  rcases j with _ | m
  · rw [Nat.cast_zero, zero_sub, herbrandFun_neg_one]
    simp only [Finset.range_zero, Finset.sum_empty, mul_eq_zero,
      (Nat.card_pos (α := ramificationGroup H B 0)).ne', false_or] at hsum
    simp [hsum]
  · have hjm : ((m + 1 : ℕ) : ℝ) - 1 = (m : ℝ) := by push_cast; ring
    rw [hjm, herbrandFun_natCast, div_eq_iff h0]
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (Nat.add_one_pos m), Nat.cast_zero,
      zero_add, Finset.Ico_add_one_right_eq_Icc] at hsum
    have hsumR : (Nat.card (ramificationGroup H B 0) : ℝ) * n =
        Nat.card (ramificationGroup H B 0) +
          ∑ i ∈ Finset.Icc 1 m, (Nat.card (ramificationGroup H B i) : ℝ) := by
      exact_mod_cast hsum
    linear_combination -hsumR

private theorem mk_mem_ramificationGroupReal_herbrandFun_iff (σ : G)
    (hσ : ∀ τ ∈ H, lowerIndex B (σ * τ) ≤ lowerIndex B σ) (u : ℝ) :
    (σ : G ⧸ H) ∈ ramificationGroupReal (G ⧸ H) (FixedPoints.subalgebra A B H)
        (herbrandFun H B u) ↔
      σ ∈ ramificationGroupReal G B u := by
  rcases eq_or_ne (lowerIndex B σ) ⊤ with htop | htop
  · rw [lowerIndex_eq_top_iff] at htop
    subst htop
    exact iff_of_true (one_mem _) (one_mem _)
  obtain ⟨j, hj⟩ := ENat.ne_top_iff_exists.1 htop
  rw [mem_ramificationGroupReal_iff_of_lowerIndex_eq
      (ENat.natCast_toNat (lowerIndex_mk_ne_top A B G H σ htop hσ)).symm,
    ← herbrandFun_lowerIndex_sub_one A B G H σ hj.symm fun τ ↦ hσ τ τ.property,
    mem_ramificationGroupReal_iff_of_lowerIndex_eq hj.symm]
  exact (herbrandFun_strictMono H B).le_iff_le

omit [FaithfulSMul G B] in
private theorem exists_mk'_eq_and_forall_lowerIndex_mul_le (σ : G) :
    ∃ σ' : G, QuotientGroup.mk' H σ' = QuotientGroup.mk' H σ ∧
      ∀ τ ∈ H, lowerIndex B (σ' * τ) ≤ lowerIndex B σ' := by
  obtain ⟨τ₀, hτ₀_mem, hτ₀⟩ := Subgroup.exists_mem_forall_lowerIndex_mul_le (S := B) H σ
  refine ⟨σ * τ₀, ?_, hτ₀⟩
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
  simp [inv_mem hτ₀_mem]

/-- **Herbrand's theorem on the lower filtration.** For a faithful finite group action on discrete
valuation rings with separable residue extension and normal subgroup `H ≤ G`, the image of `G_u`
in `G ⧸ H` is `(G ⧸ H)_{φ_H(u)}` for every real `u`. -/
theorem map_quotientMk'_ramificationGroupReal (u : ℝ) :
    (ramificationGroupReal G B u).map (QuotientGroup.mk' H) =
      ramificationGroupReal (G ⧸ H) (FixedPoints.subalgebra A B H) (herbrandFun H B u) := by
  ext q
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    obtain ⟨σ', hmk, hσ'⟩ := exists_mk'_eq_and_forall_lowerIndex_mul_le B G H σ
    have hmem : σ'⁻¹ * σ ∈ H := QuotientGroup.eq.1 hmk
    have hle : lowerIndex B σ ≤ lowerIndex B σ' := by
      simpa only [mul_inv_cancel_left] using hσ' _ hmem
    rw [← hmk, QuotientGroup.mk'_apply, mk_mem_ramificationGroupReal_herbrandFun_iff A B G H _ hσ']
    rw [ramificationGroupReal_def, mem_ramificationGroup_iff_le_lowerIndex] at hσ ⊢
    exact hσ.trans hle
  · intro h
    induction q using QuotientGroup.induction_on with | _ σ =>
    obtain ⟨σ', hmk, hσ'⟩ := exists_mk'_eq_and_forall_lowerIndex_mul_le B G H σ
    refine ⟨σ', ?_, hmk⟩
    rw [← mk_mem_ramificationGroupReal_herbrandFun_iff A B G H _ hσ']
    rw [← QuotientGroup.mk'_apply, hmk]
    exact h

/-- **Herbrand's theorem in counting form:** `#(G ⧸ H)_{φ_H(u)} · #H_u = #G_u` for every `u : ℝ`. -/
theorem natCard_ramificationGroupReal_quotient_herbrandFun_mul (u : ℝ) :
    Nat.card (ramificationGroupReal (G ⧸ H) (FixedPoints.subalgebra A B H) (herbrandFun H B u)) *
        Nat.card (ramificationGroupReal H B u) =
      Nat.card (ramificationGroupReal G B u) := by
  set U := ramificationGroupReal G B u
  set f := (QuotientGroup.mk' H).domRestrict U
  have hrange : Nat.card f.range =
      Nat.card (ramificationGroupReal (G ⧸ H) (FixedPoints.subalgebra A B H)
        (herbrandFun H B u)) := by
    rw [MonoidHom.domRestrict_range, map_quotientMk'_ramificationGroupReal A B G H u]
  have hker : Nat.card f.ker = Nat.card (ramificationGroupReal H B u) := by
    rw [MonoidHom.ker_domRestrict, QuotientGroup.ker_mk', ← subgroupOf_ramificationGroupReal,
      ← Subgroup.card_subtype U (H.subgroupOf U),
      ← Subgroup.card_subtype H (U.subgroupOf H),
      Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype, inf_comm]
  rw [← hrange, ← hker, mul_comm]
  exact Subgroup.card_ker_mul_card_range f

private theorem ramificationGroupReal_eq_of_mem_Icc (K : Type*) [Group K] [MulSemiringAction K B]
    {m : ℕ} {t u : ℝ} (ht₁ : (m : ℝ) < t) (ht₂ : t ≤ u) (hu : u ≤ m + 1) :
    ramificationGroupReal K B t = ramificationGroupReal K B u := by
  rw [ramificationGroupReal_eq_of_sub_one_lt_of_le K B (i := m + 1) (by push_cast; linarith)
      (by push_cast; linarith),
    ramificationGroupReal_eq_of_sub_one_lt_of_le K B (i := m + 1) (by push_cast; linarith)
      (by push_cast; linarith)]

private theorem ramificationGroupReal_quotient_eq_of_forall_eq {a b t : ℝ}
    (ht₁ : herbrandFun H B a < t) (ht₂ : t ≤ herbrandFun H B b)
    (h : ∀ s : ℝ, a < s → s ≤ b → ramificationGroupReal G B s = ramificationGroupReal G B b) :
    ramificationGroupReal (G ⧸ H) (FixedPoints.subalgebra A B H) t =
      ramificationGroupReal (G ⧸ H) (FixedPoints.subalgebra A B H) (herbrandFun H B b) := by
  have hs₁ : a < inverseHerbrandFun H B t := by
    rw [← inverseHerbrandFun_herbrandFun H B a]
    exact inverseHerbrandFun_strictMono H B ht₁
  have hs₂ : inverseHerbrandFun H B t ≤ b := by
    rw [← inverseHerbrandFun_herbrandFun H B b]
    exact (inverseHerbrandFun_strictMono H B).monotone ht₂
  have ht : t = herbrandFun H B (inverseHerbrandFun H B t) :=
    (herbrandFun_inverseHerbrandFun H B t).symm
  rw [ht, ← map_quotientMk'_ramificationGroupReal A B G H,
    ← map_quotientMk'_ramificationGroupReal A B G H, h _ hs₁ hs₂]

private theorem div_natCard_ramificationGroupReal_eq_mul (u : ℝ) :
    (Nat.card (ramificationGroupReal G B u) : ℝ) / Nat.card (ramificationGroup G B 0) =
      ((Nat.card (ramificationGroupReal H B u) : ℝ) / Nat.card (ramificationGroup H B 0)) *
        ((Nat.card (ramificationGroupReal (G ⧸ H) (FixedPoints.subalgebra A B H)
            (herbrandFun H B u)) : ℝ) /
          Nat.card (ramificationGroup (G ⧸ H) (FixedPoints.subalgebra A B H) 0)) := by
  set C := FixedPoints.subalgebra A B H
  have hcard : (Nat.card (ramificationGroupReal (G ⧸ H) C (herbrandFun H B u)) : ℝ) *
      Nat.card (ramificationGroupReal H B u) = Nat.card (ramificationGroupReal G B u) := by
    exact_mod_cast natCard_ramificationGroupReal_quotient_herbrandFun_mul A B G H u
  have hcard₀ : (Nat.card (ramificationGroup (G ⧸ H) C 0) : ℝ) *
      Nat.card (ramificationGroup H B 0) = Nat.card (ramificationGroup G B 0) := by
    have h0 := natCard_ramificationGroupReal_quotient_herbrandFun_mul A B G H 0
    rw [herbrandFun_zero, ← Int.cast_zero, ramificationGroupReal_intCast,
      ramificationGroupReal_intCast, ramificationGroupReal_intCast] at h0
    exact_mod_cast h0
  rw [div_mul_div_comm, ← hcard, ← hcard₀,
    mul_comm (Nat.card (ramificationGroupReal H B u) : ℝ),
    mul_comm (Nat.card (ramificationGroup H B 0) : ℝ)]

private theorem herbrandFun_tower_of_mem_Icc_of_eq (m : ℕ) {u : ℝ} (h₁ : (m : ℝ) ≤ u)
    (h₂ : u ≤ m + 1)
    (hm : herbrandFun G B m =
      herbrandFun (G ⧸ H) (FixedPoints.subalgebra A B H) (herbrandFun H B m)) :
    herbrandFun G B u =
      herbrandFun (G ⧸ H) (FixedPoints.subalgebra A B H) (herbrandFun H B u) := by
  set C := FixedPoints.subalgebra A B H
  have hG : ∀ t : ℝ, (m : ℝ) < t → t ≤ u →
      ramificationGroupReal G B t = ramificationGroupReal G B u := fun _ ht₁ ht₂ ↦
    ramificationGroupReal_eq_of_mem_Icc B G ht₁ ht₂ h₂
  have hH : ∀ t : ℝ, (m : ℝ) < t → t ≤ u →
      ramificationGroupReal H B t = ramificationGroupReal H B u := fun _ ht₁ ht₂ ↦
    ramificationGroupReal_eq_of_mem_Icc B H ht₁ ht₂ h₂
  have hGsub := herbrandFun_sub_of_forall_eq G B h₁ hG
  have hHsub := herbrandFun_sub_of_forall_eq H B h₁ hH
  have hQsub := herbrandFun_sub_of_forall_eq (G ⧸ H) C ((herbrandFun_strictMono H B).monotone h₁)
    fun _ ht₁ ht₂ ↦ ramificationGroupReal_quotient_eq_of_forall_eq A B G H ht₁ ht₂ hG
  rw [div_natCard_ramificationGroupReal_eq_mul A B G H u] at hGsub
  rw [hHsub] at hQsub
  linear_combination hGsub - hQsub + hm

private theorem herbrandFun_tower_of_mem_Icc (m : ℕ) :
    ∀ u : ℝ, (m : ℝ) ≤ u → u ≤ m + 1 →
      herbrandFun G B u =
        herbrandFun (G ⧸ H) (FixedPoints.subalgebra A B H) (herbrandFun H B u) := by
  induction m with
  | zero =>
    intro u h₁ h₂
    refine herbrandFun_tower_of_mem_Icc_of_eq A B G H 0 h₁ h₂ ?_
    simp
  | succ m ih =>
    intro u h₁ h₂
    exact herbrandFun_tower_of_mem_Icc_of_eq A B G H (m + 1) h₁ h₂
      (ih _ (by push_cast; linarith) (by push_cast; linarith))

/-- **Transitivity of the Herbrand function:** `φ_G(u) = φ_{G ⧸ H}(φ_H(u))` for every real `u`.
Completeness of `A` is not required; separability of the residue extension is essential. -/
theorem herbrandFun_tower (u : ℝ) :
    herbrandFun G B u =
      herbrandFun (G ⧸ H) (FixedPoints.subalgebra A B H) (herbrandFun H B u) := by
  set C := FixedPoints.subalgebra A B H
  rcases le_or_gt u (-1) with hu | hu
  · -- Below `-1`, both sides are affine with value `-1` at `-1` and slope `#G / #G_0`.
    have hφH_le : herbrandFun H B u ≤ -1 := by
      rw [← herbrandFun_neg_one H B]
      exact (herbrandFun_strictMono H B).monotone hu
    rw [herbrandFun_of_le_neg_one G B hu, herbrandFun_of_le_neg_one (G ⧸ H) C hφH_le,
      herbrandFun_of_le_neg_one H B hu]
    have hslope := div_natCard_ramificationGroupReal_eq_mul A B G H (-1)
    rw [herbrandFun_neg_one, show (-1 : ℝ) = ((-1 : ℤ) : ℝ) by norm_num,
      ramificationGroupReal_intCast, ramificationGroupReal_intCast, ramificationGroupReal_intCast,
      ramificationGroup_eq_top_of_le_neg_one _ _ le_rfl,
      ramificationGroup_eq_top_of_le_neg_one _ _ le_rfl,
      ramificationGroup_eq_top_of_le_neg_one _ _ le_rfl,
      Subgroup.card_top, Subgroup.card_top, Subgroup.card_top] at hslope
    rw [hslope]
    ring
  · rcases le_or_gt u 0 with h0 | h0
    · rw [herbrandFun_of_neg_one_le_of_le_zero H B hu.le h0,
        herbrandFun_of_neg_one_le_of_le_zero (G ⧸ H) C hu.le h0,
        herbrandFun_of_neg_one_le_of_le_zero G B hu.le h0]
    · exact herbrandFun_tower_of_mem_Icc A B G H ⌊u⌋₊ u (Nat.floor_le h0.le)
        (Nat.lt_floor_add_one u).le

/-- **Transitivity of the inverse Herbrand function:** `ψ_G(v) = ψ_H(ψ_{G ⧸ H}(v))` for every
real `v`. -/
theorem inverseHerbrandFun_tower (v : ℝ) :
    inverseHerbrandFun G B v =
      inverseHerbrandFun H B
        (inverseHerbrandFun (G ⧸ H) (FixedPoints.subalgebra A B H) v) := by
  apply (herbrandFun_strictMono G B).injective
  rw [herbrandFun_inverseHerbrandFun, herbrandFun_tower A B G H,
    herbrandFun_inverseHerbrandFun, herbrandFun_inverseHerbrandFun]

/-- **Transitivity of the Herbrand order isomorphism:**
`herbrandOrderIso G B = (herbrandOrderIso H B).trans (herbrandOrderIso (G ⧸ H) B^H)`. -/
theorem herbrandOrderIso_tower :
    herbrandOrderIso G B =
      (herbrandOrderIso H B).trans
        (herbrandOrderIso (G ⧸ H) (FixedPoints.subalgebra A B H)) := by
  refine OrderIso.ext (funext fun u ↦ Subtype.ext ?_)
  rw [OrderIso.trans_apply, coe_herbrandOrderIso_apply, coe_herbrandOrderIso_apply,
    coe_herbrandOrderIso_apply]
  exact herbrandFun_tower A B G H u

/-- **Transitivity of the integral inverse Herbrand function:**
`ψℕ_G(n) = ψℕ_H(ψℕ_{G ⧸ H}(n))`. -/
theorem psiNat_tower (n : ℕ) :
    psiNat G B n = psiNat H B (psiNat (G ⧸ H) (FixedPoints.subalgebra A B H) n) := by
  apply Nat.cast_injective (R := ℝ)
  rw [coe_psiNat, coe_psiNat, coe_psiNat, inverseHerbrandFun_tower A B G H]

/-- **Herbrand's theorem in the upper numbering:** for every real `v`,
`(G ⧸ H)^v = (G^v).map (QuotientGroup.mk' H)`. Completeness of `A` is not required; separability
of the residue extension is essential. -/
theorem upperRamificationGroup_quotient_eq_map (v : ℝ) :
    upperRamificationGroup (G ⧸ H) (FixedPoints.subalgebra A B H) v =
      (upperRamificationGroup G B v).map (QuotientGroup.mk' H) := by
  rw [upperRamificationGroup_def, upperRamificationGroup_def,
    map_quotientMk'_ramificationGroupReal A B G H,
    inverseHerbrandFun_tower A B G H, herbrandFun_inverseHerbrandFun]

/-- **Normal subgroup trace in the upper numbering:** `H ∩ G^v = H^{ψ_{G ⧸ H}(v)}` for every
real `v`. -/
theorem subgroupOf_upperRamificationGroup_of_normal (v : ℝ) :
    (upperRamificationGroup G B v).subgroupOf H =
      upperRamificationGroup H B
        (inverseHerbrandFun (G ⧸ H) (FixedPoints.subalgebra A B H) v) := by
  rw [subgroupOf_upperRamificationGroup, inverseHerbrandFun_tower A B G H,
    herbrandFun_inverseHerbrandFun]

/-- Every upper jump of the quotient `G ⧸ H` is an upper jump of `G`. -/
theorem upperJump_of_quotient {v : ℝ}
    (hv : UpperJump (G ⧸ H) (FixedPoints.subalgebra A B H) v) : UpperJump G B v := by
  rw [upperJump_iff] at hv ⊢
  intro w hvw
  refine lt_of_le_of_ne (upperRamificationGroup_antitone G B hvw.le) fun heq ↦ (hv w hvw).ne ?_
  rw [upperRamificationGroup_quotient_eq_map A B G H,
    upperRamificationGroup_quotient_eq_map A B G H, heq]

omit [Finite G] in
private theorem subgroup_eq_of_le_of_map_mk'_eq_of_subgroupOf_eq {K₁ K₂ : Subgroup G}
    (hle : K₁ ≤ K₂) (hmap : K₁.map (QuotientGroup.mk' H) = K₂.map (QuotientGroup.mk' H))
    (htrace : K₁.subgroupOf H = K₂.subgroupOf H) : K₁ = K₂ := by
  refine le_antisymm hle fun σ hσ ↦ ?_
  obtain ⟨τ, hτ, hτσ⟩ : QuotientGroup.mk' H σ ∈ K₁.map (QuotientGroup.mk' H) := by
    rw [hmap]
    exact Subgroup.mem_map_of_mem _ hσ
  have hρH : τ⁻¹ * σ ∈ H := by
    rw [← QuotientGroup.ker_mk' H, MonoidHom.mem_ker, map_mul, map_inv, hτσ, inv_mul_cancel]
  have hρ : (⟨τ⁻¹ * σ, hρH⟩ : H) ∈ K₁.subgroupOf H := by
    rw [htrace, Subgroup.mem_subgroupOf]
    exact mul_mem (inv_mem (hle hτ)) hσ
  rw [Subgroup.mem_subgroupOf] at hρ
  simpa only [mul_inv_cancel_left] using mul_mem hτ hρ

/-- **Upper jumps in a quotient:** `v` is an upper jump of `G` if and only if `v` is an upper jump
of `G ⧸ H` or `ψ_{G ⧸ H}(v)` is an upper jump of `H`. -/
theorem upperJump_iff_quotient_or_subgroup (v : ℝ) :
    UpperJump G B v ↔
      UpperJump (G ⧸ H) (FixedPoints.subalgebra A B H) v ∨
        UpperJump H B (inverseHerbrandFun (G ⧸ H) (FixedPoints.subalgebra A B H) v) := by
  set C := FixedPoints.subalgebra A B H
  constructor
  · intro hv
    rw [upperJump_iff] at hv
    refine or_iff_not_imp_left.2 fun hQ ↦ (upperJump_iff H B _).2 fun x hx ↦ ?_
    obtain ⟨w₀, hvw₀, hw₀⟩ : ∃ w₀, v < w₀ ∧
        upperRamificationGroup (G ⧸ H) C w₀ = upperRamificationGroup (G ⧸ H) C v := by
      simp only [upperJump_iff, not_forall] at hQ
      obtain ⟨w₀, hvw₀, hlt⟩ := hQ
      exact ⟨w₀, hvw₀, (upperRamificationGroup_antitone (G ⧸ H) C hvw₀.le).eq_of_not_lt hlt⟩
    set w := min w₀ (herbrandFun (G ⧸ H) C x)
    have hvw : v < w := lt_min hvw₀ <| by
      have hx' : inverseHerbrandFun (G ⧸ H) C v < x := hx
      simpa only [herbrandFun_inverseHerbrandFun] using herbrandFun_strictMono (G ⧸ H) C hx'
    have hw : upperRamificationGroup (G ⧸ H) C w = upperRamificationGroup (G ⧸ H) C v :=
      le_antisymm (upperRamificationGroup_antitone (G ⧸ H) C hvw.le)
        (hw₀ ▸ upperRamificationGroup_antitone (G ⧸ H) C (min_le_left _ _))
    have hxw : inverseHerbrandFun (G ⧸ H) C w ≤ x := by
      simpa only [inverseHerbrandFun_herbrandFun] using
        (inverseHerbrandFun_strictMono (G ⧸ H) C).monotone
          (min_le_right w₀ (herbrandFun (G ⧸ H) C x))
    refine (upperRamificationGroup_antitone H B hxw).trans_lt ?_
    rw [← subgroupOf_upperRamificationGroup_of_normal A B G H,
      ← subgroupOf_upperRamificationGroup_of_normal A B G H]
    refine lt_of_le_of_ne (Subgroup.comap_mono (upperRamificationGroup_antitone G B hvw.le))
      fun heq ↦ (hv w hvw).ne (subgroup_eq_of_le_of_map_mk'_eq_of_subgroupOf_eq G H
        (upperRamificationGroup_antitone G B hvw.le) ?_ heq)
    rw [← upperRamificationGroup_quotient_eq_map A B G H,
      ← upperRamificationGroup_quotient_eq_map A B G H, hw]
  · rintro (hQ | hH)
    · exact upperJump_of_quotient A B G H hQ
    · rw [upperJump_iff] at hH ⊢
      intro w hvw
      refine lt_of_le_of_ne (upperRamificationGroup_antitone G B hvw.le) fun heq ↦ ?_
      have hlt := hH _ (inverseHerbrandFun_strictMono (G ⧸ H) C hvw)
      rw [← subgroupOf_upperRamificationGroup_of_normal A B G H,
        ← subgroupOf_upperRamificationGroup_of_normal A B G H, heq] at hlt
      exact hlt.ne rfl

end Quotient

/-! ### Field form through `IsGalois.normalAutEquivQuotient` -/

section FieldForm

variable (A K L : Type*) [CommRing A] [Field K] [Algebra A K]
  [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
  [FiniteDimensional K L] [IsGalois K L]
  [IsDomain A] [IsDiscreteValuationRing A] [IsFractionRing A K]

omit [FiniteDimensional K L] in
private theorem isGaloisGroup_integralClosure :
    IsGaloisGroup (L ≃ₐ[K] L) A (integralClosure A L) :=
  IsGaloisGroup.of_isIntegralClosure (L ≃ₐ[K] L) A (integralClosure A L) K L

omit [FiniteDimensional K L] in
private theorem isInvariant_integralClosure :
    Algebra.IsInvariant A (integralClosure A L) (L ≃ₐ[K] L) :=
  (isGaloisGroup_integralClosure A K L).isInvariant

omit [FiniteDimensional K L] in
private theorem faithfulSMul_integralClosure :
    FaithfulSMul (L ≃ₐ[K] L) (integralClosure A L) :=
  (isGaloisGroup_integralClosure A K L).faithful

attribute [local instance] isInvariant_integralClosure faithfulSMul_integralClosure

variable (H : Subgroup (L ≃ₐ[K] L)) [H.Normal]
  [IsDiscreteValuationRing (integralClosure A L)]
  [IsLocalHom (algebraMap A (integralClosure A L))]
  [Algebra.IsSeparable (ResidueField A) (ResidueField (integralClosure A L))]
  [_root_.IsLocalRing (integralClosure A (IntermediateField.fixedField H))]

/-- **Transitivity of the Herbrand function** in a finite Galois extension `L/K` of fraction fields
of discrete valuation rings with normal subgroup `H ≤ Gal(L/K)` and fixed field `E = L^H`. -/
theorem herbrandFun_fixedField_tower (u : ℝ) :
    herbrandFun (L ≃ₐ[K] L) (integralClosure A L) u =
      herbrandFun
        ((IntermediateField.fixedField H) ≃ₐ[K] (IntermediateField.fixedField H))
        (integralClosure A (IntermediateField.fixedField H))
        (herbrandFun H (integralClosure A L) u) := by
  rw [herbrandFun_tower A (integralClosure A L) (L ≃ₐ[K] L) H u]
  exact (IsGalois.normalAutEquivQuotient H).herbrandFun_eq_of_equiv
    (TauCeti.fixedPointsIntegralClosureEquiv A K L H).toRingEquiv
    (TauCeti.fixedPointsIntegralClosureEquiv_smul A K L H) _

/-- **Transitivity of the inverse Herbrand function** in a finite Galois extension `L/K` of
fraction fields of discrete valuation rings with normal subgroup `H ≤ Gal(L/K)` and fixed field
`E = L^H`. -/
theorem inverseHerbrandFun_fixedField_tower (v : ℝ) :
    inverseHerbrandFun (L ≃ₐ[K] L) (integralClosure A L) v =
      inverseHerbrandFun H (integralClosure A L)
        (inverseHerbrandFun
          ((IntermediateField.fixedField H) ≃ₐ[K] (IntermediateField.fixedField H))
          (integralClosure A (IntermediateField.fixedField H)) v) := by
  rw [inverseHerbrandFun_tower A (integralClosure A L) (L ≃ₐ[K] L) H v,
    (IsGalois.normalAutEquivQuotient H).inverseHerbrandFun_eq_of_equiv
      (TauCeti.fixedPointsIntegralClosureEquiv A K L H).toRingEquiv
      (TauCeti.fixedPointsIntegralClosureEquiv_smul A K L H)]

/-- **Normal subgroup trace in the upper numbering, field form:** for a finite Galois extension
`L/K` of fraction fields of discrete valuation rings with separable residue extension and normal
subgroup `H ≤ Gal(L/K)`, `H ∩ Gal(L/K)^v = H^{ψ_{L^H / K}(v)}`. -/
theorem subgroupOf_upperRamificationGroup_fixedField (v : ℝ) :
    (upperRamificationGroup (L ≃ₐ[K] L) (integralClosure A L) v).subgroupOf H =
      upperRamificationGroup H (integralClosure A L)
        (inverseHerbrandFun
          ((IntermediateField.fixedField H) ≃ₐ[K] (IntermediateField.fixedField H))
          (integralClosure A (IntermediateField.fixedField H)) v) := by
  rw [subgroupOf_upperRamificationGroup_of_normal A (integralClosure A L) (L ≃ₐ[K] L) H v,
    (IsGalois.normalAutEquivQuotient H).inverseHerbrandFun_eq_of_equiv
      (TauCeti.fixedPointsIntegralClosureEquiv A K L H).toRingEquiv
      (TauCeti.fixedPointsIntegralClosureEquiv_smul A K L H)]

/-- **Herbrand's theorem in the upper numbering, field form through
`IsGalois.normalAutEquivQuotient`:** for a finite Galois extension `L/K` of fraction fields of
discrete valuation rings with separable residue extension and normal subgroup `H ≤ Gal(L/K)`,
`IsGalois.normalAutEquivQuotient H` identifies the quotient upper group `(G^v).map mk'` with
`Gal(L^H / K)^v` acting on `integralClosure A (L^H)`. -/
theorem upperRamificationGroup_fixedField_eq_map (v : ℝ) :
    upperRamificationGroup
        ((IntermediateField.fixedField H) ≃ₐ[K] (IntermediateField.fixedField H))
        (integralClosure A (IntermediateField.fixedField H)) v =
      ((upperRamificationGroup (L ≃ₐ[K] L) (integralClosure A L) v).map
          (QuotientGroup.mk' H)).map
        (IsGalois.normalAutEquivQuotient H).toMonoidHom := by
  rw [← upperRamificationGroup_quotient_eq_map A (integralClosure A L) (L ≃ₐ[K] L) H v]
  exact ((IsGalois.normalAutEquivQuotient H).map_upperRamificationGroup_of_equiv
    (TauCeti.fixedPointsIntegralClosureEquiv A K L H).toRingEquiv
    (TauCeti.fixedPointsIntegralClosureEquiv_smul A K L H) v).symm

/-- **Herbrand's theorem in the upper numbering, restriction form:** restriction to the fixed
field `L^H` maps `Gal(L/K)^v` onto `Gal(L^H/K)^v`. -/
theorem map_restrictNormalHom_upperRamificationGroup (v : ℝ) :
    (upperRamificationGroup (L ≃ₐ[K] L) (integralClosure A L) v).map
        (AlgEquiv.restrictNormalHom (IntermediateField.fixedField H)) =
      upperRamificationGroup
        ((IntermediateField.fixedField H) ≃ₐ[K] (IntermediateField.fixedField H))
        (integralClosure A (IntermediateField.fixedField H)) v := by
  have hcomp : (IsGalois.normalAutEquivQuotient H).toMonoidHom.comp (QuotientGroup.mk' H) =
      AlgEquiv.restrictNormalHom (IntermediateField.fixedField H) :=
    MonoidHom.ext (IsGalois.normalAutEquivQuotient_apply H)
  rw [upperRamificationGroup_fixedField_eq_map A K L H v, Subgroup.map_map, hcomp]

end FieldForm

end TauCeti.IsLocalRing
