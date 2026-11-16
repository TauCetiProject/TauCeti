/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import TauCeti.GroupTheory.Complement.CrossedProjection
public import TauCeti.GroupTheory.Perm.ParityRetract
import TauCeti.Algebra.Group.Subgroup.ZPowers

/-!
# Complements of the alternating group in the symmetric group

Let `α` be a finite type. Because `alternatingGroup α` is the kernel of `Equiv.Perm.sign`, every
odd involution `t : Equiv.Perm α` (`Perm.sign t = -1` and `t ^ 2 = 1`, for instance any
transposition `t.IsSwap`) generates a two-element complement `Subgroup.zpowers t = {1, t}` of
`alternatingGroup α` in `Equiv.Perm α` (`TauCeti.isComplement'_alternatingGroup_zpowers`,
`Equiv.Perm.IsSwap.isComplement'_alternatingGroup_zpowers`).

Conversely, when `α` is nontrivial, `Equiv.Perm.sign` is surjective onto `{1, -1}`, so every
complement `D` of `alternatingGroup α` contains a unique odd permutation `t`
(`TauCeti.existsUnique_mem_and_sign_eq_neg_one_of_isComplement'_alternatingGroup`); disjointness
from `alternatingGroup α` forces `t ^ 2 = 1` and `D = Subgroup.zpowers t`, giving the bijection
`TauCeti.alternatingGroupComplementEquiv` between odd involutions of `Equiv.Perm α` and complements
of `alternatingGroup α` in `Equiv.Perm α`.

Note that for `|α| ≥ 4` an odd involution need not be a transposition (for instance a product of
three disjoint transpositions in `S₆`), whereas on `Fin 3` and `Fin 4` the odd involutions are
precisely the transpositions.

Along a complement containing the odd involution `t`, the crossed projection
`Equiv.Perm α → alternatingGroup α` sends `g` to `g` when `g` is even and to `g * t` when `g` is
odd (`TauCeti.coe_crossedProjection_alternatingGroup_of_mem`, agreeing with
`g * t.parityRetract ht g` when `t` is a transposition). It is a group homomorphism if and only if
`Fintype.card α ≤ 2` (`TauCeti.crossedProjection_alternatingGroup_map_mul_iff`).
-/

public section

namespace TauCeti

open Equiv

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Any odd involution `t` of `Perm α` (`Perm.sign t = -1` and `t ^ 2 = 1`) generates a complement
of `alternatingGroup α` in `Perm α`. -/
theorem isComplement'_alternatingGroup_zpowers {t : Perm α} (hsign : Perm.sign t = -1)
    (hsq : t ^ 2 = 1) :
    (alternatingGroup α).IsComplement' (Subgroup.zpowers t) := by
  apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
  · rw [disjoint_iff_inf_le]
    rintro g ⟨hgA, hgt⟩
    rcases (Subgroup.mem_zpowers_iff_of_sq_eq_one hsq).mp hgt with rfl | rfl
    · exact Subgroup.one_mem ⊥
    · have h1 : Perm.sign g = 1 := Perm.mem_alternatingGroup.mp hgA
      rw [hsign] at h1
      exact absurd h1 (by decide)
  · rw [Set.eq_univ_iff_forall]
    intro g
    rcases Int.units_eq_one_or (Perm.sign g) with hg | hg
    · exact ⟨g, Perm.mem_alternatingGroup.mpr hg, 1, Subgroup.one_mem _, mul_one g⟩
    · refine ⟨g * t, Perm.mem_alternatingGroup.mpr ?_, t, Subgroup.mem_zpowers t, ?_⟩
      · rw [map_mul, hg, hsign]
        decide
      · dsimp only
        rw [mul_assoc, ← sq, hsq, mul_one]

/-- Along any complement `D` of `alternatingGroup α` containing an odd involution `t`, the crossed
projection sends even permutations `g` to `g` and odd permutations `g` to `g * t`. -/
theorem coe_crossedProjection_alternatingGroup_of_mem {D : Subgroup (Perm α)}
    (hD : (alternatingGroup α).IsComplement' D) {t : Perm α} (htD : t ∈ D)
    (hsign : Perm.sign t = -1) (hsq : t ^ 2 = 1) (g : Perm α) :
    (hD.crossedProjection g : Perm α) = if Perm.sign g = 1 then g else g * t := by
  rcases Int.units_eq_one_or (Perm.sign g) with hg | hg
  · simp only [hg, ↓reduceIte]
    exact congrArg Subtype.val (hD.crossedProjection_coe ⟨g, Perm.mem_alternatingGroup.mpr hg⟩)
  · have hne : Perm.sign g ≠ 1 := by rw [hg]; decide
    have hgt : g * t ∈ alternatingGroup α := by
      rw [Perm.mem_alternatingGroup, map_mul, hg, hsign]
      decide
    have hmul : g = (⟨g * t, hgt⟩ : alternatingGroup α) * (⟨t, htD⟩ : D) := by
      simp only [mul_assoc, ← sq, hsq, mul_one]
    simp only [hne, ↓reduceIte]
    conv_lhs => rw [hmul]
    exact congrArg Subtype.val (hD.crossedProjection_mul ⟨g * t, hgt⟩ ⟨t, htD⟩)

/-- Along any complement `D` of `alternatingGroup α` containing a transposition `t`, the crossed
projection sends `g` to `g * t.parityRetract ht g`. -/
theorem coe_crossedProjection_alternatingGroup_of_isSwap {D : Subgroup (Perm α)}
    (hD : (alternatingGroup α).IsComplement' D) {t : Perm α} (ht : t.IsSwap) (htD : t ∈ D)
    (g : Perm α) :
    (hD.crossedProjection g : Perm α) = g * t.parityRetract ht g := by
  rw [coe_crossedProjection_alternatingGroup_of_mem hD htD ht.sign_eq
    (ht.orderOf ▸ pow_orderOf_eq_one t) g, Perm.parityRetract_apply]
  split_ifs
  · exact (mul_one g).symm
  · rfl

/-- Any odd permutation belonging to a complement of `alternatingGroup α` has square `1`. -/
theorem sq_eq_one_of_isComplement'_alternatingGroup {D : Subgroup (Perm α)}
    (hD : (alternatingGroup α).IsComplement' D) {t : Perm α} (htD : t ∈ D)
    (hsign : Perm.sign t = -1) : t ^ 2 = 1 := by
  have ht2A : t ^ 2 ∈ alternatingGroup α := by
    rw [Perm.mem_alternatingGroup, map_pow, hsign]
    decide
  exact Subgroup.mem_bot.mp (disjoint_iff_inf_le.mp hD.disjoint ⟨ht2A, D.pow_mem htD 2⟩)

/-- Any complement of `alternatingGroup α` containing an odd permutation `t` is generated by `t`. -/
theorem eq_zpowers_of_isComplement'_alternatingGroup {D : Subgroup (Perm α)}
    (hD : (alternatingGroup α).IsComplement' D) {t : Perm α} (htD : t ∈ D)
    (hsign : Perm.sign t = -1) : D = Subgroup.zpowers t := by
  refine le_antisymm (fun x hxD => ?_) (Subgroup.zpowers_le.mpr htD)
  rcases Int.units_eq_one_or (Perm.sign x) with hx | hx
  · have hx1 : x = 1 := Subgroup.mem_bot.mp
      (disjoint_iff_inf_le.mp hD.disjoint ⟨Perm.mem_alternatingGroup.mpr hx, hxD⟩)
    exact hx1 ▸ Subgroup.one_mem _
  · have htxA : t⁻¹ * x ∈ alternatingGroup α := by
      rw [Perm.mem_alternatingGroup, map_mul, map_inv, hsign, hx]
      decide
    have htx1 : t⁻¹ * x = 1 := Subgroup.mem_bot.mp
      (disjoint_iff_inf_le.mp hD.disjoint ⟨htxA, D.mul_mem (D.inv_mem htD) hxD⟩)
    exact inv_mul_eq_one.mp htx1 ▸ Subgroup.mem_zpowers t

/-- When `α` is nontrivial, every complement `D` of `alternatingGroup α` in `Perm α` contains a
unique odd permutation. -/
theorem existsUnique_mem_and_sign_eq_neg_one_of_isComplement'_alternatingGroup [Nontrivial α]
    {D : Subgroup (Perm α)} (hD : (alternatingGroup α).IsComplement' D) :
    ∃! t : Perm α, t ∈ D ∧ Perm.sign t = -1 := by
  obtain ⟨g₀, hg₀⟩ := Perm.sign_surjective α (-1)
  obtain ⟨⟨n, d⟩, hnd⟩ := hD.surjective g₀
  have hd_sign : Perm.sign (d : Perm α) = -1 := by
    have hs := congrArg Perm.sign hnd
    simpa [Perm.mem_alternatingGroup.mp n.property, hg₀] using hs
  refine ⟨d, ⟨d.property, hd_sign⟩, fun t ⟨htD, hts⟩ => ?_⟩
  have hdtA : (d : Perm α)⁻¹ * t ∈ alternatingGroup α := by
    rw [Perm.mem_alternatingGroup, map_mul, map_inv, hd_sign, hts]
    decide
  have hdt1 : (d : Perm α)⁻¹ * t = 1 := Subgroup.mem_bot.mp
    (disjoint_iff_inf_le.mp hD.disjoint ⟨hdtA, D.mul_mem (D.inv_mem d.property) htD⟩)
  exact (inv_mul_eq_one.mp hdt1).symm

/-- **Classification of complements of `alternatingGroup α`.** When `α` is nontrivial, the
complements of `alternatingGroup α` in `Perm α` are precisely the subgroups generated by an odd
involution. -/
theorem isComplement'_alternatingGroup_iff [Nontrivial α] (D : Subgroup (Perm α)) :
    (alternatingGroup α).IsComplement' D ↔
      ∃ t : Perm α, Perm.sign t = -1 ∧ t ^ 2 = 1 ∧ Subgroup.zpowers t = D := by
  refine ⟨fun hD => ?_, ?_⟩
  · obtain ⟨t, ⟨htD, hts⟩, -⟩ :=
      existsUnique_mem_and_sign_eq_neg_one_of_isComplement'_alternatingGroup hD
    exact ⟨t, hts, sq_eq_one_of_isComplement'_alternatingGroup hD htD hts,
      (eq_zpowers_of_isComplement'_alternatingGroup hD htD hts).symm⟩
  · rintro ⟨t, hts, hsq, rfl⟩
    exact isComplement'_alternatingGroup_zpowers hts hsq

/-- **Bijection between odd involutions and complements of `alternatingGroup α`.** -/
noncomputable def alternatingGroupComplementEquiv (α : Type*) [Fintype α] [DecidableEq α]
    [Nontrivial α] :
    {t : Perm α // Perm.sign t = -1 ∧ t ^ 2 = 1} ≃
      {D : Subgroup (Perm α) // (alternatingGroup α).IsComplement' D} :=
  Equiv.ofBijective
    (fun t => ⟨Subgroup.zpowers t.val, isComplement'_alternatingGroup_zpowers t.2.1 t.2.2⟩)
    ⟨fun t₁ t₂ h => Subtype.ext <| by
        have hz : Subgroup.zpowers t₁.val = Subgroup.zpowers t₂.val := congrArg Subtype.val h
        have hmem : t₁.val ∈ Subgroup.zpowers t₂.val := hz ▸ Subgroup.mem_zpowers t₁.val
        rcases (Subgroup.mem_zpowers_iff_of_sq_eq_one t₂.2.2).mp hmem with h1 | h12
        · have hs1 := t₁.2.1
          rw [h1, map_one] at hs1
          exact absurd hs1 (by decide)
        · exact h12,
      fun D =>
        let ⟨t, hs, hsq, hz⟩ := (isComplement'_alternatingGroup_iff D.val).mp D.property
        ⟨⟨t, hs, hsq⟩, Subtype.ext hz⟩⟩

/-- The complement of `alternatingGroup α` attached to an odd involution `t` is
`Subgroup.zpowers t`. -/
@[simp]
theorem coe_alternatingGroupComplementEquiv_apply [Nontrivial α]
    (t : {t : Perm α // Perm.sign t = -1 ∧ t ^ 2 = 1}) :
    (alternatingGroupComplementEquiv α t : Subgroup (Perm α)) = Subgroup.zpowers t.val :=
  (rfl)

/-- The odd involution attached to a complement `D` generates `D`. -/
@[simp]
theorem zpowers_alternatingGroupComplementEquiv_symm_apply [Nontrivial α]
    (D : {D : Subgroup (Perm α) // (alternatingGroup α).IsComplement' D}) :
    Subgroup.zpowers ((alternatingGroupComplementEquiv α).symm D : Perm α) = D.val :=
  congrArg Subtype.val ((alternatingGroupComplementEquiv α).apply_symm_apply D)

/-- The odd involution attached to a complement `D` belongs to `D`. -/
@[simp]
theorem mem_alternatingGroupComplementEquiv_symm_apply [Nontrivial α]
    (D : {D : Subgroup (Perm α) // (alternatingGroup α).IsComplement' D}) :
    ((alternatingGroupComplementEquiv α).symm D : Perm α) ∈ D.val := by
  rw [← zpowers_alternatingGroupComplementEquiv_symm_apply]
  exact Subgroup.mem_zpowers _

attribute [local instance] Subgroup.conjugationAction in
/-- **Multiplicativity of the crossed projection onto `alternatingGroup α`.** For any complement `D`
of `alternatingGroup α` in `Perm α`, its crossed projection is a group homomorphism if and only if
`Fintype.card α ≤ 2`. -/
theorem crossedProjection_alternatingGroup_map_mul_iff {D : Subgroup (Perm α)}
    (hD : (alternatingGroup α).IsComplement' D) :
    (∀ g k : Perm α, hD.crossedProjection (g * k) =
        hD.crossedProjection g * hD.crossedProjection k) ↔
      Fintype.card α ≤ 2 := by
  rw [hD.crossedProjection_map_mul_iff]
  refine ⟨fun htriv => ?_, fun h2 d n => ?_⟩
  · by_contra! hcard
    have : Nontrivial α := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    obtain ⟨t, ⟨htD, hsign⟩, -⟩ :=
      existsUnique_mem_and_sign_eq_neg_one_of_isComplement'_alternatingGroup hD
    have hsq : t ^ 2 = 1 := sq_eq_one_of_isComplement'_alternatingGroup hD htD hsign
    have ht1 : t ≠ 1 := by rintro rfl; simp at hsign
    obtain ⟨a, hab⟩ : ∃ a : α, t a ≠ a := by
      by_contra! hfix
      exact ht1 (Perm.ext hfix)
    have hcompl : (({a, t a} : Finset α)ᶜ).Nonempty := by
      rw [← Finset.card_pos]
      have hsum := Finset.card_add_card_compl ({a, t a} : Finset α)
      rw [Finset.card_pair hab.symm] at hsum
      omega
    obtain ⟨c, hc⟩ := hcompl
    simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or, ← ne_eq] at hc
    let σ : Perm α := swap a (t a) * swap (t a) c
    have hσ : σ ∈ alternatingGroup α := by
      rw [Perm.mem_alternatingGroup, map_mul, Perm.sign_swap hab.symm, Perm.sign_swap hc.2.symm]
      decide
    have hcomm : t * σ = σ * t := by
      have hs := congrArg Subtype.val (htriv ⟨t, htD⟩ ⟨σ, hσ⟩)
      rw [Subgroup.coe_conjugationAction_smul] at hs
      exact mul_inv_eq_iff_eq_mul.mp hs
    have hlhs : (t * σ) a = a := by
      simp only [σ, Perm.mul_apply, swap_apply_of_ne_of_ne hab.symm hc.1.symm, swap_apply_left]
      exact (Perm.mul_apply t t a).symm.trans (by rw [← sq, hsq, Perm.one_apply])
    have hrhs : (σ * t) a = c := by
      simp only [σ, Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne hc.1 hc.2]
    exact hc.1 (hrhs.symm.trans ((congrFun (congrArg DFunLike.coe hcomm) a).symm.trans hlhs))
  · have hbot : alternatingGroup α = ⊥ :=
      alternatingGroup.eq_bot_of_card_le_two (Nat.card_eq_fintype_card.trans_le h2)
    have hn1 : n = 1 := Subtype.ext (Subgroup.mem_bot.mp (hbot ▸ n.property))
    rw [hn1, MulDistribMulAction.smul_one]

end TauCeti

namespace Equiv.Perm

/-- Every transposition generates a complement of `alternatingGroup α` in `Perm α`. -/
theorem IsSwap.isComplement'_alternatingGroup_zpowers {α : Type*} [Fintype α] [DecidableEq α]
    {t : Perm α} (ht : t.IsSwap) :
    (alternatingGroup α).IsComplement' (Subgroup.zpowers t) :=
  TauCeti.isComplement'_alternatingGroup_zpowers ht.sign_eq (ht.orderOf ▸ pow_orderOf_eq_one t)

end Equiv.Perm
