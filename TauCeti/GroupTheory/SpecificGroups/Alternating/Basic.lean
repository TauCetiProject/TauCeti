/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
import TauCeti.Algebra.Group.Subgroup.Pointwise

/-!
# Support bounds and point stabilizers of alternating groups

This module records elementary facts about support cardinalities and point stabilizers of
`alternatingGroup α` for a finite type `α`:

* Every permutation of support size `2` is a transposition and hence odd, so no element of
  `alternatingGroup α` has support cardinality `2` (`alternatingGroup.card_support_ne_two`), and
  an even permutation moves at most `2` points if and only if it is the identity
  (`alternatingGroup.card_support_le_two_iff_eq_one`).
* When `Nat.card α ≤ 4`, an even permutation fixing two distinct points moves at most `2` points
  and is therefore trivial (`alternatingGroup.eq_one_of_mem_stabilizer_of_mem_stabilizer`,
  `alternatingGroup.stabilizer_inf_stabilizer_eq_bot`).
* A point stabilizer in `alternatingGroup α` is trivial if and only if `Nat.card α < 4`
  (`alternatingGroup.stabilizer_eq_bot_iff`).
* Whenever `4 ≤ Nat.card α`, distinct points of `α` have distinct stabilizers in
  `alternatingGroup α` (`alternatingGroup.stabilizer_injective`), so each point stabilizer is
  self-normalizing in `alternatingGroup α` (`alternatingGroup.normalizer_stabilizer`) and its image
  in `Equiv.Perm α` has normalizer equal to `MulAction.stabilizer (Equiv.Perm α) a`
  (`alternatingGroup.normalizer_map_subtype_stabilizer`).

## Main results

* `alternatingGroup.card_support_ne_two`: no element of `alternatingGroup α` has support size `2`.
* `alternatingGroup.card_support_le_two_iff_eq_one`: an even permutation has support cardinality at
  most `2` if and only if it is `1`.
* `alternatingGroup.eq_one_of_mem_stabilizer_of_mem_stabilizer`,
  `alternatingGroup.stabilizer_inf_stabilizer_eq_bot`: distinct points have trivially intersecting
  stabilizers in `alternatingGroup α` when `Nat.card α ≤ 4`.
* `alternatingGroup.stabilizer_injective`: distinct points have distinct stabilizers in
  `alternatingGroup α` when `4 ≤ Nat.card α`.
* `alternatingGroup.stabilizer_eq_bot_iff`: a point stabilizer in `alternatingGroup α` is trivial
  if and only if `Nat.card α < 4`.
* `alternatingGroup.normalizer_stabilizer`, `alternatingGroup.normalizer_map_subtype_stabilizer`:
  normalizers of point stabilizers of `alternatingGroup α` in `alternatingGroup α` and in
  `Equiv.Perm α` when `4 ≤ Nat.card α`.
-/

public section

namespace alternatingGroup

open Equiv Equiv.Perm

variable {α : Type*} [DecidableEq α] [Fintype α]

/-! ### Support cardinality of even permutations -/

/-- No even permutation has support of cardinality `2`, since every permutation of support size `2`
is a transposition and therefore odd. -/
theorem card_support_ne_two (g : alternatingGroup α) : (g : Perm α).support.card ≠ 2 := by
  intro h2
  have hsign := (card_support_eq_two.mp h2).sign_eq
  have halt := mem_alternatingGroup.mp g.property
  rw [hsign] at halt
  exact absurd halt (by decide)

/-- An even permutation has support of cardinality at most `2` if and only if it is the
identity. -/
@[simp]
theorem card_support_le_two_iff_eq_one {g : alternatingGroup α} :
    (g : Perm α).support.card ≤ 2 ↔ g = 1 := by
  refine ⟨fun hle => ?_, fun h => by simp [h]⟩
  have hle1 : (g : Perm α).support.card ≤ 1 :=
    Nat.lt_succ_iff.mp (lt_of_le_of_ne hle (card_support_ne_two g))
  exact Subtype.ext (card_support_le_one.mp hle1)

/-! ### Point stabilizers and their normalizers -/

/-- An even permutation of a type with `Nat.card α ≤ 4` fixing two distinct points is the
identity. -/
theorem eq_one_of_mem_stabilizer_of_mem_stabilizer (hα : Nat.card α ≤ 4) {a b : α}
    (hab : a ≠ b) {g : alternatingGroup α}
    (ha : g ∈ MulAction.stabilizer (alternatingGroup α) a)
    (hb : g ∈ MulAction.stabilizer (alternatingGroup α) b) : g = 1 := by
  refine card_support_le_two_iff_eq_one.mp ?_
  have hsub : (g : Perm α).support ⊆ ({a, b} : Finset α)ᶜ := by
    intro x hx
    rw [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton]
    rintro (rfl | rfl)
    · exact mem_support.mp hx ha
    · exact mem_support.mp hx hb
  have hcard : Fintype.card α ≤ 4 := by rwa [← Nat.card_eq_fintype_card]
  refine (Finset.card_le_card hsub).trans ?_
  rw [Finset.card_compl, Finset.card_pair hab]
  omega

/-- Distinct points of a type with `Nat.card α ≤ 4` have trivially intersecting stabilizers in
`alternatingGroup α`. -/
theorem stabilizer_inf_stabilizer_eq_bot (hα : Nat.card α ≤ 4) {a b : α} (hab : a ≠ b) :
    MulAction.stabilizer (alternatingGroup α) a ⊓
      MulAction.stabilizer (alternatingGroup α) b = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨ha, hb⟩
  exact Subgroup.mem_bot.mpr (eq_one_of_mem_stabilizer_of_mem_stabilizer hα hab ha hb)

/-- Distinct points have distinct stabilizers in `alternatingGroup α` whenever
`4 ≤ Nat.card α`. -/
theorem stabilizer_injective (hα : 4 ≤ Nat.card α) :
    Function.Injective (MulAction.stabilizer (alternatingGroup α) : α → _) := by
  intro a b h
  by_contra hab
  obtain ⟨c, hc, d, hd, hcd⟩ := (Finset.one_lt_card (s := ({a, b} : Finset α)ᶜ)).mp (by
    rw [Finset.card_compl, Finset.card_pair hab, ← Nat.card_eq_fintype_card]
    omega)
  simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or, ← ne_eq] at hc hd
  let g : alternatingGroup α :=
    ⟨swap b c * swap c d,
      mem_alternatingGroup.mpr (by rw [map_mul, sign_swap hc.2.symm, sign_swap hcd]; decide)⟩
  have hga : g ∈ MulAction.stabilizer (alternatingGroup α) a := by
    rw [MulAction.mem_stabilizer_iff, Subgroup.smul_def, Perm.smul_def]
    dsimp only [g]
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne hc.1.symm hd.1.symm,
      swap_apply_of_ne_of_ne hab hc.1.symm]
  have hgb : g ∈ MulAction.stabilizer (alternatingGroup α) b := h ▸ hga
  rw [MulAction.mem_stabilizer_iff, Subgroup.smul_def, Perm.smul_def] at hgb
  dsimp only [g] at hgb
  rw [Perm.mul_apply, swap_apply_of_ne_of_ne hc.2.symm hd.2.symm, swap_apply_left] at hgb
  exact hc.2 hgb

/-- A point stabilizer in `alternatingGroup α` is trivial if and only if `Nat.card α < 4`. -/
theorem stabilizer_eq_bot_iff (a : α) :
    MulAction.stabilizer (alternatingGroup α) a = ⊥ ↔ Nat.card α < 4 := by
  refine ⟨fun hbot => ?_, fun hα => ?_⟩
  · by_contra hge
    have h4 : 4 ≤ Nat.card α := by omega
    have : Nontrivial α := Finite.one_lt_card_iff_nontrivial.mp (by omega)
    obtain ⟨b, hba⟩ := exists_ne a
    have := isPretransitive_of_three_le_card α (by omega)
    obtain ⟨g, hga⟩ := MulAction.exists_smul_eq (alternatingGroup α) a b
    have hstab : MulAction.stabilizer (alternatingGroup α) b =
        MulAction.stabilizer (alternatingGroup α) a := by
      rw [← hga, MulAction.stabilizer_smul_eq_stabilizer_map_conj, hbot, Subgroup.map_bot]
    exact hba (stabilizer_injective h4 hstab)
  · rw [eq_bot_iff]
    intro g hg
    refine Subgroup.mem_bot.mpr (card_support_le_two_iff_eq_one.mp ?_)
    have hsub : (g : Perm α).support ⊆ ({a} : Finset α)ᶜ := by
      intro x hx
      rw [Finset.mem_compl, Finset.mem_singleton]
      rintro rfl
      exact mem_support.mp hx hg
    have hcard : Fintype.card α < 4 := by rwa [← Nat.card_eq_fintype_card]
    refine (Finset.card_le_card hsub).trans ?_
    rw [Finset.card_compl, Finset.card_singleton]
    omega

/-- Every point stabilizer of `alternatingGroup α` is self-normalizing whenever
`4 ≤ Nat.card α`. -/
theorem normalizer_stabilizer (hα : 4 ≤ Nat.card α) (a : α) :
    Subgroup.normalizer (MulAction.stabilizer (alternatingGroup α) a) =
      MulAction.stabilizer (alternatingGroup α) a := by
  ext g
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, ← MulEquiv.toMonoidHom_eq_coe,
    ← MulAction.stabilizer_smul_eq_stabilizer_map_conj,
    (stabilizer_injective hα).eq_iff, MulAction.mem_stabilizer_iff]

/-- In `Equiv.Perm α`, the normalizer of the image of `MulAction.stabilizer (alternatingGroup α) a`
is `MulAction.stabilizer (Equiv.Perm α) a` whenever `4 ≤ Nat.card α`. -/
theorem normalizer_map_subtype_stabilizer (hα : 4 ≤ Nat.card α) (a : α) :
    Subgroup.normalizer
      ((MulAction.stabilizer (alternatingGroup α) a).map (alternatingGroup α).subtype) =
      MulAction.stabilizer (Perm α) a := by
  have hmap (x : α) :
      (MulAction.stabilizer (alternatingGroup α) x).map (alternatingGroup α).subtype =
        MulAction.stabilizer (Perm α) x ⊓ alternatingGroup α := by
    rw [← MulAction.stabilizer_subgroupOf, Subgroup.subgroupOf_map_subtype]
  have hconj (σ : Perm α) :
      ((MulAction.stabilizer (alternatingGroup α) a).map (alternatingGroup α).subtype).map
          (MulAut.conj σ : Perm α →* Perm α) =
        (MulAction.stabilizer (alternatingGroup α) (σ • a)).map (alternatingGroup α).subtype := by
    rw [hmap a, hmap (σ • a), Subgroup.map_inf _ _ _ (MulAut.conj σ).injective,
      ← MulEquiv.toMonoidHom_eq_coe, ← MulAction.stabilizer_smul_eq_stabilizer_map_conj]
    congr 1
    rw [MulEquiv.toMonoidHom_eq_coe, TauCeti.map_conj_eq_conj_smul,
      Subgroup.Normal.conj_smul_eq_self]
  ext σ
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, hconj σ,
    (Subgroup.map_injective (alternatingGroup α).subtype_injective).eq_iff,
    (stabilizer_injective hα).eq_iff, MulAction.mem_stabilizer_iff]

end alternatingGroup
