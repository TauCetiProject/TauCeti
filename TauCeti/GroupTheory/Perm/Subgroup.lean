/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Complement
public import Mathlib.GroupTheory.Perm.Subgroup
public import Mathlib.Order.Sum.Order
import TauCeti.Data.Fintype.Sort

/-!
# Subgroups of permutation groups

These formulas describe how the permutation associated by Mathlib's
`Equiv.Perm.subgroupOfMulAction`, and its inverse permutation, act on points of a faithful action.

When `ι` has a single element, the transpositions `swap (inl default) x` of `ι ⊕ κ` form a left
transversal of the subgroup `Perm ι × Perm κ`, the range of `Equiv.Perm.sumCongrHom`
(`Equiv.Perm.isComplement_range_swap_inl_sumCongrHom_range`). When `κ₁` and `κ₂` are finite linear
orders, so do the shuffles, the permutations `σ` of `κ₁ ⊕ κ₂` that are increasing on each summand
for the order induced by an injective map `f : κ₁ ⊕ κ₂ → L` to a linear order
(`Equiv.Perm.isComplement_setOf_strictMono_sumCongrHom_range`), for instance for the lexicographic
order (`Equiv.Perm.isComplement_setOf_strictMono_toLex_sumCongrHom_range`). The underlying fact is
that exactly one permutation of a finite linear order sorts the values of an injective map
(`Equiv.Perm.existsUnique_strictMono_comp`, from `TauCeti.Data.Fintype.Sort`).
-/

public section

namespace TauCeti

/-- Restricting `MulAction.toPermHom` to its image leaves its action on points unchanged. -/
@[simp]
theorem subgroupOfMulAction_apply {G H : Type*} [Group G] [MulAction G H]
    [FaithfulSMul G H] (g : G) (x : H) :
    ((Equiv.Perm.subgroupOfMulAction G H g : (MulAction.toPermHom G H).range) :
      Equiv.Perm H) x = g • x := rfl

/-- The inverse permutation associated to `g` acts by `g⁻¹`. -/
@[simp]
theorem subgroupOfMulAction_inv_apply {G H : Type*} [Group G] [MulAction G H]
    [FaithfulSMul G H] (g : G) (x : H) :
    (((Equiv.Perm.subgroupOfMulAction G H g : (MulAction.toPermHom G H).range) :
      Equiv.Perm H)⁻¹) x = g⁻¹ • x := by
  simpa only [map_inv, Subgroup.coe_inv] using subgroupOfMulAction_apply g⁻¹ x

end TauCeti

namespace Equiv.Perm

/-- The transpositions of `inl default` with the elements of `ι ⊕ κ` (including the identity) form
a left transversal of `Perm ι × Perm κ` in `Perm (ι ⊕ κ)` when `ι` has a single element. -/
theorem isComplement_range_swap_inl_sumCongrHom_range (ι κ : Type*) [Unique ι] [DecidableEq ι]
    [DecidableEq κ] :
    Subgroup.IsComplement (Set.range fun x : ι ⊕ κ => swap (.inl default) x)
      (sumCongrHom ι κ).range := by
  -- A permutation fixing `inl default` preserves the right summand, and so lies in the range.
  have hmem (τ : Perm (ι ⊕ κ)) (hτ : τ (.inl default) = .inl default) :
      τ ∈ (sumCongrHom ι κ).range := by
    have h (x : ι ⊕ κ) : (τ x).isRight ↔ x.isRight := by
      rcases x with a | b
      · simp [Unique.eq_default a, hτ]
      · rcases hb : τ (.inr b) with a | _
        · rw [Unique.eq_default a, ← hτ] at hb
          simpa using τ.injective hb
        · simp
    refine ⟨(1, sumIsRight.permCongr (τ.subtypePerm h)), ?_⟩
    ext (a | b)
    · simp [Unique.eq_default a, hτ]
    · simp [permCongr_apply, subtypePerm_apply]
  rw [Subgroup.isComplement_iff_existsUnique_inv_mul_mem]
  intro g
  refine ⟨⟨swap (.inl default) (g (.inl default)), Set.mem_range_self _⟩, hmem _ (by simp), ?_⟩
  rintro ⟨_, ⟨a, rfl⟩⟩ ⟨⟨p, q⟩, hpq⟩
  have h : swap (.inl default) a (g (.inl default)) = .inl default := by
    simpa [Unique.eq_default (p default)] using congr($hpq (Sum.inl default)).symm
  simp [(swap_apply_eq_iff.mp h).trans (swap_apply_left _ _)]

/-- The shuffles, the permutations of `κ₁ ⊕ κ₂` that are increasing on each summand for the order
induced by an injective map `f` to a linear order, form a left transversal of
`Perm κ₁ × Perm κ₂` in `Perm (κ₁ ⊕ κ₂)`. -/
theorem isComplement_setOf_strictMono_sumCongrHom_range {κ₁ κ₂ L : Type*} [LinearOrder κ₁]
    [Finite κ₁] [LinearOrder κ₂] [Finite κ₂] [LinearOrder L] {f : κ₁ ⊕ κ₂ → L}
    (hf : Function.Injective f) :
    Subgroup.IsComplement
      {σ : Perm (κ₁ ⊕ κ₂) | StrictMono (f ∘ σ ∘ Sum.inl) ∧ StrictMono (f ∘ σ ∘ Sum.inr)}
      (sumCongrHom κ₁ κ₂).range := by
  rw [Subgroup.isComplement_iff_existsUnique_inv_mul_mem]
  intro g
  -- Sort the values of `f ∘ g` on each summand separately.
  obtain ⟨p, hp, hpu⟩ := existsUnique_strictMono_comp (hf.comp (g.injective.comp Sum.inl_injective))
  obtain ⟨q, hq, hqu⟩ := existsUnique_strictMono_comp (hf.comp (g.injective.comp Sum.inr_injective))
  have hl (a : Perm κ₁) (b : Perm κ₂) :
      f ∘ ⇑(g * sumCongr a b) ∘ Sum.inl = (f ∘ g ∘ Sum.inl) ∘ a := by
    ext
    simp
  have hr (a : Perm κ₁) (b : Perm κ₂) :
      f ∘ ⇑(g * sumCongr a b) ∘ Sum.inr = (f ∘ g ∘ Sum.inr) ∘ b := by
    ext
    simp
  refine ⟨⟨g * sumCongr p q, by rw [Set.mem_ofPred_eq, hl, hr]; exact ⟨hp, hq⟩⟩,
    ⟨(p⁻¹, q⁻¹), by simp⟩, ?_⟩
  rintro ⟨t, ht⟩ ⟨⟨a, b⟩, hab⟩
  -- A shuffle in the coset of `g` is `g * sumCongr a⁻¹ b⁻¹`, so `a⁻¹` and `b⁻¹` sort `f ∘ g`.
  have ht' : t = g * sumCongr a⁻¹ b⁻¹ := by
    rw [sumCongrHom_apply, eq_inv_mul_iff_mul_eq, ← eq_mul_inv_iff_mul_eq] at hab
    simpa using hab
  subst ht'
  rw [Set.mem_ofPred_eq, hl, hr] at ht
  ext1
  simp only [hpu _ ht.1, hqu _ ht.2]

/-- The `(κ₁, κ₂)`-shuffles, the permutations of `κ₁ ⊕ κ₂` that are increasing on each summand
for the lexicographic order, form a left transversal of `Perm κ₁ × Perm κ₂` in
`Perm (κ₁ ⊕ κ₂)`. -/
theorem isComplement_setOf_strictMono_toLex_sumCongrHom_range (κ₁ κ₂ : Type*) [LinearOrder κ₁]
    [Finite κ₁] [LinearOrder κ₂] [Finite κ₂] :
    Subgroup.IsComplement
      {σ : Perm (κ₁ ⊕ κ₂) | StrictMono (toLex ∘ σ ∘ Sum.inl) ∧ StrictMono (toLex ∘ σ ∘ Sum.inr)}
      (sumCongrHom κ₁ κ₂).range :=
  isComplement_setOf_strictMono_sumCongrHom_range toLex.injective

end Equiv.Perm
