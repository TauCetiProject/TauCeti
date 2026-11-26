/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Sum.Order
public import Mathlib.Order.Hom.Basic
public import Mathlib.Logic.Equiv.Sum

/-!
# Subtypes of lexicographic sums

A subtype of the lexicographic sum `α ⊕ₗ β` is order isomorphic to the lexicographic sum of its
part in `α` and its part in `β`: `OrderIso.subtypeSumLex`. This is the order version of Mathlib's
`Equiv.subtypeSum`.
-/

public section

namespace OrderIso

variable {α β : Type*} [LE α] [LE β] {p : α ⊕ₗ β → Prop}

/-- A subtype of a lexicographic sum is order isomorphic to the lexicographic sum of its two
parts. -/
def subtypeSumLex :
    {c // p c} ≃o {a // p (toLex (Sum.inl a))} ⊕ₗ {b // p (toLex (Sum.inr b))} where
  toEquiv := (Equiv.subtypeEquiv ofLex fun _ => Iff.rfl).trans (Equiv.subtypeSum.trans toLex)
  map_rel_iff' {c c'} := by
    obtain ⟨c, h⟩ := c
    obtain ⟨c', h'⟩ := c'
    -- `Equiv.subtypeSum` is defined by matching on the summand, so the map sends
    -- `⟨toLex (inl a), h⟩` to `toLex (inl ⟨a, h⟩)` and `⟨toLex (inr b), h⟩` to
    -- `toLex (inr ⟨b, h⟩)` by definition, and `≤` on a subtype is `≤` on the values. The `Sum.Lex`
    -- lemmas below therefore apply to both sides of each goal up to this unfolding.
    obtain ⟨a | b, rfl⟩ := toLex.surjective c <;> obtain ⟨a' | b', rfl⟩ := toLex.surjective c'
    · exact Sum.Lex.inl_le_inl_iff.trans
        (Sum.Lex.inl_le_inl_iff (β := β) (a := a) (b := a')).symm
    · exact iff_of_true (Sum.Lex.inl_le_inr _ _) (Sum.Lex.inl_le_inr _ _)
    · exact iff_of_false Sum.Lex.not_inr_le_inl Sum.Lex.not_inr_le_inl
    · exact Sum.Lex.inr_le_inr_iff.trans
        (Sum.Lex.inr_le_inr_iff (α := α) (a := b) (b := b')).symm

@[simp]
theorem subtypeSumLex_apply_inl (a : α) (h : p (toLex (Sum.inl a))) :
    subtypeSumLex ⟨toLex (Sum.inl a), h⟩ = toLex (Sum.inl ⟨a, h⟩) :=
  (rfl)

@[simp]
theorem subtypeSumLex_apply_inr (b : β) (h : p (toLex (Sum.inr b))) :
    subtypeSumLex ⟨toLex (Sum.inr b), h⟩ = toLex (Sum.inr ⟨b, h⟩) :=
  (rfl)

@[simp]
theorem subtypeSumLex_symm_apply_inl (a : {a // p (toLex (Sum.inl a))}) :
    subtypeSumLex.symm (toLex (Sum.inl a)) = ⟨toLex (Sum.inl a.val), a.property⟩ :=
  (rfl)

@[simp]
theorem subtypeSumLex_symm_apply_inr (b : {b // p (toLex (Sum.inr b))}) :
    subtypeSumLex.symm (toLex (Sum.inr b)) = ⟨toLex (Sum.inr b.val), b.property⟩ :=
  (rfl)

end OrderIso
