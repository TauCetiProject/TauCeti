/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.List.Cycle

/-!
# Chains on extended lists

A list extended by one entry is a chain exactly when the list is a chain whose last entry is related
to the new one. In particular a list followed by its first entry is a chain exactly when the list is
a chain whose last entry is related to its first.

A list followed by itself is a chain for a relation exactly when the list is a chain as a cycle:
consecutive entries are related, and so is the last entry to the first. This cyclic condition is
invariant under rotating the list, and it can be assembled from two chains, one leading from a
nonempty block to another and one leading back.

If any two entries of a list are related in one direction or the other, then some permutation of
the list is a chain. This is the list form of the existence of a spanning path in a tournament.
-/

public section

namespace List

variable {α : Type*} {R : α → α → Prop}

/-- A list extended by one entry is a chain exactly when the list is a chain whose last entry, if
any, is related to the new entry. -/
theorem isChain_append_singleton_iff {l : List α} {a : α} :
    (l ++ [a]).IsChain R ↔ l.IsChain R ∧ ∀ x ∈ l.getLast?, R x a := by
  simp [isChain_append]

/-- A list followed by its first entry is a chain exactly when the list is a chain whose last entry,
if the list is nonempty, is related to its first entry. -/
theorem isChain_append_take_one_iff {l : List α} :
    (l ++ l.take 1).IsChain R ↔ l.IsChain R ∧ ∀ h : l ≠ [], R (l.getLast h) (l.head h) := by
  cases l with
  | nil => simp
  | cons a l =>
    rw [take_one, head?_cons, Option.toList_some, isChain_append_singleton_iff,
      getLast?_eq_some_getLast (cons_ne_nil a l)]
    simp

/-- A list followed by itself is a chain exactly when the list is a chain as a cycle. -/
theorem isChain_append_self_iff {l : List α} :
    (l ++ l).IsChain R ↔ Cycle.Chain R (l : Cycle α) := by
  cases l with
  | nil => simp
  | cons a l =>
    rw [Cycle.chain_coe_cons]
    refine ⟨fun h => h.prefix ⟨l, by simp⟩, fun h => ?_⟩
    simpa using h.append_overlap (l₁ := a :: l) (l₂ := [a]) (l₃ := l)
      (by simpa using h.left_of_append) (by simp)

/-- The chain condition on a list followed by itself is invariant under rotating the list. -/
theorem IsRotated.isChain_append_self_iff {l l' : List α} (h : l ~r l') :
    (l ++ l).IsChain R ↔ (l' ++ l').IsChain R := by
  rw [List.isChain_append_self_iff, List.isChain_append_self_iff, Cycle.coe_eq_coe.2 h]

/-- A cyclic version of `List.IsChain.append_overlap`: chains running from a nonempty block `l₁`
to a nonempty block `l₃` and from `l₃` back to `l₁` close up to a chain on the cycle
`l₁ ++ l₂ ++ l₃ ++ l₄`. -/
theorem IsChain.append_self_of_overlap {l₁ l₂ l₃ l₄ : List α} (h : (l₁ ++ l₂ ++ l₃).IsChain R)
    (h' : (l₃ ++ l₄ ++ l₁).IsChain R) (h₁ : l₁ ≠ []) (h₃ : l₃ ≠ []) :
    (l₁ ++ l₂ ++ l₃ ++ l₄ ++ (l₁ ++ l₂ ++ l₃ ++ l₄)).IsChain R := by
  have g : (l₁ ++ l₂ ++ l₃ ++ l₄ ++ l₁).IsChain R := by
    simpa using h.append_overlap (by simpa using h') h₃
  simpa using g.append_overlap (l₃ := l₂ ++ l₃ ++ l₄) (g.prefix ⟨l₁, by simp⟩) h₁

/-- Inserting `x` into a chain `l` whose entries are each related to `x` in one direction or the
other gives a chain that is a permutation of `x :: l` and that starts with `x` or with the first
entry of `l`. -/
private theorem exists_perm_cons_isChain_aux {x : α} :
    ∀ {l : List α}, l.IsChain R → (∀ a ∈ l, R x a ∨ R a x) →
      ∃ l', l' ~ x :: l ∧ l'.IsChain R ∧ (l'.head? = some x ∨ l'.head? = l.head?)
  | [], _, _ => ⟨[x], Perm.refl _, isChain_singleton x, Or.inl rfl⟩
  | a :: t, hl, h => by
    rcases h a mem_cons_self with hxa | hax
    · exact ⟨x :: a :: t, Perm.refl _, hl.cons (by simpa using hxa), Or.inl rfl⟩
    · obtain ⟨t', ht', hct', hd⟩ := exists_perm_cons_isChain_aux (isChain_cons.1 hl).2
        fun b hb => h b (mem_cons_of_mem a hb)
      refine ⟨a :: t', (ht'.cons a).trans (Perm.swap x a t), hct'.cons ?_, Or.inr rfl⟩
      rcases hd with hd | hd
      · simpa [hd] using hax
      · simpa [hd] using (isChain_cons.1 hl).1

/-- If any two entries of a list are related by `R` in one direction or the other, then some
permutation of the list is a chain for `R`. -/
theorem Pairwise.exists_perm_isChain {l : List α} (hl : l.Pairwise fun a b => R a b ∨ R b a) :
    ∃ l', l' ~ l ∧ l'.IsChain R := by
  induction hl with
  | nil => exact ⟨[], Perm.refl _, isChain_nil⟩
  | @cons x t hx _ ih =>
    obtain ⟨l, hlt, hl⟩ := ih
    obtain ⟨l', hl', hcl', -⟩ := exists_perm_cons_isChain_aux hl fun a ha => hx a (hlt.subset ha)
    exact ⟨l', hl'.trans (hlt.cons x), hcl'⟩

end List
