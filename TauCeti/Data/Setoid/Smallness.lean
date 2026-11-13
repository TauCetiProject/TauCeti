/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Setoid.Basic
public import Mathlib.Data.Set.Countable

/-!
# Small sides of equivalence-class partitions

Suppose a set meets countably many classes of an equivalence relation, and small sets are closed
under countable unions. If the set is not small, some class has a non-small intersection with it.
If every class cut has a small side, the complement of that intersection is small.

This is a combinatorial way to find a centre for a concentrated family. The smallness predicate
can, for example, mean that a set meets only countably many classes of a finer relation, or that
an ordinal-valued rank is bounded below the first uncountable ordinal.
-/

public section

open Set

namespace Setoid

/-- If a non-small set meets countably many equivalence classes and every class cut has a small
side, one class meets it in a non-small set with small complement. Only closure under countable
unions is needed; downward closure of smallness is not required. -/
theorem exists_class_not_small_and_small_sdiff {X : Type*} (E : Setoid X) (K : Set X)
    (small : Set X → Prop)
    (hUnion : ∀ S : Set (Set X), S.Countable → (∀ s ∈ S, small s) → small (⋃₀ S))
    [Countable (Quotient (E.comap (Subtype.val : K → X)))] (hK : ¬ small K)
    (hsplit : ∀ x ∈ K, small (K ∩ {y | E x y}) ∨ small (K \ {y | E x y})) :
    ∃ x ∈ K, ¬ small (K ∩ {y | E x y}) ∧ small (K \ {y | E x y}) := by
  classical
  let F (q : Quotient (E.comap (Subtype.val : K → X))) := K ∩ {y | E q.out.val y}
  have hcover : ⋃₀ range F = K := by
    ext x
    constructor
    · rintro ⟨s, ⟨q, rfl⟩, hx⟩
      exact hx.1
    · intro hx
      let q : Quotient (E.comap (Subtype.val : K → X)) := ⟦⟨x, hx⟩⟧
      exact mem_sUnion.2 ⟨F q, mem_range_self q,
        hx, Quotient.exact (s := E.comap (Subtype.val : K → X)) (Quotient.out_eq q)⟩
  have hex : ∃ q, ¬ small (F q) := by
    by_contra! h
    exact hK (hcover ▸ hUnion (range F) (countable_range F) (by
      rintro s ⟨q, rfl⟩
      exact h q))
  obtain ⟨q, hq⟩ := hex
  exact ⟨q.out.val, q.out.prop, hq, (hsplit q.out.val q.out.prop).resolve_left hq⟩

end Setoid
