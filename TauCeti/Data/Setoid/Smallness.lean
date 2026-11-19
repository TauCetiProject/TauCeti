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
under countable unions. If the set is not small, some class has a non-small intersection with it
(`Setoid.exists_class_not_small`); for instance, if the set meets uncountably many classes of a
second relation, some class of the first meets it in uncountably many of them
(`Setoid.exists_class_not_countable_image`). If every class cut has a small side, the complement
of that intersection is small (`Setoid.exists_class_not_small_and_small_sdiff`).

This is a combinatorial way to find a centre for a concentrated family. The smallness predicate
can, for example, mean that a set meets only countably many classes of a finer relation, or that
an ordinal-valued rank is bounded below the first uncountable ordinal.
-/

public section

open Set

namespace Setoid

/-- If a non-small set meets countably many equivalence classes, one class meets it in a non-small
set, provided smallness is closed under countable unions. -/
theorem exists_class_not_small {X : Type*} (E : Setoid X) (K : Set X) (small : Set X → Prop)
    (hUnion : ∀ S : Set (Set X), S.Countable → (∀ s ∈ S, small s) → small (⋃₀ S))
    [Countable (Quotient (E.comap (Subtype.val : K → X)))] (hK : ¬ small K) :
    ∃ x ∈ K, ¬ small (K ∩ {y | E x y}) := by
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
  exact ⟨q.out.val, q.out.prop, hq⟩

/-- If a set meets countably many classes of `E` and uncountably many classes of `F`, one class of
`E` meets it in a set meeting uncountably many classes of `F`. -/
theorem exists_class_not_countable_image {X : Type*} (E F : Setoid X) (K : Set X)
    [Countable (Quotient (E.comap (Subtype.val : K → X)))]
    (hK : ¬ (Quotient.mk F '' K).Countable) :
    ∃ x ∈ K, ¬ (Quotient.mk F '' (K ∩ {y | E x y})).Countable := by
  refine E.exists_class_not_small K (fun A => (Quotient.mk F '' A).Countable)
    (fun S hS hs => ?_) hK
  rw [image_sUnion, sUnion_image]
  exact hS.biUnion hs

/-- If a non-small set meets countably many equivalence classes and every class cut has a small
side, one class meets it in a non-small set with small complement. Only closure under countable
unions is needed; downward closure of smallness is not required. -/
theorem exists_class_not_small_and_small_sdiff {X : Type*} (E : Setoid X) (K : Set X)
    (small : Set X → Prop)
    (hUnion : ∀ S : Set (Set X), S.Countable → (∀ s ∈ S, small s) → small (⋃₀ S))
    [Countable (Quotient (E.comap (Subtype.val : K → X)))] (hK : ¬ small K)
    (hsplit : ∀ x ∈ K, small (K ∩ {y | E x y}) ∨ small (K \ {y | E x y})) :
    ∃ x ∈ K, ¬ small (K ∩ {y | E x y}) ∧ small (K \ {y | E x y}) := by
  obtain ⟨x, hx, hnot⟩ := E.exists_class_not_small K small hUnion hK
  exact ⟨x, hx, hnot, (hsplit x hx).resolve_left hnot⟩

end Setoid
