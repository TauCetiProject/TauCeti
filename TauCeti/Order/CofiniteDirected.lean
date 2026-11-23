/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Order.Cofinal

/-!
# Cofinite directed refinements of directed orders

A directed set is *cofinite* if every element has only finitely many elements below it.
Cofinite directed sets are the index sets on which inverse systems can be built, and maps
into them constructed, by induction on the finitely many predecessors of an index: for
instance the matching objects of a pro-object at an index are finite limits.

Every directed preorder `α` receives a monotone map with cofinal range from a cofinite
directed partial order: the finite subsets of `α` that have a greatest element, ordered by
inclusion, and mapped to a chosen greatest element.

## Main declarations

* `TauCeti.FinsetWithGreatest α`: the finite subsets of `α` with a greatest element, ordered
  by inclusion.
* `TauCeti.FinsetWithGreatest.greatest`: a chosen greatest element.
* `TauCeti.FinsetWithGreatest.greatest_monotone` and
  `TauCeti.FinsetWithGreatest.isCofinal_range_greatest`: the chosen greatest element is a
  monotone map with cofinal range.
* `TauCeti.FinsetWithGreatest.finite_Iic`: the order is cofinite.

## References

* M. Artin and B. Mazur, *Étale homotopy*, Lecture Notes in Math. 100, Appendix, §2.
* S. Mardešić and J. Segal, *Shape theory*, Chapter I, §1.2, Theorem 2.
* D. Isaksen, *A model structure on the category of pro-simplicial sets*, Trans. Amer. Math.
  Soc. 353 (2001), §2.
-/

public section

noncomputable section

namespace TauCeti

variable (α : Type*)

section LE

variable [LE α]

/-- The finite subsets of an ordered type `α` that have a greatest element. They are ordered by
inclusion; when `α` is directed they form a cofinite directed set refining `α`. -/
@[ext]
structure FinsetWithGreatest where
  /-- The underlying finite subset. -/
  toFinset : Finset α
  /-- The finite subset has a greatest element. -/
  exists_isGreatest : ∃ a, IsGreatest (toFinset : Set α) a

namespace FinsetWithGreatest

variable {α}

theorem toFinset_injective : Function.Injective (toFinset : FinsetWithGreatest α → Finset α) :=
  fun _ _ ↦ FinsetWithGreatest.ext

/-- Finite subsets with a greatest element are ordered by inclusion. -/
instance : PartialOrder (FinsetWithGreatest α) :=
  PartialOrder.lift toFinset toFinset_injective

theorem le_iff_subset {s t : FinsetWithGreatest α} : s ≤ t ↔ s.toFinset ⊆ t.toFinset :=
  Iff.rfl

/-- A chosen greatest element of a finite subset with a greatest element. -/
def greatest (s : FinsetWithGreatest α) : α :=
  s.exists_isGreatest.choose

theorem isGreatest_greatest (s : FinsetWithGreatest α) :
    IsGreatest (s.toFinset : Set α) s.greatest :=
  s.exists_isGreatest.choose_spec

@[simp]
theorem greatest_mem (s : FinsetWithGreatest α) : s.greatest ∈ s.toFinset :=
  s.isGreatest_greatest.1

theorem le_greatest {s : FinsetWithGreatest α} {a : α} (ha : a ∈ s.toFinset) :
    a ≤ s.greatest :=
  s.isGreatest_greatest.2 ha

/-- Each finite subset with a greatest element contains only finitely many others: the order
is cofinite. -/
theorem finite_Iic (s : FinsetWithGreatest α) : (Set.Iic s).Finite :=
  (s.toFinset.powerset.finite_toSet.preimage toFinset_injective.injOn).subset
    fun _ ht ↦ Finset.mem_coe.2 (Finset.mem_powerset.2 ht)

end FinsetWithGreatest

end LE

namespace FinsetWithGreatest

variable {α} [Preorder α]

/-- Enlarging a finite subset can only increase its chosen greatest element. -/
theorem greatest_monotone : Monotone (greatest : FinsetWithGreatest α → α) :=
  fun _ t hst ↦ le_greatest (s := t) (hst (greatest_mem _))

/-- The singleton `{a}`, whose greatest element is `a`. -/
def singleton (a : α) : FinsetWithGreatest α :=
  ⟨{a}, a, by simp⟩

@[simp]
theorem toFinset_singleton (a : α) : (singleton a).toFinset = {a} := (rfl)

@[simp]
theorem greatest_singleton (a : α) : (singleton a).greatest = a :=
  Finset.mem_singleton.1 (greatest_mem (singleton a))

/-- Every element of `α` is the chosen greatest element of some finite subset, so the range
of `greatest` is cofinal. -/
theorem isCofinal_range_greatest : IsCofinal (Set.range (greatest : FinsetWithGreatest α → α)) :=
  fun a ↦ ⟨a, ⟨singleton a, greatest_singleton a⟩, le_rfl⟩

instance [Nonempty α] : Nonempty (FinsetWithGreatest α) :=
  ⟨singleton (Classical.arbitrary α)⟩

/-- Two finite subsets with greatest elements `a` and `b` both lie in their union with an
upper bound of `a` and `b`, which is the greatest element of that union. -/
instance [IsDirected α (· ≤ ·)] : IsDirected (FinsetWithGreatest α) (· ≤ ·) := by
  classical
  refine ⟨fun s t ↦ ?_⟩
  obtain ⟨c, hsc, htc⟩ := directed_of (· ≤ ·) s.greatest t.greatest
  refine ⟨⟨insert c (s.toFinset ∪ t.toFinset), c, by simp, fun x hx ↦ ?_⟩, ?_, ?_⟩
  · simp only [Finset.coe_insert, Finset.coe_union, Set.mem_insert_iff, Set.mem_union,
      Finset.mem_coe] at hx
    rcases hx with rfl | hx | hx
    · exact le_rfl
    · exact (le_greatest hx).trans hsc
    · exact (le_greatest hx).trans htc
  · exact fun x hx ↦ Finset.mem_insert_of_mem (Finset.mem_union_left _ hx)
  · exact fun x hx ↦ Finset.mem_insert_of_mem (Finset.mem_union_right _ hx)

end FinsetWithGreatest

end TauCeti
