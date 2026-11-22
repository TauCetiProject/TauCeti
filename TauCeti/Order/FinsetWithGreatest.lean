/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.Interval
public import Mathlib.Order.Cofinal

/-!
# Finite subsets with a greatest element

For a preorder `α`, `TauCeti.FinsetWithGreatest α` is the type of finite subsets of `α` that
have a greatest element, partially ordered by inclusion. Every element of it has only finitely
many elements below it, namely the subsets of a finite set that are again in the type, so it is
a locally finite order with respect to lower intervals (`LocallyFiniteOrderBot`): it is
*cofinite* in the sense of pro-homotopy theory. Choosing a greatest element gives a monotone
map `FinsetWithGreatest.greatest` to `α` with cofinal range, and when `α` is directed so is
`FinsetWithGreatest α`.

Together with Deligne's theorem that every filtered category receives a final functor from a
directed poset, this replaces any filtered or cofiltered indexing category by a cofinite directed
poset, which is what inductive constructions over predecessor sets (matching objects of
pro-objects, for instance) require.

## Main definitions and results

* `TauCeti.FinsetWithGreatest α`: finite subsets of `α` with a greatest element.
* `TauCeti.FinsetWithGreatest.greatest`: a chosen greatest element, a monotone map to `α`.
* `TauCeti.FinsetWithGreatest.isCofinal_range_greatest`: its range is cofinal.
* instances: `FinsetWithGreatest α` is a partial order with finite lower intervals,
  directed when `α` is, and nonempty when `α` is.

## References

* D. A. Edwards and H. M. Hastings, *Čech and Steenrod homotopy theories with applications to
  geometric topology*, Lecture Notes in Mathematics 542, §2.1.
* D. C. Isaksen, *A model structure on the category of pro-simplicial sets*, Trans. Amer. Math.
  Soc. 353 (2001), §2.
-/

public section

namespace TauCeti

variable (α : Type*) [Preorder α]

/-- The finite subsets of `α` that have a greatest element, ordered by inclusion. The body is
exposed because the compiler must see that this type is a subtype in importing modules. -/
@[expose]
def FinsetWithGreatest : Type _ := {s : Finset α // ∃ a, IsGreatest (s : Set α) a}

namespace FinsetWithGreatest

variable {α}

instance : PartialOrder (FinsetWithGreatest α) :=
  inferInstanceAs (PartialOrder {s : Finset α // ∃ a, IsGreatest (s : Set α) a})

/-- The underlying finite set. -/
def toFinset (s : FinsetWithGreatest α) : Finset α := Subtype.val s

/-- The element of `FinsetWithGreatest α` given by a finite set with a greatest element. -/
def mk (s : Finset α) (h : ∃ a, IsGreatest (s : Set α) a) : FinsetWithGreatest α :=
  Subtype.mk s h

@[simp]
theorem toFinset_mk (s : Finset α) (h : ∃ a, IsGreatest (s : Set α) a) :
    (mk s h).toFinset = s := (rfl)

theorem exists_isGreatest (s : FinsetWithGreatest α) :
    ∃ a, IsGreatest (s.toFinset : Set α) a :=
  Subtype.property s

theorem toFinset_injective : Function.Injective (toFinset (α := α)) :=
  Subtype.val_injective

@[ext]
theorem ext {s t : FinsetWithGreatest α} (h : s.toFinset = t.toFinset) : s = t :=
  toFinset_injective h

theorem le_iff_subset {s t : FinsetWithGreatest α} : s ≤ t ↔ s.toFinset ⊆ t.toFinset :=
  Iff.rfl

/-- A chosen greatest element of a finite set with a greatest element. -/
noncomputable def greatest (s : FinsetWithGreatest α) : α := s.exists_isGreatest.choose

theorem isGreatest_greatest (s : FinsetWithGreatest α) :
    IsGreatest (s.toFinset : Set α) s.greatest :=
  s.exists_isGreatest.choose_spec

theorem greatest_mem (s : FinsetWithGreatest α) : s.greatest ∈ s.toFinset :=
  s.isGreatest_greatest.1

theorem le_greatest {s : FinsetWithGreatest α} {a : α} (ha : a ∈ s.toFinset) :
    a ≤ s.greatest :=
  s.isGreatest_greatest.2 ha

/-- In a partial order the greatest element is the unique one. -/
theorem greatest_eq {α : Type*} [PartialOrder α] {s : FinsetWithGreatest α} {a : α}
    (h : IsGreatest (s.toFinset : Set α) a) : s.greatest = a :=
  s.isGreatest_greatest.unique h

/-- Inclusion of finite sets with greatest elements raises the greatest element. -/
theorem greatest_mono : Monotone (greatest (α := α)) :=
  fun _ _ hst ↦ le_greatest (le_iff_subset.1 hst (greatest_mem _))

/-- The singleton finite set, whose greatest element is its point. -/
def singleton (a : α) : FinsetWithGreatest α :=
  mk {a} ⟨a, by simp⟩

@[simp]
theorem toFinset_singleton (a : α) : (singleton a).toFinset = {a} := (rfl)

theorem le_greatest_singleton (a : α) : a ≤ (singleton a).greatest :=
  le_greatest (by simp)

@[simp]
theorem greatest_singleton {α : Type*} [PartialOrder α] (a : α) : (singleton a).greatest = a :=
  greatest_eq (by simp)

/-- The range of `greatest` is cofinal: every element lies below the greatest element of its
singleton. -/
theorem isCofinal_range_greatest : IsCofinal (Set.range (greatest (α := α))) :=
  fun a ↦ ⟨_, Set.mem_range_self (singleton a), le_greatest_singleton a⟩

instance [Nonempty α] : Nonempty (FinsetWithGreatest α) :=
  ‹Nonempty α›.map singleton

/-- Every element has finitely many elements below it: those below `s` are among the subsets of
the finite set `s.toFinset`. -/
noncomputable instance : LocallyFiniteOrderBot (FinsetWithGreatest α) := by
  classical
  exact inferInstanceAs (LocallyFiniteOrderBot {s : Finset α // ∃ a, IsGreatest (s : Set α) a})

/-- Two finite sets with greatest elements both lie in the union with an upper bound of their
greatest elements adjoined, whose greatest element is that upper bound. -/
instance [IsDirected α (· ≤ ·)] : IsDirected (FinsetWithGreatest α) (· ≤ ·) where
  directed s t := by
    classical
    obtain ⟨c, hsc, htc⟩ := directed_of (· ≤ ·) s.greatest t.greatest
    refine ⟨mk (insert c (s.toFinset ∪ t.toFinset)) ⟨c, by simp, ?_⟩, ?_, ?_⟩
    · intro b hb
      simp only [Finset.coe_insert, Finset.coe_union, Set.mem_insert_iff, Set.mem_union,
        Finset.mem_coe] at hb
      rcases hb with rfl | hb | hb
      · exact le_rfl
      · exact (le_greatest hb).trans hsc
      · exact (le_greatest hb).trans htc
    · exact le_iff_subset.2 fun x hx ↦ by simp [hx]
    · exact le_iff_subset.2 fun x hx ↦ by simp [hx]

end FinsetWithGreatest

end TauCeti
