/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Presentable.Directed
public import TauCeti.Order.FinsetWithGreatest

/-!
# Cofinite directed reindexing of filtered and cofiltered categories

A directed poset is *cofinite* if every element has only finitely many elements below it;
in Mathlib's language it is a `LocallyFiniteOrderBot`. This file shows that every small filtered
category `J` receives a final functor from a nonempty cofinite directed poset in the same
universe, and dually that every small cofiltered category `I` receives an initial functor from
the opposite of one. Reindexing a cofiltered diagram along such an initial functor therefore
presents the same limit, or the same pro-object, by a diagram indexed by a cofinite directed
poset: the indexing used for inductive constructions over finite predecessor sets, such as the
matching objects of pro-simplicial sets.

The proof composes Deligne's theorem `CategoryTheory.IsFiltered.exists_directed`, which provides
a final functor from a directed poset `α`, with the monotone map
`TauCeti.FinsetWithGreatest.greatest` from the cofinite directed poset of finite subsets of `α`
having a greatest element, which is final because its range is cofinal.

## Main results

* `TauCeti.FinsetWithGreatest.greatestFunctor`: the greatest-element functor, final when `α` is
  directed (`TauCeti.FinsetWithGreatest.final_greatestFunctor`).
* `CategoryTheory.IsFiltered.exists_cofinite_directed`: a small filtered category receives a final
  functor from a nonempty cofinite directed poset.
* `CategoryTheory.IsCofiltered.exists_cofinite_directed`: a small cofiltered category receives an
  initial functor from the opposite of a nonempty cofinite directed poset.

## References

* A. Grothendieck and J.-L. Verdier, *Exposé I : Préfaisceaux*, SGA 4, I 8.1.6.
* D. A. Edwards and H. M. Hastings, *Čech and Steenrod homotopy theories with applications to
  geometric topology*, Lecture Notes in Mathematics 542, §2.1.
* D. C. Isaksen, *A model structure on the category of pro-simplicial sets*, Trans. Amer. Math.
  Soc. 353 (2001), §2.
-/

public section

open CategoryTheory

universe w

namespace TauCeti.FinsetWithGreatest

variable (α : Type*) [Preorder α]

/-- The greatest-element map as a functor between the poset categories. -/
noncomputable def greatestFunctor : FinsetWithGreatest α ⥤ α :=
  greatest_mono.functor

@[simp]
theorem greatestFunctor_obj (s : FinsetWithGreatest α) :
    (greatestFunctor α).obj s = s.greatest := (rfl)

/-- For directed `α`, the greatest-element functor is final, since its range is cofinal. -/
instance final_greatestFunctor [IsDirected α (· ≤ ·)] : (greatestFunctor α).Final :=
  Functor.final_of_exists_of_isFiltered _
    (fun a ↦ ⟨singleton a, ⟨homOfLE (le_greatest_singleton a)⟩⟩)
    (fun {_ s} _ _ ↦ ⟨s, 𝟙 s, Subsingleton.elim _ _⟩)

end TauCeti.FinsetWithGreatest

namespace CategoryTheory

open TauCeti

/-- **Cofinite directed reindexing of a filtered category.** Every small filtered category
receives a final functor from a nonempty directed poset, in the same universe, in which every
element has only finitely many elements below it. -/
theorem IsFiltered.exists_cofinite_directed (J : Type w) [SmallCategory J] [IsFiltered J] :
    ∃ (α : Type w) (_ : PartialOrder α) (_ : LocallyFiniteOrderBot α)
      (_ : IsDirected α (· ≤ ·)) (_ : Nonempty α) (F : α ⥤ J), F.Final := by
  obtain ⟨β, _, _, _, F, _⟩ := IsFiltered.exists_directed J
  exact ⟨FinsetWithGreatest β, inferInstance, inferInstance, inferInstance, inferInstance,
    FinsetWithGreatest.greatestFunctor β ⋙ F, inferInstance⟩

/-- **Cofinite directed reindexing of a cofiltered category.** Every small cofiltered category
receives an initial functor from the opposite of a nonempty directed poset, in the same universe,
in which every element has only finitely many elements below it. Precomposing a cofiltered
diagram with this functor gives a presentation of the same limit indexed by a cofinite directed
poset. -/
theorem IsCofiltered.exists_cofinite_directed (I : Type w) [SmallCategory I] [IsCofiltered I] :
    ∃ (α : Type w) (_ : PartialOrder α) (_ : LocallyFiniteOrderBot α)
      (_ : IsDirected α (· ≤ ·)) (_ : Nonempty α) (G : αᵒᵖ ⥤ I), G.Initial := by
  obtain ⟨α, _, _, _, _, F, _⟩ := IsFiltered.exists_cofinite_directed Iᵒᵖ
  exact ⟨α, inferInstance, inferInstance, inferInstance, inferInstance, F.leftOp, inferInstance⟩

end CategoryTheory
