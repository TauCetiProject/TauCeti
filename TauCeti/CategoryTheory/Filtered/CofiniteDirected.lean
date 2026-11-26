/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Presentable.Directed
public import TauCeti.Order.CofiniteDirected

/-!
# Cofinite directed presentations of filtered categories

Mathlib's `CategoryTheory.IsFiltered.exists_directed` presents a small filtered category by a
final functor from a directed partial order. Precomposing with the cofinite refinement
`TauCeti.FinsetWithGreatest` of that order, which is final by `Monotone.final_functor_iff`,
every small filtered category receives a final functor from a cofinite directed partial order
in the same universe. Dually, every small cofiltered category receives an initial functor from the
opposite of a cofinite directed partial order. Cofiniteness is expressed by Mathlib's
`LocallyFiniteOrderBot`: every element has only finitely many elements below it.

Diagrams over a cofiltered category may thus be restricted to cofinite directed index sets
without changing their limits, which is how pro-objects are presented in inductive
constructions over finitely many predecessors.

## Main results

* `TauCeti.FinsetWithGreatest.greatestFunctor`: the greatest-element functor, final when the
  order is directed (`TauCeti.FinsetWithGreatest.final_greatestFunctor`).
* `TauCeti.IsFiltered.exists_cofinite_directed`: a small filtered category receives a final
  functor from a cofinite directed partial order.
* `TauCeti.IsCofiltered.exists_cofinite_directed`: a small cofiltered category receives an
  initial functor from the opposite of a cofinite directed partial order.

## References

* A. Grothendieck and J.-L. Verdier, *Exposé I : Préfaisceaux*, SGA 4, I 8.1.6.
* D. A. Edwards and H. M. Hastings, *Čech and Steenrod homotopy theories with applications to
  geometric topology*, Lecture Notes in Mathematics 542, §2.1.
* M. Artin and B. Mazur, *Étale homotopy*, Lecture Notes in Math. 100, Appendix, §2.
* D. Isaksen, *A model structure on the category of pro-simplicial sets*, Trans. Amer. Math.
  Soc. 353 (2001), §2.
-/

public section

open CategoryTheory

universe w

namespace TauCeti

namespace FinsetWithGreatest

variable (α : Type*) [Preorder α]

/-- The greatest-element map as a functor between the poset categories. -/
noncomputable def greatestFunctor : FinsetWithGreatest α ⥤ α :=
  greatest_monotone.functor

@[simp]
theorem greatestFunctor_obj (s : FinsetWithGreatest α) :
    (greatestFunctor α).obj s = s.greatest := (rfl)

/-- For directed `α`, the greatest-element functor is final, since its range is cofinal. -/
instance final_greatestFunctor [IsDirected α (· ≤ ·)] : (greatestFunctor α).Final :=
  greatest_monotone.final_functor_iff.2 fun a ↦ ⟨singleton a, (greatest_singleton a).ge⟩

end FinsetWithGreatest

/-- **Cofinite directed presentations.** A small filtered category receives a final functor
from a nonempty directed partial order in the same universe in which every element has only
finitely many elements below it. -/
theorem IsFiltered.exists_cofinite_directed (J : Type w) [SmallCategory J] [IsFiltered J] :
    ∃ (α : Type w) (_ : PartialOrder α) (_ : LocallyFiniteOrderBot α)
      (_ : IsDirected α (· ≤ ·)) (_ : Nonempty α) (F : α ⥤ J), F.Final := by
  obtain ⟨β, _, _, _, F, _⟩ := CategoryTheory.IsFiltered.exists_directed J
  exact ⟨FinsetWithGreatest β, inferInstance, inferInstance, inferInstance, inferInstance,
    FinsetWithGreatest.greatestFunctor β ⋙ F, inferInstance⟩

/-- **Cofinite directed presentations, cofiltered form.** A small cofiltered category receives
an initial functor from the opposite of a nonempty directed partial order in the same universe
in which every element has only finitely many elements below it. Precomposing a cofiltered
diagram with this functor gives a presentation of the same limit indexed by a cofinite directed
poset. -/
theorem IsCofiltered.exists_cofinite_directed (I : Type w) [SmallCategory I] [IsCofiltered I] :
    ∃ (α : Type w) (_ : PartialOrder α) (_ : LocallyFiniteOrderBot α)
      (_ : IsDirected α (· ≤ ·)) (_ : Nonempty α) (G : αᵒᵖ ⥤ I), G.Initial := by
  obtain ⟨α, _, _, _, _, F, _⟩ := IsFiltered.exists_cofinite_directed Iᵒᵖ
  exact ⟨α, inferInstance, inferInstance, inferInstance, inferInstance, F.leftOp, inferInstance⟩

end TauCeti
