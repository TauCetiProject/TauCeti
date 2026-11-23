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
opposite of a cofinite directed partial order.

Diagrams over a cofiltered category may thus be restricted to cofinite directed index sets
without changing their limits, which is how pro-objects are presented in inductive
constructions over finitely many predecessors.

## Main results

* `TauCeti.IsFiltered.exists_cofinite_directed`: a small filtered category receives a final
  functor from a cofinite directed partial order.
* `TauCeti.IsCofiltered.exists_cofinite_directed`: a small cofiltered category receives an
  initial functor from the opposite of a cofinite directed partial order.

## References

* M. Artin and B. Mazur, *Étale homotopy*, Lecture Notes in Math. 100, Appendix, §2.
* D. Isaksen, *A model structure on the category of pro-simplicial sets*, Trans. Amer. Math.
  Soc. 353 (2001), §2.
-/

public section

open CategoryTheory

universe w

namespace TauCeti

/-- **Cofinite directed presentations.** A small filtered category receives a final functor
from a nonempty directed partial order in the same universe in which every element has only
finitely many elements below it. -/
theorem IsFiltered.exists_cofinite_directed (J : Type w) [SmallCategory J] [IsFiltered J] :
    ∃ (α : Type w) (_ : PartialOrder α) (_ : IsDirected α (· ≤ ·)) (_ : Nonempty α)
      (_ : ∀ a : α, (Set.Iic a).Finite) (F : α ⥤ J), F.Final := by
  obtain ⟨β, _, _, _, F, _⟩ := CategoryTheory.IsFiltered.exists_directed J
  have := (FinsetWithGreatest.greatest_monotone (α := β)).final_functor_iff.2 fun b ↦
    Set.exists_range_iff.mp (FinsetWithGreatest.isCofinal_range_greatest b)
  exact ⟨FinsetWithGreatest β, inferInstance, inferInstance, inferInstance,
    FinsetWithGreatest.finite_Iic, FinsetWithGreatest.greatest_monotone.functor ⋙ F,
    inferInstance⟩

/-- **Cofinite directed presentations, cofiltered form.** A small cofiltered category receives
an initial functor from the opposite of a nonempty directed partial order in the same universe
in which every element has only finitely many elements below it. -/
theorem IsCofiltered.exists_cofinite_directed (I : Type w) [SmallCategory I] [IsCofiltered I] :
    ∃ (α : Type w) (_ : PartialOrder α) (_ : IsDirected α (· ≤ ·)) (_ : Nonempty α)
      (_ : ∀ a : α, (Set.Iic a).Finite) (G : αᵒᵖ ⥤ I), G.Initial := by
  obtain ⟨α, _, _, _, hα, F, _⟩ := IsFiltered.exists_cofinite_directed Iᵒᵖ
  exact ⟨α, inferInstance, inferInstance, inferInstance, hα, F.leftOp, inferInstance⟩

end TauCeti
