/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Presentable.Directed
public import TauCeti.CategoryTheory.Countable

/-!
# Countability of Deligne's finite diagrams

The finite diagrams in Mathlib's formalization of Deligne's directed presentation (SGA 4,
Exposé I, 8.1.6) form a countable type when the ambient category is countable. Each diagram
is determined by its finite sets of objects and arrows. A unique terminal object adds no
further choice, so the poset of finite diagrams with a unique terminal object is countable too.
-/

public section

open CategoryTheory IsCardinalFiltered.exists_cardinal_directed

namespace TauCeti

/-- There are only countably many finite diagrams of objects and arrows in a countable
category. -/
instance instCountableDiagram (J : Type*) [SmallCategory J] [CountableCategory J] :
    Countable (Diagram J Cardinal.aleph0) := by
  let support (D : Diagram J Cardinal.aleph0) := (D.W.toSet, Set.ofPred D.P)
  rw [← Set.countable_univ_iff]
  apply Set.MapsTo.countable_of_injOn (f := support) _ _
    (Set.Countable.ofPred_finite.prod Set.Countable.ofPred_finite)
  · intro D _
    exact ⟨Set.finite_coe_iff.mp ((hasCardinalLT_aleph0_iff _).mp D.hW),
      Set.finite_coe_iff.mp ((hasCardinalLT_aleph0_iff _).mp D.hP)⟩
  · intro D _ E _ h
    obtain ⟨hW, hP⟩ := Prod.mk.inj h
    apply Diagram.ext
    · ext X Y f
      simpa only [MorphismProperty.arrow_mk_mem_toSet_iff] using Set.ext_iff.mp hW (Arrow.mk f)
    · exact Set.ofPred_injective hP

/-- The poset of Deligne diagrams with a unique terminal object is countable when the ambient
category is countable and the diagrams are finite. -/
instance instCountableDiagramWithUniqueTerminal (J : Type*) [SmallCategory J]
    [CountableCategory J] : Countable (DiagramWithUniqueTerminal J Cardinal.aleph0) := by
  refine Function.Injective.countable (f := DiagramWithUniqueTerminal.toDiagram) fun D E h ↦ ?_
  exact DiagramWithUniqueTerminal.ext J _ (congrArg Diagram.W h) (congrArg Diagram.P h)

end TauCeti
