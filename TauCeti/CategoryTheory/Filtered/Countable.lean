/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.CategoryTheory.Presentable.Directed
public import TauCeti.CategoryTheory.Countable

/-!
# Sequential presentations of countable cofiltered categories

Every countable cofiltered category admits an initial functor from the opposite of the natural
numbers. By `Functor.Initial.limitIso`, its inverse limits can be computed over towers. This
is the countable step of the cardinal induction for limits of diamonds in Scholze's *Étale
cohomology of diamonds*, Lemma 11.22. Countability can be tested on the total arrow type by
`Arrow.countable_iff`. Dually, every countable filtered category admits a final sequence.

We use Deligne's directed presentation of a filtered category (SGA 4, Exposé I, 8.1.6), as
formalized in `Mathlib.CategoryTheory.Presentable.Directed`. For a countable category the finite
diagrams with a unique terminal object form a countable poset, even in the presence of parallel
arrows. Mathlib's `Limits.IsFiltered.sequentialFunctor` gives a final sequence in that poset.
-/

public section

namespace CategoryTheory

namespace IsCardinalFiltered.exists_cardinal_directed

/-- There are only countably many finite diagrams of objects and arrows in a countable
category. -/
instance Diagram.instCountable (J : Type*) [SmallCategory J] [CountableCategory J] :
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
instance DiagramWithUniqueTerminal.instCountable (J : Type*) [SmallCategory J]
    [CountableCategory J] : Countable (DiagramWithUniqueTerminal J Cardinal.aleph0) := by
  refine Function.Injective.countable (f := DiagramWithUniqueTerminal.toDiagram) fun D E h ↦ ?_
  exact DiagramWithUniqueTerminal.ext J _ (congrArg Diagram.W h) (congrArg Diagram.P h)

end IsCardinalFiltered.exists_cardinal_directed

open IsCardinalFiltered.exists_cardinal_directed in
/-- A countable filtered category admits a final sequence. -/
theorem IsFiltered.exists_final_nat (J : Type*) [Category* J] [CountableCategory J]
    [IsFiltered J] : ∃ F : ℕ ⥤ J, F.Final := by
  let K := CountableCategory.HomAsType J
  let e := CountableCategory.homAsTypeEquiv J
  have : IsFiltered K := IsFiltered.of_equivalence e.symm
  -- The extra natural-number coordinate gives each object a strict successor, as required by
  -- Deligne's presentation. Projection back to K is final.
  let L := K × ℕ
  have := Cardinal.fact_isRegular_aleph0.{0}
  have : IsCardinalFiltered L Cardinal.aleph0 := (isCardinalFiltered_aleph0_iff L).2 inferInstance
  have hL (x : L) : ∃ (y : L) (_ : x ⟶ y), IsEmpty (y ⟶ x) :=
    ⟨(x.1, x.2 + 1), (𝟙 _, homOfLE (Nat.le_succ _)),
      ⟨fun f ↦ Nat.not_succ_le_self _ (leOfHom f.2)⟩⟩
  let P := DiagramWithUniqueTerminal L Cardinal.aleph0
  have : IsCardinalFiltered P Cardinal.aleph0 := isCardinalFiltered L _ hL
  have : IsFiltered P := isFiltered_of_isCardinalFiltered P Cardinal.aleph0
  have : (functor L Cardinal.aleph0).Final := final_functor L _ hL
  exact ⟨Limits.IsFiltered.sequentialFunctor P ⋙ functor L _ ⋙ Prod.fst K ℕ ⋙ e.functor,
    inferInstance⟩

/-- A countable cofiltered category admits an initial tower. Restricting a diagram along this
functor computes its limit over the original category. -/
theorem IsCofiltered.exists_initial_nat_op (J : Type*) [Category* J] [CountableCategory J]
    [IsCofiltered J] : ∃ F : ℕᵒᵖ ⥤ J, F.Initial := by
  obtain ⟨F, _⟩ := IsFiltered.exists_final_nat Jᵒᵖ
  exact ⟨F.leftOp, inferInstance⟩

end CategoryTheory
