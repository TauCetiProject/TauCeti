/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import TauCeti.CategoryTheory.Presentable.Directed

import TauCeti.CategoryTheory.Products.Basic

/-!
# Sequential presentations of countable cofiltered categories

Every countable cofiltered category admits an initial functor from the opposite of the natural
numbers. By `Functor.Initial.limitIso`, its inverse limits can be computed over towers. This
is the countable step of the cardinal induction for limits of diamonds in Scholze's *Étale
cohomology of diamonds*, Lemma 11.22. Countability can be tested on the total arrow type by
`TauCeti.countable_arrow_iff`. The chosen `TauCeti.Cofiltered.countableSequence` is the identity
on `ℕᵒᵖ`. Dually, every countable filtered category admits a final sequence.

We use Deligne's directed presentation of a filtered category (SGA 4, Exposé I, 8.1.6), as
formalized in `Mathlib.CategoryTheory.Presentable.Directed`. For a countable category the finite
diagrams with a unique terminal object form a countable poset, even in the presence of parallel
arrows. To make this poset directed, we first add a natural-number coordinate to the ambient
category, giving each object a strict successor. This specializes the product-and-projection
argument of `IsCardinalFiltered.exists_cardinal_directed` to a natural-number coordinate.
Mathlib's `Limits.IsFiltered.sequentialFunctor` gives a final sequence in the resulting directed
poset, and the projection back to the original category preserves finality.
-/

public section

open CategoryTheory

namespace TauCeti

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
    ⟨(x.1, x.2 + 1), Prod.mkHom (𝟙 _) (homOfLE (Nat.le_succ _)),
      ⟨fun f ↦ Nat.not_succ_le_self _ (leOfHom f.2)⟩⟩
  let P := DiagramWithUniqueTerminal L Cardinal.aleph0
  have : IsCardinalFiltered P Cardinal.aleph0 := isCardinalFiltered L _ hL
  have : IsFiltered P := isFiltered_of_isCardinalFiltered P Cardinal.aleph0
  have : (functor L Cardinal.aleph0).Final := final_functor L _ hL
  exact ⟨Limits.IsFiltered.sequentialFunctor P ⋙ functor L _ ⋙ CategoryTheory.Prod.fst K ℕ ⋙
    e.functor, inferInstance⟩

/-- A countable cofiltered category admits an initial tower. Restricting a diagram along this
functor computes its limit over the original category. -/
theorem IsCofiltered.exists_initial_nat_op (J : Type*) [Category* J] [CountableCategory J]
    [IsCofiltered J] : ∃ F : ℕᵒᵖ ⥤ J, F.Initial := by
  obtain ⟨F, _⟩ := IsFiltered.exists_final_nat Jᵒᵖ
  exact ⟨F.leftOp, inferInstance⟩

namespace Cofiltered

/-- A chosen initial tower in a countable cofiltered category. On `ℕᵒᵖ` it is the identity. -/
noncomputable def countableSequence (J : Type*) [Category* J] [CountableCategory J]
    [IsCofiltered J] : ℕᵒᵖ ⥤ J := by
  classical
  exact if h : Nonempty (ℕᵒᵖ ≌ J) then h.some.functor
    else (IsCofiltered.exists_initial_nat_op J).choose

/-- The chosen countable tower is initial. -/
instance countableSequence_initial (J : Type*) [Category* J] [CountableCategory J]
    [IsCofiltered J] : (countableSequence J).Initial := by
  classical
  unfold countableSequence
  split
  · infer_instance
  · exact (IsCofiltered.exists_initial_nat_op J).choose_spec

/-- The chosen tower on the opposite of the natural-number category fixes every stage. -/
@[simp]
theorem countableSequence_nat : countableSequence (ℕᵒᵖ) = 𝟭 (ℕᵒᵖ) := by
  classical
  unfold countableSequence
  have e : Nonempty (ℕᵒᵖ ≌ ℕᵒᵖ) := ⟨CategoryTheory.Equivalence.refl⟩
  rw [dite_eq_left e]
  -- A well-order has only the identity order automorphism.
  have h : e.some.unop.toOrderIso = OrderIso.refl ℕ := Subsingleton.elim _ _
  refine CategoryTheory.Functor.ext (fun n ↦ ?_) (fun _ _ _ ↦ Subsingleton.elim _ _)
  apply Opposite.unop_injective
  simpa only [Equivalence.toOrderIso_apply, Equivalence.unop_functor, Functor.unop_obj,
    Opposite.op_unop, Functor.id_obj, OrderIso.refl_apply] using
    congrArg (fun o : ℕ ≃o ℕ ↦ o n.unop) h

end Cofiltered

end TauCeti
