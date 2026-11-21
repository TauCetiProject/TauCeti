/-
Copyright (c) 2026 Vincent Quenneville-Belair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Quenneville-Belair
-/
module

public import Mathlib.CategoryTheory.Presentable.Directed

/-!
# A cofiltered preorder over a cofiltered category

Dualizing Mathlib's directed-poset construction gives an initial functor from a
cofiltered preorder to any cofiltered category, with explicit universe bounds.
-/

public section

universe u v

namespace CategoryTheory

open Limits

/-- Every cofiltered category admits an initial functor from a cofiltered preorder. -/
@[stacks 0032 "(2)"]
lemma Limits.IsCofiltered.preorder_of_cofiltered
    (J : Type u) [Category.{v} J] [IsCofiltered J] :
    ∃ (I : Type (max u v)) (_ : Preorder I) (_ : IsCofiltered I) (F : I ⥤ J), F.Initial := by
  obtain ⟨α, _, _, _, F, _⟩ := IsFiltered.exists_directed (AsSmall.{max u v} J)ᵒᵖ
  exact ⟨αᵒᵈ, inferInstance, inferInstance,
    (orderDualEquivalence α).functor ⋙ F.leftOp ⋙ AsSmall.equiv.inverse, inferInstance⟩

end CategoryTheory
