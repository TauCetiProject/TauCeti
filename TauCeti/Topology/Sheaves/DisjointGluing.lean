/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Sheaves.SheafCondition.PairwiseIntersections
public import Mathlib.CategoryTheory.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-!
# Gluing sections of sheaves on disjoint opens

Sections of a sheaf with values in a concrete category on two disjoint open sets glue to a section
on their union. The compatibility condition on the intersection is automatic: the sections over
the empty open form a terminal object, which the forgetful functor sends to a one-point type.
This applies in particular to sheaves of commutative rings.
-/

public section

open CategoryTheory Limits Opposite TopologicalSpace

universe w

namespace TopCat.Sheaf

variable {X : TopCat.{w}}

/-- Sections of a sheaf with values in a concrete category on two disjoint opens glue to a section
on their union. -/
theorem exists_section_sup_of_disjoint {C : Type*} [Category* C] {FC : C → C → Type*}
    {CC : C → Type*} [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]
    [PreservesLimitsOfShape WalkingCospan (CategoryTheory.forget C)]
    [PreservesLimit (Functor.empty.{0} C) (CategoryTheory.forget C)]
    (F : X.Sheaf C) {A B : Opens X} (hAB : Disjoint A B) (σ : ToType (F.obj.obj (op A)))
    (ρ : ToType (F.obj.obj (op B))) :
    ∃ τ : ToType (F.obj.obj (op (A ⊔ B))),
      F.obj.map (homOfLE le_sup_left).op τ = σ ∧ F.obj.map (homOfLE le_sup_right).op τ = ρ := by
  have hP := (IsPullback.of_isLimit (F.isLimitPullbackCone A B)).map (CategoryTheory.forget C)
  have hT : Subsingleton ((CategoryTheory.forget C).obj (F.obj.obj (op (A ⊓ B)))) :=
    (Types.isTerminalEquivUnique _ |>.toFun
      ((F.isTerminalOfEqEmpty hAB.eq_bot).isTerminalObj (CategoryTheory.forget C))).instSubsingleton
  exact Types.exists_of_isPullback hP σ ρ (Subsingleton.elim _ _)

end TopCat.Sheaf
