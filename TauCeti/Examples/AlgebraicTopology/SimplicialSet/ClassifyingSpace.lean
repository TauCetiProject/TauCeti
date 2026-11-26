/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Algebra.Group.PUnit
import Mathlib.CategoryTheory.Limits.Preorder
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Cospan
import Mathlib.CategoryTheory.SingleObj
import TauCeti.AlgebraicTopology.SimplicialSet.Nerve.ClassifyingSpace
import TauCeti.AlgebraicTopology.SimplicialSet.Nerve.WeaklyContractible

/-!
# Examples of classifying spaces of categories

Small examples and typeclass-synthesis checks for `CategoryTheory.classifyingSpace`: distinct
vertices in `Discrete Bool`, non-constancy and endpoint retractions on `Fin 2`, non-contractibility
of empty categories, zigzags in `Limits.WalkingCospan`, and automatic synthesis of
`ContractibleSpace`, `SSet.IsWeaklyContractible`, and `Unique` on bounded preorders and thin
one-object categories.
-/

open CategoryTheory TauCeti.CategoryTheory TauCeti.CategoryTheory.classifyingSpace

example : vertex (⟨true⟩ : Discrete Bool) ≠ vertex ⟨false⟩ :=
  fun h ↦ Bool.noConfusion (Discrete.ext_iff.1 (vertex_injective h))
example (b : Fin 2) :
    (𝟭 (Fin 2)).classifyingSpaceMap ≠ ((Functor.const (Fin 2)).obj b).classifyingSpaceMap := by
  intro h
  have hb := vertex_injective <| by simpa using ConcreteCategory.congr_hom h (vertex (1 - b))
  fin_cases b <;> exact absurd hb (by decide)
example (b : Fin 2) :
    (((Functor.const (Discrete PUnit.{1})).obj b) ⋙
        ((Functor.const (Fin 2)).obj ⟨PUnit.unit⟩)).classifyingSpaceMap =
        𝟙 (classifyingSpace (Discrete PUnit.{1})) ∧
    (((Functor.const (Fin 2)).obj ⟨PUnit.unit⟩) ⋙
        ((Functor.const (Discrete PUnit.{1})).obj b)).classifyingSpaceMap =
      ((Functor.const (Fin 2)).obj b).classifyingSpaceMap := by
  have hcomp : ((Functor.const (Discrete PUnit.{1})).obj b) ⋙
      ((Functor.const (Fin 2)).obj ⟨PUnit.unit⟩) = 𝟭 (Discrete PUnit.{1}) :=
    CategoryTheory.Functor.ext (fun ⟨⟨⟩⟩ ↦ rfl) fun ⟨⟨⟩⟩ ⟨⟨⟩⟩ _ ↦ Subsingleton.elim _ _
  exact ⟨by rw [hcomp, Functor.classifyingSpaceMap_id], rfl⟩
example (C : Type*) [Category* C] [IsEmpty C] : ¬ ContractibleSpace (classifyingSpace C) := fun _ ↦
  let ⟨e⟩ := ContractibleSpace.hequiv_unit (classifyingSpace C); IsEmpty.false (e.invFun ())
example :
    IsEmpty (Limits.WalkingCospan.left ⟶ Limits.WalkingCospan.right) ∧
    IsEmpty (Limits.WalkingCospan.right ⟶ Limits.WalkingCospan.left) ∧
    Joined (vertex Limits.WalkingCospan.left) (vertex Limits.WalkingCospan.right) :=
  ⟨⟨nofun⟩, ⟨nofun⟩,
    ⟨(edge Limits.WalkingCospan.Hom.inl).trans (edge Limits.WalkingCospan.Hom.inr).symm⟩⟩
example (n : ℕ) : ContractibleSpace (classifyingSpace (Fin (n + 1))) := inferInstance
example (n : ℕ) : SSet.IsWeaklyContractible (nerve (Fin (n + 1))) := inferInstance
noncomputable example : Unique (classifyingSpace (Discrete PUnit.{1})) := inferInstance
noncomputable example : Unique (classifyingSpace (Fin 1)) := inferInstance
noncomputable example : Unique (classifyingSpace (SingleObj Unit)) :=
  haveI : Quiver.IsThin (SingleObj Unit) := fun _ _ ↦ inferInstanceAs (Subsingleton Unit)
  inferInstance
