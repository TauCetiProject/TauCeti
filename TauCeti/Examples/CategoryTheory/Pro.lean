/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.CategoryTheory.Pro.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.CategoryTheory.Category.Preorder

/-!
# Checks for pro-objects

Constant finite sets retain their maps, including the asymmetric empty-set cases.
A constant cofiltered Boolean tower recovers the Boolean object, and the map induced
by negation has negation, rather than the identity, on every projection.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TauCeti

-- Fully faithfulness retains all nine functions from a two-element set to a three-element set.
example : Nat.card (Pro.const.obj (Fin 2) ⟶ Pro.const.obj (Fin 3)) = 9 := by
  calc
    _ = Nat.card (Fin 2 → Fin 3) := Nat.card_congr
      (Pro.const.fullyFaithful.homEquiv.symm.trans TypeCat.homEquiv)
    _ = 9 := by simp

-- The empty object has exactly one map to a point, not the other way around.
example : Unique (Pro.const.obj PEmpty ⟶ Pro.const.obj PUnit) := by
  let e : (PEmpty → PUnit) ≃ (Pro.const.obj PEmpty ⟶ Pro.const.obj PUnit) :=
    TypeCat.homEquiv.symm.trans Pro.const.fullyFaithful.homEquiv
  exact e.uniqueCongr inferInstance

example : IsEmpty (Pro.const.obj PUnit ⟶ Pro.const.obj PEmpty) := by
  refine ⟨fun f ↦ ?_⟩
  exact (Pro.const.preimage f PUnit.unit).elim

-- The constant presentation is recovered with its given projections.
example : Pro.mk ((Functor.const ℕᵒᵖ).obj Bool) ≅ Pro.const.obj Bool :=
  Pro.mkConstIso Bool

example (n : ℕᵒᵖ) :
    (Pro.mkConstIso (I := ℕᵒᵖ) Bool).inv ≫
      Pro.π ((Functor.const ℕᵒᵖ).obj Bool) n = 𝟙 _ := by
  simp

-- The lift API is usable without unfolding the presentation cone.
example (c : Cone (((Functor.const ℕᵒᵖ).obj Bool) ⋙ Pro.const)) (n : ℕᵒᵖ) :
    Pro.lift c ≫ Pro.π ((Functor.const ℕᵒᵖ).obj Bool) n = c.π.app n := by
  simp only [Pro.lift_π]

-- The induced map on the tower really has the prescribed nonidentity coordinate.
example (n : ℕᵒᵖ) :
    Pro.lim.map ((Functor.const ℕᵒᵖ).map (↾Bool.not)) ≫
      Pro.π ((Functor.const ℕᵒᵖ).obj Bool) n =
    Pro.π ((Functor.const ℕᵒᵖ).obj Bool) n ≫ Pro.const.map (↾Bool.not) := by
  simp

example : Pro.lim.map ((Functor.const ℕᵒᵖ).map (↾Bool.not)) ≠ 𝟙 _ := by
  intro h
  have heq := congrArg (fun f ↦ f ≫ Pro.π ((Functor.const ℕᵒᵖ).obj Bool) (op 0)) h
  simp only [Pro.lim_map_π, Functor.const_obj_obj, Functor.const_map_app,
    Category.id_comp] at heq
  have hmap : Pro.const.map (↾Bool.not) = 𝟙 (Pro.const.obj Bool) := by
    apply (cancel_epi (Pro.mkConstIso (I := ℕᵒᵖ) Bool).hom).mp
    simpa only [← Pro.π_const Bool (op 0), Category.comp_id] using heq
  have hnot : ↾Bool.not = 𝟙 Bool := by
    apply Pro.const.map_injective
    simpa using hmap
  have := congrArg (fun f : Bool ⟶ Bool ↦ f true) hnot
  simp at this
