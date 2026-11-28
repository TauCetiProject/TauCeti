/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialSet.Nerve.Basic
public import TauCeti.AlgebraicTopology.SimplicialSet.PiZero
public import TauCeti.CategoryTheory.ConnectedComponents

/-!
# Connected components of the nerve of a category

The `0`- and `1`-simplices of `nerve C` are the objects and morphisms of `C`, so the vertex
equivalence relation defining `SSet.π₀ (nerve C)` agrees with the zigzag relation defining
`CategoryTheory.ConnectedComponents C`. This file constructs the natural equivalence
`CategoryTheory.nerve.π₀EquivConnectedComponents` and proves `CategoryTheory.nerve.isConnected_iff`,
which together with `SSet.π₀EquivZerothHomotopy` identify the path components of `|nerve C|` with
`ConnectedComponents C`.
-/

public section

open Opposite Simplicial
universe v u
namespace CategoryTheory.nerve
section
variable (C : Type u) [Category.{v} C]
/-- The connected components of `nerve C` correspond naturally to `ConnectedComponents C`. -/
def π₀EquivConnectedComponents : SSet.π₀ (nerve C) ≃ ConnectedComponents C where
  toFun := SSet.π₀.lift (fun x ↦ ConnectedComponents.mk (nerveEquiv x))
    (fun _ _ e ↦ _root_.Quotient.sound (Zigzag.of_hom (homEquiv e)))
  invFun := _root_.Quotient.lift (fun c ↦ SSet.π₀.mk (X := nerve C) (nerveEquiv.symm c))
    fun _ _ (h : Zigzag _ _) ↦ by
      induction h with
      | refl => rfl
      | tail _ hzag ih =>
        exact hzag.rec (fun ⟨f⟩ ↦ ih.trans (SSet.π₀.sound (edgeMk f)))
          fun ⟨f⟩ ↦ ih.trans (SSet.π₀.sound (edgeMk f)).symm
  left_inv := SSet.π₀.rec fun x ↦
    congrArg (SSet.π₀.mk (X := nerve C)) (Equiv.symm_apply_apply nerveEquiv x)
  right_inv := _root_.Quotient.ind fun c ↦
    congrArg ConnectedComponents.mk (Equiv.apply_symm_apply nerveEquiv c)
@[simp] lemma π₀EquivConnectedComponents_mk (x : (nerve C) _⦋0⦌) :
    π₀EquivConnectedComponents C (SSet.π₀.mk x) = ConnectedComponents.mk (nerveEquiv x) := (rfl)
@[simp] lemma π₀EquivConnectedComponents_mk_nerveEquiv_symm (c : C) :
    π₀EquivConnectedComponents C (SSet.π₀.mk (X := nerve C) (nerveEquiv.symm c)) =
      ConnectedComponents.mk c :=
  (π₀EquivConnectedComponents_mk C (nerveEquiv.symm c : (nerve C) _⦋0⦌)).trans
    (congrArg ConnectedComponents.mk (Equiv.apply_symm_apply nerveEquiv c))
@[simp] lemma π₀EquivConnectedComponents_symm_mk (c : C) :
    (π₀EquivConnectedComponents C).symm (ConnectedComponents.mk c) =
      SSet.π₀.mk (X := nerve C) (nerveEquiv.symm c) := (rfl)
/-- `nerve C` is connected as a simplicial set if and only if `C` is a connected category. -/
@[simp] lemma isConnected_iff : (nerve C).IsConnected ↔ CategoryTheory.IsConnected C := by
  rw [SSet.isConnected_iff_nonempty_unique, ← nonempty_unique_connectedComponents_iff]
  exact ⟨fun ⟨_⟩ ↦ ⟨(π₀EquivConnectedComponents C).symm.unique⟩,
    fun ⟨_⟩ ↦ ⟨(π₀EquivConnectedComponents C).unique⟩⟩
instance [CategoryTheory.IsConnected C] : (nerve C).IsConnected := (isConnected_iff C).2 ‹_›
end
@[simp] lemma π₀EquivConnectedComponents_mapπ₀_nerveMap {C D : Type u} [Category.{v} C]
    [Category.{v} D] (F : C ⥤ D) (z : SSet.π₀ (nerve C)) :
    π₀EquivConnectedComponents D (SSet.mapπ₀ (nerveMap F) z) =
      F.mapConnectedComponents (π₀EquivConnectedComponents C z) := by
  induction z using SSet.π₀.rec with | _ x =>
  have h : (nerveMap F).app (op ⦋0⦌) x = nerveEquiv.symm (F.obj (nerveEquiv x)) := by
    conv_lhs => rw [← Equiv.symm_apply_apply nerveEquiv x]
    exact nerveMap_app_nerveEquiv_symm F (nerveEquiv x)
  rw [SSet.mapπ₀_mk, h, π₀EquivConnectedComponents_mk_nerveEquiv_symm,
    π₀EquivConnectedComponents_mk, Functor.mapConnectedComponents_mk]
end CategoryTheory.nerve
