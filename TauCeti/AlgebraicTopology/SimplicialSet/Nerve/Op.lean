/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.AlgebraicTopology.SimplicialSet.Op
public import TauCeti.CategoryTheory.EqToHom

/-!
# The nerve of the opposite category

The nerve of the opposite category `Cᵒᵖ` is the opposite of the nerve of `C`
(`CategoryTheory.nerve.opIso`): an `n`-simplex of `nerve Cᵒᵖ`, a sequence of `n` composable
morphisms of `Cᵒᵖ`, is the same as the reversed sequence of composable morphisms of `C`, which is
an `n`-simplex of `(nerve C)ᵒᵖ`. On simplices it is given by Mathlib's equivalence
`CategoryTheory.ComposableArrows.opEquivalence`. This isomorphism transports results about
terminal vertices of nerves to results about initial vertices of nerves by duality.

## Main definitions

* `CategoryTheory.nerve.opIso C`: the isomorphism `nerve Cᵒᵖ ≅ (nerve C)ᵒᵖ`.

## Main results

* `CategoryTheory.nerve.opIso_hom_app_obj`: the vertex `i` of the image of a simplex `G` of
  `nerve Cᵒᵖ` is the vertex `i.rev` of `G`.
* `CategoryTheory.nerve.opIso_hom_app_map`: the arrow `i ⟶ j` of the image of a simplex `G` of
  `nerve Cᵒᵖ` is the opposite of the arrow `j.rev ⟶ i.rev` of `G`.
* `CategoryTheory.nerve.opIso_inv_app_obj` and `CategoryTheory.nerve.opIso_inv_app_map`: the
  same descriptions for the inverse isomorphism.
* `CategoryTheory.nerve.opIso_hom_app_nerveEquiv_symm`: on vertices, the isomorphism is the
  identification of the objects of `Cᵒᵖ` with those of `C`.
-/

public section

open CategoryTheory Opposite Simplicial

universe v u

namespace CategoryTheory.nerve

variable (C : Type u) [Category.{v} C]

/-- The nerve of the opposite category is the opposite of the nerve: an `n`-simplex of
`nerve Cᵒᵖ`, a sequence of composable morphisms of `Cᵒᵖ`, is the reversed sequence of composable
morphisms of `C`. -/
noncomputable def opIso : nerve Cᵒᵖ ≅ (nerve C).op :=
  NatIso.ofComponents (fun n ↦ Equiv.toIso
    { toFun G := ((ComposableArrows.opEquivalence C _).inverse.obj G).unop
      invFun F := (ComposableArrows.opEquivalence C _).functor.obj (op F)
      -- Reversing the vertices twice is the identity, up to `Fin.rev_rev`.
      left_inv G := ComposableArrows.ext (fun i ↦ congrArg G.obj (Fin.rev_rev i))
        (fun _ _ ↦ Functor.map_homOfLE_eq G (Fin.rev_rev _) (Fin.rev_rev _) _)
      right_inv F := ComposableArrows.ext (fun i ↦ congrArg F.obj (Fin.rev_rev i))
        (fun _ _ ↦ Functor.map_homOfLE_eq F (Fin.rev_rev _) (Fin.rev_rev _) _) })
    (fun _ ↦ by
      ext G
      -- The simplicial operators of `(nerve C)ᵒᵖ` act through `SimplexCategory.rev`, which
      -- conjugates by `Fin.rev`.
      exact ComposableArrows.ext (fun i ↦ congrArg (fun j ↦ unop (G.obj j)) (Fin.rev_rev _).symm)
        (fun _ _ ↦ Functor.unop_map_homOfLE_eq G (Fin.rev_rev _).symm (Fin.rev_rev _).symm _))

/-- The vertex `i` of the image under `opIso` of a simplex `G` of `nerve Cᵒᵖ` is the vertex
`i.rev` of `G`. -/
@[simp]
lemma opIso_hom_app_obj {n : ℕ} (G : (nerve Cᵒᵖ) _⦋n⦌) (i : Fin (n + 1)) :
    ((nerve C).opObjEquiv ((opIso C).hom.app _ G)).obj i = unop (G.obj i.rev) :=
  (rfl)

/-- The arrow `i ⟶ j` of the image under `opIso` of a simplex `G` of `nerve Cᵒᵖ` is the opposite
of the arrow `j.rev ⟶ i.rev` of `G`. -/
@[simp]
lemma opIso_hom_app_map {n : ℕ} (G : (nerve Cᵒᵖ) _⦋n⦌) {i j : Fin (n + 1)} (h : i ≤ j) :
    ((nerve C).opObjEquiv ((opIso C).hom.app _ G)).map (homOfLE h) =
      eqToHom (opIso_hom_app_obj C G i) ≫ (G.map (homOfLE (Fin.rev_le_rev.2 h))).unop ≫
        eqToHom (opIso_hom_app_obj C G j).symm :=
  -- Both transports are identities once `opIso` is unfolded.
  ((Category.id_comp _).trans (Category.comp_id _)).symm

/-- The vertex `i` of the image under `opIso.inv` of a simplex `F` of `(nerve C)ᵒᵖ` is the vertex
`i.rev` of `F`. -/
@[simp]
lemma opIso_inv_app_obj {n : ℕ} (F : (nerve C).op _⦋n⦌) (i : Fin (n + 1)) :
    ((opIso C).inv.app _ F).obj i = op (((nerve C).opObjEquiv F).obj i.rev) :=
  (rfl)

/-- The arrow `i ⟶ j` of the image under `opIso.inv` of a simplex `F` of `(nerve C)ᵒᵖ` is the
opposite of the arrow `j.rev ⟶ i.rev` of `F`. -/
@[simp]
lemma opIso_inv_app_map {n : ℕ} (F : (nerve C).op _⦋n⦌) {i j : Fin (n + 1)} (h : i ≤ j) :
    ((opIso C).inv.app _ F).map (homOfLE h) =
      eqToHom (opIso_inv_app_obj C F i) ≫
        (((nerve C).opObjEquiv F).map (homOfLE (Fin.rev_le_rev.2 h))).op ≫
          eqToHom (opIso_inv_app_obj C F j).symm :=
  -- Both transports are identities once `opIso` is unfolded.
  ((Category.id_comp _).trans (Category.comp_id _)).symm

/-- On vertices, `opIso` is the identification of the objects of `Cᵒᵖ` with those of `C`. -/
@[simp]
lemma opIso_hom_app_nerveEquiv_symm (x : Cᵒᵖ) :
    (opIso C).hom.app (op ⦋0⦌) (nerveEquiv.symm x) =
      (SSet.opObjEquiv (X := nerve C) (n := op ⦋0⦌)).symm (nerveEquiv.symm x.unop) :=
  ComposableArrows.ext₀ rfl

end CategoryTheory.nerve
