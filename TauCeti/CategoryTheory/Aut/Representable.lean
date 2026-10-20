/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.Yoneda

/-!
# Automorphisms of a represented presheaf

Let a presheaf `F : Cᵒᵖ ⥤ Type w` be represented by an object `Y`, through natural bijections
`homEquiv : (X ⟶ Y) ≃ F(X)`. By the Yoneda lemma, automorphisms of `F` are the same as
automorphisms of `Y`: an automorphism `σ` of `F` corresponds to the unique automorphism `s` of `Y`
with `homEquiv (f ≫ s) = σ (homEquiv f)` for every `f : X ⟶ Y`. This file records the
correspondence as an isomorphism of groups `Aut F ≃* Aut Y`
(`CategoryTheory.Functor.RepresentableBy.autMulEquiv`). Composing with it turns an action of a
group on a represented presheaf into an action on the representing object.

The presheaf may take values in any universe `w`, unrelated to the universe `v` of morphisms of
`C`. This is the generality of moduli problems, which take values in a larger universe than the
morphisms of their category of test objects. Mathlib identifies a representation with an
isomorphism to the Yoneda functor only when `F` takes values in `Type v`
(`CategoryTheory.Functor.RepresentableBy.toIso`), or with an isomorphism to the lifted Yoneda
functor when `F` takes values in `Type (max w v)`
(`CategoryTheory.Functor.RepresentableBy.equivUliftYonedaIso`), where the universe `w` cannot be
inferred from `F` and has to be given explicitly. The correspondence here needs neither: the
automorphism of `Y` attached to `σ` compares the representation of `F` by `Y` with its transport
along `σ`, by uniqueness of representing objects
(`CategoryTheory.Functor.RepresentableBy.uniqueUpToIso`).

## Main definitions

* `CategoryTheory.Functor.RepresentableBy.autMulEquiv`: automorphisms of a represented presheaf are
  automorphisms of the representing object.

## Main results

* `CategoryTheory.Functor.RepresentableBy.homEquiv_comp_autMulEquiv_hom`: the automorphism of `Y`
  attached to `σ` acts on `homEquiv f` as `σ`.
* `CategoryTheory.Functor.RepresentableBy.autMulEquiv_symm_hom_app`: conversely, the automorphism of
  `F` attached to an automorphism `s` of `Y` is postcomposition with `s`.
-/

public section

namespace CategoryTheory.Functor.RepresentableBy

open Opposite

universe w v u

variable {C : Type u} [Category.{v} C] {F : Cᵒᵖ ⥤ Type w} {Y : C} (R : F.RepresentableBy Y)

/-- Postcomposition with a morphism `s : Y ⟶ Y`, transported to `F` along `homEquiv`, commutes
with the maps of `F`. -/
private theorem homEquiv_homEquiv_symm_comp_naturality (s : Y ⟶ Y) {X X' : C} (f : X ⟶ X')
    (x : F.obj (op X')) :
    R.homEquiv (R.homEquiv.symm (F.map f.op x) ≫ s) =
      F.map f.op (R.homEquiv (R.homEquiv.symm x ≫ s)) := by
  rw [← comp_homEquiv_symm, Category.assoc, homEquiv_comp]

/-- The automorphism of the presheaf `F` given by postcomposition with an automorphism `s` of the
representing object: it sends `homEquiv f` to `homEquiv (f ≫ s)`. -/
private def postcompIso (s : Aut Y) : F ≅ F :=
  NatIso.ofComponents
    (fun X ↦ Equiv.toIso ((R.homEquiv.symm.trans s.asIso.homToEquiv).trans R.homEquiv))
    -- both sides are `homEquiv_homEquiv_symm_comp_naturality` after unfolding `Equiv.toIso`
    (fun f ↦ by ext x; exact R.homEquiv_homEquiv_symm_comp_naturality s.asIso.hom f.unop x)

/-- The automorphism of `Y` attached to an automorphism `σ` of `F`: by uniqueness of representing
objects, it compares the representation `R` with its transport along `σ`. -/
private def toAutObj (σ : Aut F) : Aut Y :=
  .of ((R.ofIso σ.asIso).uniqueUpToIso R)

private theorem homEquiv_comp_toAutObj_hom (σ : Aut F) {X : C} (f : X ⟶ Y) :
    R.homEquiv (f ≫ (R.toAutObj σ).asIso.hom) = σ.asIso.hom.app (op X) (R.homEquiv f) := by
  have h : (R.toAutObj σ).asIso.hom =
      R.homEquiv.symm (σ.asIso.hom.app (op Y) (R.homEquiv (𝟙 Y))) := by
    simp [toAutObj, Yoneda.fullyFaithful_preimage, ofIso]
  rw [h, homEquiv_comp, Equiv.apply_symm_apply, ← NatTrans.naturality_apply, ← homEquiv_comp,
    Category.comp_id]

private theorem homEquiv_toAutObj_hom (σ : Aut F) :
    R.homEquiv (R.toAutObj σ).asIso.hom = σ.asIso.hom.app (op Y) (R.homEquiv (𝟙 Y)) := by
  rw [← R.homEquiv_comp_toAutObj_hom, Category.id_comp]

/-- **Automorphisms of a represented presheaf are automorphisms of the representing object.** If
`F` is represented by `Y`, an automorphism `σ` of `F` corresponds to the automorphism `s` of `Y`
with `homEquiv (f ≫ s) = σ (homEquiv f)` for every `f : X ⟶ Y`
(`homEquiv_comp_autMulEquiv_hom`); an automorphism `s` of `Y` corresponds to postcomposition
with `s` (`autMulEquiv_symm_hom_app`). -/
def autMulEquiv : Aut F ≃* Aut Y where
  toFun := R.toAutObj
  invFun s := .of (R.postcompIso s)
  left_inv σ := by
    ext X x
    obtain ⟨f, rfl⟩ := R.homEquiv.surjective x
    -- the left side is `homEquiv (homEquiv.symm (homEquiv f) ≫ s)` after unfolding `Equiv.toIso`
    exact (congrArg (fun g ↦ R.homEquiv (g ≫ _)) (R.homEquiv.symm_apply_apply f)).trans
      (R.homEquiv_comp_toAutObj_hom σ f)
  right_inv s := by
    ext
    refine R.homEquiv.injective ?_
    rw [homEquiv_toAutObj_hom]
    -- the left side is `homEquiv (homEquiv.symm (homEquiv (𝟙 Y)) ≫ s)` after unfolding
    -- `Equiv.toIso`
    exact (congrArg (fun g ↦ R.homEquiv (g ≫ s.asIso.hom)) (R.homEquiv.symm_apply_apply _)).trans
      (by rw [Category.id_comp])
  map_mul' σ τ := by
    ext
    refine R.homEquiv.injective ?_
    rw [Aut.mul_asIso, Iso.trans_hom, homEquiv_comp_toAutObj_hom, homEquiv_toAutObj_hom,
      homEquiv_toAutObj_hom, Aut.mul_asIso, Iso.trans_hom, NatTrans.comp_app, types_comp_apply]

/-- The automorphism of `Y` attached to an automorphism `σ` of `F` acts on `homEquiv f` as `σ`. -/
@[simp]
theorem homEquiv_comp_autMulEquiv_hom (σ : Aut F) {X : C} (f : X ⟶ Y) :
    R.homEquiv (f ≫ (R.autMulEquiv σ).asIso.hom) = σ.asIso.hom.app (op X) (R.homEquiv f) :=
  R.homEquiv_comp_toAutObj_hom σ f

/-- The inverse of the automorphism of `Y` attached to an automorphism `σ` of `F` acts on
`homEquiv f` as the inverse of `σ`. -/
@[simp]
theorem homEquiv_comp_autMulEquiv_inv (σ : Aut F) {X : C} (f : X ⟶ Y) :
    R.homEquiv (f ≫ (R.autMulEquiv σ).asIso.inv) = σ.asIso.inv.app (op X) (R.homEquiv f) := by
  rw [← Iso.symm_hom, ← Aut.inv_asIso, ← _root_.map_inv, homEquiv_comp_autMulEquiv_hom,
    Aut.inv_asIso, Iso.symm_hom]

/-- The automorphism of `F` attached to an automorphism `s` of `Y` is postcomposition with `s`. -/
@[simp]
theorem autMulEquiv_symm_hom_app (s : Aut Y) {X : C} (x : F.obj (op X)) :
    (R.autMulEquiv.symm s).asIso.hom.app (op X) x = R.homEquiv (R.homEquiv.symm x ≫ s.asIso.hom) :=
  (rfl)

end CategoryTheory.Functor.RepresentableBy
