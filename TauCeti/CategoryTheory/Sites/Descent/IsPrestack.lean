/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.Descent.DescentData
public import TauCeti.CategoryTheory.Bicategory.Functor.LocallyDiscrete

/-!
# Restricting a morphism in the presheaf of morphisms

Let `F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat` be a pseudofunctor and `M`, `N` objects of `F` over `S`.
Mathlib's presheaf of morphisms `Pseudofunctor.presheafHom M N` on `Over S` has value
`f^* M ⟶ f^* N` at `(Y, f)`, and its value at the terminal object `Over.mk (𝟙 S)` is identified with
`M ⟶ N` by `Pseudofunctor.presheafHomObjHomEquiv`. This file shows that restricting the element
given by `φ : M ⟶ N` to `(Y, f)` gives `f^* φ`
(`CategoryTheory.Pseudofunctor.presheafHom_map_presheafHomObjHomEquiv`). So a morphism `φ` is an
amalgamation of a family of local morphisms exactly when its pullbacks are the members of the
family, which is how the sheaf condition of `presheafHom M N` (the prestack condition) is checked.

It also shows that pulling back morphisms between pullbacks commutes with restricting `F` along a
functor `p : D ⥤ C`: for the pseudofunctor `p.op.toPseudofunctor.comp F`, pulling back along `g`
is pulling back along `p.map g` for `F`
(`CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom_toPseudofunctor_comp`).
-/

public section

open CategoryTheory Opposite Bicategory

namespace CategoryTheory.Pseudofunctor

variable {C : Type*} [Category* C] (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat) {S : C}

/-- The restriction of the element of `F.presheafHom M N` over the terminal object given by
`φ : M ⟶ N` to an object `(Y, f)` of `Over S` is `f^* φ`. -/
lemma presheafHom_map_presheafHomObjHomEquiv {M N : F.obj (.mk (op S))} (φ : M ⟶ N)
    {Y : Over S} (g : Y ⟶ Over.mk (𝟙 S)) :
    (F.presheafHom M N).map g.op (F.presheafHomObjHomEquiv φ) =
      (F.map Y.hom.op.toLoc).toFunctor.map φ := by
  obtain ⟨Y, y, rfl⟩ := Over.mk_surjective Y
  obtain rfl : g = Over.homMk y := by ext; simpa using Over.w g
  -- This is the component, for the family consisting of `y` alone, of Mathlib's identification of
  -- the compatible family given by `φ` with the morphism of descent data `toDescentData.map φ`.
  exact congr(DescentData.Hom.hom
    $(DescentData.subtypeCompatibleHomEquiv_toCompatible_presheafHomObjHomEquiv F
      (fun _ : PUnit.{1} ↦ y) φ) PUnit.unit)

namespace LocallyDiscreteOpToCat

variable {D : Type*} [Category* D] (p : D ⥤ C)

/-- Pulling back a morphism between pullbacks along a morphism `g` of `D`, for the restriction
`p.op.toPseudofunctor.comp F` of `F` along `p : D ⥤ C`, is pulling it back along `p.map g` for
`F`. -/
lemma pullHom_toPseudofunctor_comp ⦃X₁ X₂ : D⦄
    ⦃M₁ : (p.op.toPseudofunctor.comp F).obj (.mk (op X₁))⦄
    ⦃M₂ : (p.op.toPseudofunctor.comp F).obj (.mk (op X₂))⦄ ⦃Y : D⦄ ⦃f₁ : Y ⟶ X₁⦄ ⦃f₂ : Y ⟶ X₂⦄
    (φ : ((p.op.toPseudofunctor.comp F).map f₁.op.toLoc).toFunctor.obj M₁ ⟶
      ((p.op.toPseudofunctor.comp F).map f₂.op.toLoc).toFunctor.obj M₂)
    ⦃Y' : D⦄ (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂) (hgf₁ : g ≫ f₁ = gf₁)
    (hgf₂ : g ≫ f₂ = gf₂) :
    pullHom φ g gf₁ gf₂ hgf₁ hgf₂ =
      pullHom (F := F) (X₁ := p.obj X₁) (X₂ := p.obj X₂) (M₁ := M₁) (M₂ := M₂) (f₁ := p.map f₁)
        (f₂ := p.map f₂) φ (p.map g) (p.map gf₁) (p.map gf₂) (by rw [← hgf₁, p.map_comp])
        (by rw [← hgf₂, p.map_comp]) := by
  unfold pullHom
  rw [comp_mapComp'_eq_mapComp' _ _ f₁.op.toLoc g.op.toLoc gf₁.op.toLoc (by rw [← hgf₁]; rfl),
    comp_mapComp'_eq_mapComp' _ _ f₂.op.toLoc g.op.toLoc gf₂.op.toLoc (by rw [← hgf₂]; rfl)]
  -- Both sides now use the comparisons of `F`; the pullback functors along `g.op.toLoc` for the
  -- restriction and along `(p.map g).op.toLoc` for `F` agree by unfolding `Pseudofunctor.comp`.
  rfl

end LocallyDiscreteOpToCat

end CategoryTheory.Pseudofunctor
