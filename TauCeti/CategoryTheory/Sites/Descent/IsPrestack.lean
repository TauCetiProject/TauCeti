/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.Descent.DescentData

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

The restriction maps of `presheafHom` are Mathlib's `Pseudofunctor.LocallyDiscreteOpToCat.pullHom`.
This file also shows that `pullHom` is compatible with composition and identities
(`CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom_comp`,
`CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom_id_eq_id`), hence sends isomorphisms
to isomorphisms (`CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.inv_pullHom`), and that it
sends the pullback `f^* φ` of a morphism `φ` to its pullback along the composite
(`CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom_map`).
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

variable {F}

/-- `pullHom` is compatible with composition of morphisms. -/
lemma pullHom_comp ⦃X₁ X₂ X₃ : C⦄ ⦃M₁ : F.obj (.mk (op X₁))⦄ ⦃M₂ : F.obj (.mk (op X₂))⦄
    ⦃M₃ : F.obj (.mk (op X₃))⦄ ⦃Y : C⦄ ⦃f₁ : Y ⟶ X₁⦄ ⦃f₂ : Y ⟶ X₂⦄ ⦃f₃ : Y ⟶ X₃⦄
    (φ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂)
    (ψ : (F.map f₂.op.toLoc).toFunctor.obj M₂ ⟶ (F.map f₃.op.toLoc).toFunctor.obj M₃) ⦃Y' : C⦄
    (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂) (gf₃ : Y' ⟶ X₃) (hgf₁ : g ≫ f₁ = gf₁)
    (hgf₂ : g ≫ f₂ = gf₂) (hgf₃ : g ≫ f₃ = gf₃) :
    pullHom (φ ≫ ψ) g gf₁ gf₃ hgf₁ hgf₃ =
      pullHom φ g gf₁ gf₂ hgf₁ hgf₂ ≫ pullHom ψ g gf₂ gf₃ hgf₂ hgf₃ := by
  simp [pullHom, ← Cat.Hom₂.comp_app_assoc]

/-- `pullHom` sends an identity morphism to an identity morphism. -/
@[simp]
lemma pullHom_id_eq_id ⦃X : C⦄ ⦃M : F.obj (.mk (op X))⦄ ⦃Y : C⦄ ⦃f : Y ⟶ X⦄ ⦃Y' : C⦄
    (g : Y' ⟶ Y) (gf : Y' ⟶ X) (hgf : g ≫ f = gf) :
    pullHom (𝟙 ((F.map f.op.toLoc).toFunctor.obj M)) g gf gf hgf hgf = 𝟙 _ := by
  simp [pullHom, ← Cat.Hom₂.comp_app]

/-- `pullHom` sends an isomorphism to an isomorphism. -/
instance isIso_pullHom ⦃X₁ X₂ : C⦄ ⦃M₁ : F.obj (.mk (op X₁))⦄ ⦃M₂ : F.obj (.mk (op X₂))⦄
    ⦃Y : C⦄ ⦃f₁ : Y ⟶ X₁⦄ ⦃f₂ : Y ⟶ X₂⦄
    (φ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂) [IsIso φ]
    ⦃Y' : C⦄ (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂) (hgf₁ : g ≫ f₁ = gf₁)
    (hgf₂ : g ≫ f₂ = gf₂) : IsIso (pullHom φ g gf₁ gf₂ hgf₁ hgf₂) :=
  ⟨pullHom (inv φ) g gf₂ gf₁ hgf₂ hgf₁, by simp [← pullHom_comp], by simp [← pullHom_comp]⟩

/-- `pullHom φ g` is an isomorphism exactly when the pullback `g^* φ` is. -/
lemma isIso_pullHom_iff ⦃X₁ X₂ : C⦄ ⦃M₁ : F.obj (.mk (op X₁))⦄ ⦃M₂ : F.obj (.mk (op X₂))⦄
    ⦃Y : C⦄ ⦃f₁ : Y ⟶ X₁⦄ ⦃f₂ : Y ⟶ X₂⦄
    (φ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂)
    ⦃Y' : C⦄ (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂) (hgf₁ : g ≫ f₁ = gf₁)
    (hgf₂ : g ≫ f₂ = gf₂) :
    IsIso (pullHom φ g gf₁ gf₂ hgf₁ hgf₂) ↔ IsIso ((F.map g.op.toLoc).toFunctor.map φ) := by
  rw [map_eq_pullHom φ g gf₁ gf₂ hgf₁ hgf₂]
  simp only [isIso_comp_left_iff, isIso_comp_right_iff]

/-- `pullHom` commutes with taking inverses. -/
@[simp]
lemma inv_pullHom ⦃X₁ X₂ : C⦄ ⦃M₁ : F.obj (.mk (op X₁))⦄ ⦃M₂ : F.obj (.mk (op X₂))⦄
    ⦃Y : C⦄ ⦃f₁ : Y ⟶ X₁⦄ ⦃f₂ : Y ⟶ X₂⦄
    (φ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂) [IsIso φ]
    ⦃Y' : C⦄ (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂) (hgf₁ : g ≫ f₁ = gf₁)
    (hgf₂ : g ≫ f₂ = gf₂) :
    inv (pullHom φ g gf₁ gf₂ hgf₁ hgf₂) = pullHom (inv φ) g gf₂ gf₁ hgf₂ hgf₁ :=
  IsIso.inv_eq_of_hom_inv_id (by simp [← pullHom_comp])

/-- `pullHom` sends the pullback `f^* φ` of a morphism `φ : M ⟶ N` along `f` to its pullback
along the composite `gf = g ≫ f`. -/
@[simp]
lemma pullHom_map ⦃X : C⦄ ⦃M N : F.obj (.mk (op X))⦄ (φ : M ⟶ N) ⦃Y : C⦄ (f : Y ⟶ X) ⦃Y' : C⦄
    (g : Y' ⟶ Y) (gf : Y' ⟶ X) (hgf : g ≫ f = gf) :
    pullHom ((F.map f.op.toLoc).toFunctor.map φ) g gf gf hgf hgf =
      (F.map gf.op.toLoc).toFunctor.map φ := by
  simp [pullHom]

end LocallyDiscreteOpToCat

end CategoryTheory.Pseudofunctor
