/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.Descent.DescentData

/-!
# Descent data utilities

For a descent datum `D` for a pseudofunctor `F` along a family `f : ∀ i, X i ⟶ S`, Mathlib's
morphisms `D.hom q f₁ f₂ hf₁ hf₂` carry the common composite `q : Y ⟶ S` of `f₁ ≫ f i₁` and
`f₂ ≫ f i₂` as an argument. This file records that they do not depend on `q`
(`DescentData.hom_congr`), states the cocycle condition `DescentData.hom_comp` for two morphisms
whose common composites are only propositionally equal (`DescentData.hom_comp_hom`), and extracts
component isomorphisms from an isomorphism of descent data (`DescentData.isoApp`).
-/

public section

open CategoryTheory Bicategory

namespace CategoryTheory.Pseudofunctor.DescentData

variable {C : Type*} [Category* C] {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat} {ι : Type*}
  {S : C} {X : ι → C} {f : ∀ i, X i ⟶ S} (D : F.DescentData f)

/-- Extract the component isomorphism `D₁.obj i ≅ D₂.obj i` from an isomorphism of descent data
`e : D₁ ≅ D₂`. -/
def isoApp {D₁ D₂ : F.DescentData f} (e : D₁ ≅ D₂) (i : ι) :
    D₁.obj i ≅ D₂.obj i where
  hom := e.hom.hom i
  inv := e.inv.hom i
  hom_inv_id := congrArg (fun φ : D₁ ⟶ D₁ ↦ φ.hom i) e.hom_inv_id
  inv_hom_id := congrArg (fun φ : D₂ ⟶ D₂ ↦ φ.hom i) e.inv_hom_id

/-- The forward morphism of `DescentData.isoApp e i` is the `i`-th component of `e.hom`. -/
@[simp]
lemma isoApp_hom {D₁ D₂ : F.DescentData f} (e : D₁ ≅ D₂) (i : ι) :
    (isoApp e i).hom = e.hom.hom i :=
  (rfl)

/-- The inverse morphism of `DescentData.isoApp e i` is the `i`-th component of `e.inv`. -/
@[simp]
lemma isoApp_inv {D₁ D₂ : F.DescentData f} (e : D₁ ≅ D₂) (i : ι) :
    (isoApp e i).inv = e.inv.hom i :=
  (rfl)

/-- The morphisms `D.hom q f₁ f₂` do not depend on the common composite `q`, which is determined
by `f₁`. -/
lemma hom_congr ⦃Y : C⦄ ⦃i₁ i₂ : ι⦄ (q q' : Y ⟶ S) (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
    (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) (hq : q = q') :
    D.hom q f₁ f₂ hf₁ hf₂ = D.hom q' f₁ f₂ (hf₁.trans hq) (hf₂.trans hq) := by
  subst hq
  rfl

/-- The cocycle condition `DescentData.hom_comp` for possibly different common composites. -/
@[reassoc]
lemma hom_comp_hom ⦃Y : C⦄ ⦃i₁ i₂ i₃ : ι⦄ (q q' : Y ⟶ S) (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
    (f₃ : Y ⟶ X i₃) (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) (hf₂' : f₂ ≫ f i₂ = q')
    (hf₃ : f₃ ≫ f i₃ = q') :
    D.hom q f₁ f₂ hf₁ hf₂ ≫ D.hom q' f₂ f₃ hf₂' hf₃ =
      D.hom q f₁ f₃ hf₁ (hf₃.trans (hf₂'.symm.trans hf₂)) := by
  obtain rfl : q' = q := hf₂'.symm.trans hf₂
  exact D.hom_comp _ _ _ _ _ _ _

end CategoryTheory.Pseudofunctor.DescentData
