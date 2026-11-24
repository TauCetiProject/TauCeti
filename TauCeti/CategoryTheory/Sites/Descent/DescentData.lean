/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.Sites.Descent.DescentData

/-!
# Morphisms of descent data

For a descent datum `D` for a pseudofunctor `F` along a family `f : ∀ i, X i ⟶ S`, Mathlib's
morphisms `D.hom q f₁ f₂ hf₁ hf₂` carry the common composite `q : Y ⟶ S` of `f₁ ≫ f i₁` and
`f₂ ≫ f i₂` as an argument. This file records that they do not depend on `q`
(`DescentData.hom_congr`), and states the cocycle condition `DescentData.hom_comp` for two
morphisms whose common composites are only propositionally equal (`DescentData.hom_comp_hom`).

A morphism of Mathlib's descent data `D₁ ⟶ D₂` along `f` is a family of morphisms
`φ i : D₁.obj i ⟶ D₂.obj i` commuting with the gluing morphisms over every `Y` mapping to two of
the `X i` compatibly with the maps to `S`. When the pairs `X i₁ ×_S X i₂` have pullbacks, it is
enough to check this on the pullbacks themselves: every other `Y` maps to one of them, and the
gluing morphisms over `Y` are pulled back from those over the pullback
(`CategoryTheory.Pseudofunctor.DescentData.homMkOfIsPullback`). This is the form of the
compatibility condition used when descent data are compared with coalgebras.

The argument for `homMkOfIsPullback` is that of Mathlib's
`CategoryTheory.Pseudofunctor.DescentData'.comm`, which proves the same compatibility for descent
data stated on chosen pullbacks.
-/

public section

open CategoryTheory Bicategory Opposite

namespace CategoryTheory.Pseudofunctor.DescentData

variable {C : Type*} [Category* C] {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat} {ι : Type*}
  {S : C} {X : ι → C} {f : ∀ i, X i ⟶ S} (D : F.DescentData f)

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

open LocallyDiscreteOpToCat

variable {D₁ D₂ : F.DescentData f}

/-- **Morphisms of descent data are checked on pullbacks.** Given, for all `i j`, a pullback square
`P i j` of `f i` and `f j` with projections `p₁ i j` and `p₂ i j`, a family of morphisms
`φ i : D₁.obj i ⟶ D₂.obj i` which commutes with the gluing morphisms over every `P i j` is a
morphism of descent data. -/
def homMkOfIsPullback (φ : ∀ i, D₁.obj i ⟶ D₂.obj i) {P : ι → ι → C}
    {p₁ : ∀ i j, P i j ⟶ X i} {p₂ : ∀ i j, P i j ⟶ X j}
    (h : ∀ i j, IsPullback (p₁ i j) (p₂ i j) (f i) (f j))
    (comm : ∀ i j, (F.map (p₁ i j).op.toLoc).toFunctor.map (φ i) ≫
        D₂.hom (p₁ i j ≫ f i) (p₁ i j) (p₂ i j) rfl (h i j).w.symm =
      D₁.hom (p₁ i j ≫ f i) (p₁ i j) (p₂ i j) rfl (h i j).w.symm ≫
        (F.map (p₂ i j).op.toLoc).toFunctor.map (φ j)) :
    D₁ ⟶ D₂ where
  hom := φ
  comm Y q i₁ i₂ f₁ f₂ hf₁ hf₂ := by
    -- `Y` maps to the pullback `P i₁ i₂` by `g`, and the gluing morphisms over `Y` are the
    -- pullbacks along `g` of those over `P i₁ i₂`.
    let g := (h i₁ i₂).lift f₁ f₂ (hf₁.trans hf₂.symm)
    have hg₁ : g ≫ p₁ i₁ i₂ = f₁ := (h i₁ i₂).lift_fst _ _ _
    have hg₂ : g ≫ p₂ i₁ i₂ = f₂ := (h i₁ i₂).lift_snd _ _ _
    have hq : g ≫ p₁ i₁ i₂ ≫ f i₁ = q := by rw [reassoc_of% hg₁, hf₁]
    rw [← D₁.pullHom_hom g _ q hq _ _ rfl (h i₁ i₂).w.symm _ _ hg₁ hg₂,
      ← D₂.pullHom_hom g _ q hq _ _ rfl (h i₁ i₂).w.symm _ _ hg₁ hg₂]
    -- Move `φ` across the comparison isomorphisms of `F` by their naturality, and apply `comm`
    -- pulled back along `g`.
    dsimp only [pullHom]
    rw [mapComp'_hom_naturality_assoc, ← Functor.map_comp_assoc, comm, Functor.map_comp_assoc,
      mapComp'_inv_naturality]
    simp only [Category.assoc]

/-- The components of `homMkOfIsPullback φ h comm` are the given morphisms `φ i`. -/
@[simp]
lemma homMkOfIsPullback_hom (φ : ∀ i, D₁.obj i ⟶ D₂.obj i) {P : ι → ι → C}
    {p₁ : ∀ i j, P i j ⟶ X i} {p₂ : ∀ i j, P i j ⟶ X j}
    (h : ∀ i j, IsPullback (p₁ i j) (p₂ i j) (f i) (f j))
    (comm : ∀ i j, (F.map (p₁ i j).op.toLoc).toFunctor.map (φ i) ≫
        D₂.hom (p₁ i j ≫ f i) (p₁ i j) (p₂ i j) rfl (h i j).w.symm =
      D₁.hom (p₁ i j ≫ f i) (p₁ i j) (p₂ i j) rfl (h i j).w.symm ≫
        (F.map (p₂ i j).op.toLoc).toFunctor.map (φ j)) (i : ι) :
    (homMkOfIsPullback φ h comm).hom i = φ i :=
  -- The body of `homMkOfIsPullback` is not exposed, so this is not a `rfl` lemma for `dsimp`
  -- outside this module.
  by rfl

end CategoryTheory.Pseudofunctor.DescentData
