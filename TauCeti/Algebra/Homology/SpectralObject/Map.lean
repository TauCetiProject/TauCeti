/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.SpectralObject.Differentials

/-!
# Functoriality of the pages of spectral objects

Let `φ : X ⟶ Y` be a morphism of spectral objects in an abelian category. We define the induced
maps on the objects `E^n(f₁, f₂, f₃)` (`CategoryTheory.Abelian.SpectralObject.EMap`), on the
cycles `Z^n(f, g)` (`CategoryTheory.Abelian.SpectralObject.cyclesMapOfHom`), and show that they are
functorial in `φ` (`EMap_id`, `EMap_comp`, `cyclesMapOfHom_id`, `cyclesMapOfHom_comp`) and
compatible with the projections `πE`, the maps `toCycles`, the
functoriality maps `X.map` in the indices, and the differentials `X.d`
(`CategoryTheory.Abelian.SpectralObject.d_EMap`). These are the ingredients of the morphism of
spectral sequences induced by `φ`.

## Main definitions

* `CategoryTheory.Abelian.SpectralObject.EMap φ f₁ f₂ f₃ n₀ n₁ n₂`: the map
  `X.E f₁ f₂ f₃ n₀ n₁ n₂ ⟶ Y.E f₁ f₂ f₃ n₀ n₁ n₂`.
* `CategoryTheory.Abelian.SpectralObject.cyclesMapOfHom φ f g n`: the map on cycles.
* `CategoryTheory.Abelian.SpectralObject.opcyclesMapOfHom φ f g n`: the map on opcycles, with
  `isIso_opcyclesMapOfHom_of_isIso` (three-lemma on Mathlib's short exact sequences
  `0 ⟶ opZ^n(f₁, f₂ ≫ f₃) ⟶ opZ^n(f₁ ≫ f₂, f₃) ⟶ E^n(f₁, f₂, f₃) ⟶ 0`).

## Main results

* `CategoryTheory.Abelian.SpectralObject.EMap_id`, `EMap_comp`: functoriality.
* `CategoryTheory.Abelian.SpectralObject.map_EMap`: compatibility with `X.map`.
* `CategoryTheory.Abelian.SpectralObject.d_EMap`: compatibility with the differentials.

## References

* The constructions adapt to morphisms of spectral objects those of Joël Riou's Mathlib files
  `Mathlib/Algebra/Homology/SpectralObject/{Page,Cycles,Differentials}.lean` (`shortComplexMap`,
  `map`, `cyclesMap`, `πE_map`), which are functorial in the indices.
* J.-L. Verdier, *Des catégories dérivées des catégories abéliennes*, Astérisque 239 (1996), II.4.
-/

public section

namespace CategoryTheory.Abelian.SpectralObject

open ComposableArrows Limits

variable {C ι : Type*} [Category* C] [Category* ι] [Abelian C]
  {X Y Z : SpectralObject C ι} (φ : X ⟶ Y) (ψ : Y ⟶ Z)

section E

variable {i j k l : ι} (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l) (n₀ n₁ n₂ : ℤ)
  (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂)

/-- The morphism of short complexes `X.shortComplex f₁ f₂ f₃ ⟶ Y.shortComplex f₁ f₂ f₃` induced by
a morphism of spectral objects. -/
def shortComplexMapOfHom :
    X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ⟶ Y.shortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ where
  τ₁ := (φ.hom n₀).app (mk₁ f₃)
  τ₂ := (φ.hom n₁).app (mk₁ f₂)
  τ₃ := (φ.hom n₂).app (mk₁ f₁)
  comm₁₂ := (φ.comm n₀ n₁ hn₁ f₂ f₃).symm
  comm₂₃ := (φ.comm n₁ n₂ hn₂ f₁ f₂).symm

@[simp]
lemma shortComplexMapOfHom_τ₁ :
    (shortComplexMapOfHom φ f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).τ₁ = (φ.hom n₀).app (mk₁ f₃) := by
  rw [shortComplexMapOfHom]

@[simp]
lemma shortComplexMapOfHom_τ₂ :
    (shortComplexMapOfHom φ f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).τ₂ = (φ.hom n₁).app (mk₁ f₂) := by
  rw [shortComplexMapOfHom]

@[simp]
lemma shortComplexMapOfHom_τ₃ :
    (shortComplexMapOfHom φ f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).τ₃ = (φ.hom n₂).app (mk₁ f₁) := by
  rw [shortComplexMapOfHom]

@[simp]
lemma shortComplexMapOfHom_id :
    shortComplexMapOfHom (𝟙 X) f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ = 𝟙 _ := by
  -- the remaining goals are `𝟙 ((X.H n₀).obj (mk₁ f₃)) = 𝟙 (X.shortComplex …).X₁` (and similarly
  -- for `X₂`, `X₃`): `(X.shortComplex …).X₁` is `(X.H n₀).obj (mk₁ f₃)` by definition, and
  -- `shortComplex_X₁` cannot rewrite the object under `𝟙`
  ext <;> simp only [shortComplexMapOfHom_τ₁, shortComplexMapOfHom_τ₂, shortComplexMapOfHom_τ₃,
    id_hom, NatTrans.id_app, ShortComplex.id_τ₁, ShortComplex.id_τ₂, ShortComplex.id_τ₃] <;> rfl

@[reassoc, simp]
lemma shortComplexMapOfHom_comp :
    shortComplexMapOfHom (φ ≫ ψ) f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ =
      shortComplexMapOfHom φ f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ≫
        shortComplexMapOfHom ψ f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ := by
  -- after `simp`, both sides are `(φ.hom n).app _ ≫ (ψ.hom n).app _`, composed in `C` between
  -- the objects `(Y.H n).obj _` and `(Y.shortComplex …).X₁` (equal by definition), hence `rfl`
  ext <;> simp only [shortComplexMapOfHom_τ₁, shortComplexMapOfHom_τ₂, shortComplexMapOfHom_τ₃,
    comp_hom, NatTrans.comp_app, ShortComplex.comp_τ₁, ShortComplex.comp_τ₂,
    ShortComplex.comp_τ₃] <;> rfl

/-- The morphism `X.E f₁ f₂ f₃ n₀ n₁ n₂ ⟶ Y.E f₁ f₂ f₃ n₀ n₁ n₂` induced by a morphism of
spectral objects. -/
noncomputable def EMap :
    X.E f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ⟶ Y.E f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ :=
  ShortComplex.homologyMap (shortComplexMapOfHom φ f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂)

@[simp]
lemma EMap_id :
    EMap (𝟙 X) f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ = 𝟙 _ := by
  rw [EMap, shortComplexMapOfHom_id, ShortComplex.homologyMap_id]
  -- `X.E f₁ f₂ f₃ …` is by definition `(X.shortComplex f₁ f₂ f₃ …).homology`
  rfl

@[reassoc, simp]
lemma EMap_comp :
    EMap (φ ≫ ψ) f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ =
      EMap φ f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ≫ EMap ψ f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ := by
  rw [EMap, shortComplexMapOfHom_comp, ShortComplex.homologyMap_comp]
  -- `X.E f₁ f₂ f₃ …` is by definition `(X.shortComplex f₁ f₂ f₃ …).homology`
  rfl

variable {i' j' k' l' : ι} {f₁' : i' ⟶ j'} {f₂' : j' ⟶ k'} {f₃' : k' ⟶ l'}

/-- The morphisms `shortComplexMapOfHom` commute with the functoriality maps
`X.shortComplexMap` in the indices. -/
@[reassoc]
lemma shortComplexMap_shortComplexMapOfHom (α : mk₃ f₁ f₂ f₃ ⟶ mk₃ f₁' f₂' f₃') :
    X.shortComplexMap f₁ f₂ f₃ f₁' f₂' f₃' α n₀ n₁ n₂ hn₁ hn₂ ≫
      shortComplexMapOfHom φ f₁' f₂' f₃' n₀ n₁ n₂ hn₁ hn₂ =
      shortComplexMapOfHom φ f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ≫
        Y.shortComplexMap f₁ f₂ f₃ f₁' f₂' f₃' α n₀ n₁ n₂ hn₁ hn₂ := by
  ext <;> simp only [ShortComplex.comp_τ₁, ShortComplex.comp_τ₂, ShortComplex.comp_τ₃,
    shortComplexMap_τ₁, shortComplexMap_τ₂, shortComplexMap_τ₃, shortComplexMapOfHom_τ₁,
    shortComplexMapOfHom_τ₂, shortComplexMapOfHom_τ₃] <;>
    exact (φ.hom _).naturality _

/-- The maps `EMap` commute with the functoriality maps `X.map` in the indices. -/
@[reassoc]
lemma map_EMap (α : mk₃ f₁ f₂ f₃ ⟶ mk₃ f₁' f₂' f₃') :
    X.map f₁ f₂ f₃ f₁' f₂' f₃' α n₀ n₁ n₂ hn₁ hn₂ ≫ EMap φ f₁' f₂' f₃' n₀ n₁ n₂ hn₁ hn₂ =
      EMap φ f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ≫ Y.map f₁ f₂ f₃ f₁' f₂' f₃' α n₀ n₁ n₂ hn₁ hn₂ := by
  -- `ShortComplex.homologyMap_comp` only matches the zero-morphism instances of
  -- `X.shortComplex` up to unfolding of instances, hence `erw`.
  dsimp only [map, EMap]
  erw [← ShortComplex.homologyMap_comp, shortComplexMap_shortComplexMapOfHom,
    ShortComplex.homologyMap_comp]
  -- `X.E f₁ f₂ f₃ …` is by definition `(X.shortComplex f₁ f₂ f₃ …).homology`
  rfl

end E

section Cycles

variable {i j k : ι} (f : i ⟶ j) (g : j ⟶ k) (n : ℤ)

/-- The morphism `X.cycles f g n ⟶ Y.cycles f g n` induced by a morphism of spectral objects. -/
noncomputable def cyclesMapOfHom : X.cycles f g n ⟶ Y.cycles f g n :=
  Y.liftCycles f g n (n + 1) rfl (X.iCycles f g n ≫ (φ.hom n).app (mk₁ g)) (by
    rw [Category.assoc, ← φ.comm n (n + 1) rfl f g, X.iCycles_δ_assoc f g n (n + 1) rfl,
      zero_comp])

@[reassoc (attr := simp)]
lemma cyclesMapOfHom_i :
    cyclesMapOfHom φ f g n ≫ Y.iCycles f g n = X.iCycles f g n ≫ (φ.hom n).app (mk₁ g) :=
  Y.liftCycles_i ..

@[simp]
lemma cyclesMapOfHom_id : cyclesMapOfHom (𝟙 X) f g n = 𝟙 _ := by
  rw [← cancel_mono (X.iCycles f g n), cyclesMapOfHom_i, id_hom, NatTrans.id_app, Category.comp_id,
    Category.id_comp]

@[reassoc, simp]
lemma cyclesMapOfHom_comp :
    cyclesMapOfHom (φ ≫ ψ) f g n = cyclesMapOfHom φ f g n ≫ cyclesMapOfHom ψ f g n := by
  rw [← cancel_mono (Z.iCycles f g n), cyclesMapOfHom_i, Category.assoc, cyclesMapOfHom_i,
    cyclesMapOfHom_i_assoc, comp_hom, NatTrans.comp_app]

@[reassoc]
lemma toCycles_cyclesMapOfHom (fg : i ⟶ k) (h : f ≫ g = fg) :
    X.toCycles f g fg h n ≫ cyclesMapOfHom φ f g n =
      (φ.hom n).app (mk₁ fg) ≫ Y.toCycles f g fg h n := by
  rw [← cancel_mono (Y.iCycles f g n), Category.assoc, cyclesMapOfHom_i, toCycles_i_assoc,
    Category.assoc, toCycles_i]
  exact (φ.hom n).naturality _

variable {l : ι} (f₃ : k ⟶ l) (n₀ n₂ : ℤ) (hn₁ : n₀ + 1 = n) (hn₂ : n + 1 = n₂)

/-- Through the identifications `cyclesIso`, the map on cycles of `shortComplexMapOfHom` is
`cyclesMapOfHom`. -/
@[reassoc]
lemma cyclesIso_inv_cyclesMap_shortComplexMapOfHom :
    (X.cyclesIso f g f₃ n₀ n n₂ hn₁ hn₂).inv ≫
      ShortComplex.cyclesMap (shortComplexMapOfHom φ f g f₃ n₀ n n₂ hn₁ hn₂) =
      cyclesMapOfHom φ f g n ≫ (Y.cyclesIso f g f₃ n₀ n n₂ hn₁ hn₂).inv := by
  rw [← cancel_mono (Y.shortComplex f g f₃ n₀ n n₂ hn₁ hn₂).iCycles, Category.assoc,
    ShortComplex.cyclesMap_i, X.cyclesIso_inv_i_assoc f g f₃ n₀ n n₂ hn₁ hn₂, Category.assoc,
    Y.cyclesIso_inv_i f g f₃ n₀ n n₂ hn₁ hn₂]
  exact (cyclesMapOfHom_i φ f g n).symm

@[reassoc (attr := simp)]
lemma πE_EMap :
    X.πE f g f₃ n₀ n n₂ hn₁ hn₂ ≫ EMap φ f g f₃ n₀ n n₂ hn₁ hn₂ =
      cyclesMapOfHom φ f g n ≫ Y.πE f g f₃ n₀ n n₂ hn₁ hn₂ := by
  dsimp only [πE, EMap]
  -- as in Mathlib's `Page.lean`, the short complexes `X.shortComplex` only match the generic
  -- lemmas up to unfolding of instances, hence `erw`.
  erw [Category.assoc, ShortComplex.homologyπ_naturality,
    cyclesIso_inv_cyclesMap_shortComplexMapOfHom_assoc φ f g n f₃ n₀ n₂ hn₁ hn₂]

end Cycles

section Opcycles

section

variable {i j k : ι} (f : i ⟶ j) (g : j ⟶ k) (n : ℤ)

/-- The morphism `X.opcycles f g n ⟶ Y.opcycles f g n` induced by a morphism of spectral
objects. -/
noncomputable def opcyclesMapOfHom : X.opcycles f g n ⟶ Y.opcycles f g n :=
  X.descOpcycles f g (n - 1) n (sub_add_cancel n 1)
    ((φ.hom n).app (mk₁ f) ≫ Y.pOpcycles f g n) (by
      rw [← Category.assoc, φ.comm (n - 1) n (sub_add_cancel n 1) f g, Category.assoc,
        Y.δ_pOpcycles f g (n - 1) n (sub_add_cancel n 1), comp_zero])

@[reassoc (attr := simp)]
lemma p_opcyclesMapOfHom :
    X.pOpcycles f g n ≫ opcyclesMapOfHom φ f g n = (φ.hom n).app (mk₁ f) ≫ Y.pOpcycles f g n :=
  X.p_descOpcycles ..

@[simp]
lemma opcyclesMapOfHom_id : opcyclesMapOfHom (𝟙 X) f g n = 𝟙 _ := by
  rw [← cancel_epi (X.pOpcycles f g n), p_opcyclesMapOfHom, id_hom, NatTrans.id_app,
    Category.comp_id, Category.id_comp]

@[reassoc, simp]
lemma opcyclesMapOfHom_comp :
    opcyclesMapOfHom (φ ≫ ψ) f g n = opcyclesMapOfHom φ f g n ≫ opcyclesMapOfHom ψ f g n := by
  rw [← cancel_epi (X.pOpcycles f g n), p_opcyclesMapOfHom, p_opcyclesMapOfHom_assoc,
    p_opcyclesMapOfHom, comp_hom, NatTrans.comp_app, Category.assoc]

@[reassoc]
lemma opcyclesMapOfHom_fromOpcycles (fg : i ⟶ k) (h : f ≫ g = fg) :
    opcyclesMapOfHom φ f g n ≫ Y.fromOpcycles f g fg h n =
      X.fromOpcycles f g fg h n ≫ (φ.hom n).app (mk₁ fg) := by
  rw [← cancel_epi (X.pOpcycles f g n), p_opcyclesMapOfHom_assoc, p_fromOpcycles,
    p_fromOpcycles_assoc]
  exact ((φ.hom n).naturality _).symm

@[reassoc]
lemma opcyclesMap_opcyclesMapOfHom {i' j' k' : ι} (f' : i' ⟶ j') (g' : j' ⟶ k')
    (α : mk₂ f g ⟶ mk₂ f' g') :
    X.opcyclesMap f g f' g' α n ≫ opcyclesMapOfHom φ f' g' n =
      opcyclesMapOfHom φ f g n ≫ Y.opcyclesMap f g f' g' α n := by
  rw [← cancel_epi (X.pOpcycles f g n),
    X.p_opcyclesMap_assoc f g f' g' α (homMk₁ (α.app 0) (α.app 1) (naturality' α 0 1)) n,
    p_opcyclesMapOfHom, p_opcyclesMapOfHom_assoc,
    Y.p_opcyclesMap f g f' g' α (homMk₁ (α.app 0) (α.app 1) (naturality' α 0 1)) n,
    ← Category.assoc, ← Category.assoc]
  exact congrArg (· ≫ Y.pOpcycles f' g' n) ((φ.hom n).naturality _)

end

variable {i₀ i₁ i₂ i₃ : ι} (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
  (f₁₂ : i₀ ⟶ i₂) (h₁₂ : f₁ ≫ f₂ = f₁₂) (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂)

@[reassoc]
lemma opcyclesMapOfHom_opcyclesToE :
    opcyclesMapOfHom φ f₁₂ f₃ n₁ ≫ Y.opcyclesToE f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ n₂ hn₁ hn₂ =
      X.opcyclesToE f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ n₂ hn₁ hn₂ ≫ EMap φ f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ := by
  rw [← cancel_epi (X.pOpcycles f₁₂ f₃ n₁), p_opcyclesMapOfHom_assoc,
    Y.p_opcyclesToE f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ n₂ hn₁ hn₂,
    X.p_opcyclesToE_assoc f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ n₂ hn₁ hn₂,
    πE_EMap φ f₁ f₂ n₁ f₃ n₀ n₂ hn₁ hn₂, toCycles_cyclesMapOfHom_assoc]

variable (f₂₃ : i₁ ⟶ i₃) (h₂₃ : f₂ ≫ f₃ = f₂₃)

include h₁₂ h₂₃ in
/-- A morphism of spectral objects which is an isomorphism on `opZ^n(f₁, f₂ ≫ f₃)` and on
`E^n(f₁, f₂, f₃)` is an isomorphism on `opZ^n(f₁ ≫ f₂, f₃)`. -/
lemma isIso_opcyclesMapOfHom_of_isIso [IsIso (opcyclesMapOfHom φ f₁ f₂₃ n₁)]
    [IsIso (EMap φ f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂)] :
    IsIso (opcyclesMapOfHom φ f₁₂ f₃ n₁) := by
  let γ : X.shortComplexOpcyclesThreeδ₂Toδ₁ f₁ f₂ f₃ f₁₂ f₂₃ h₁₂ h₂₃ n₀ n₁ n₂ hn₁ hn₂ ⟶
      Y.shortComplexOpcyclesThreeδ₂Toδ₁ f₁ f₂ f₃ f₁₂ f₂₃ h₁₂ h₂₃ n₀ n₁ n₂ hn₁ hn₂ :=
    { τ₁ := opcyclesMapOfHom φ f₁ f₂₃ n₁
      τ₂ := opcyclesMapOfHom φ f₁₂ f₃ n₁
      τ₃ := EMap φ f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂
      comm₁₂ := (opcyclesMap_opcyclesMapOfHom φ _ _ n₁ _ _ _).symm
      comm₂₃ := opcyclesMapOfHom_opcyclesToE φ f₁ f₂ f₃ f₁₂ h₁₂ n₀ n₁ n₂ hn₁ hn₂ }
  have : IsIso γ.τ₁ := ‹_›
  have : IsIso γ.τ₃ := ‹_›
  exact ShortComplex.isIso₂_of_shortExact_of_isIso₁₃ γ
    (X.shortComplexOpcyclesThreeδ₂Toδ₁_shortExact ..)
    (Y.shortComplexOpcyclesThreeδ₂Toδ₁_shortExact ..)

end Opcycles

section Differentials

variable {i₀ i₁ i₂ i₃ i₄ i₅ : ι} (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
  (f₄ : i₃ ⟶ i₄) (f₅ : i₄ ⟶ i₅) (n₀ n₁ n₂ n₃ : ℤ)
  (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) (hn₃ : n₂ + 1 = n₃)

/-- **The maps `EMap` commute with the differentials.** -/
@[reassoc]
lemma d_EMap :
    X.d f₁ f₂ f₃ f₄ f₅ n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃ ≫ EMap φ f₁ f₂ f₃ n₁ n₂ n₃ hn₂ hn₃ =
      EMap φ f₃ f₄ f₅ n₀ n₁ n₂ hn₁ hn₂ ≫ Y.d f₁ f₂ f₃ f₄ f₅ n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃ := by
  rw [← cancel_epi (X.toCycles f₃ f₄ (f₃ ≫ f₄) rfl n₁ ≫ X.πE f₃ f₄ f₅ n₀ n₁ n₂ hn₁ hn₂),
    Category.assoc, X.toCycles_πE_d_assoc f₁ f₂ f₃ f₄ f₅ (f₁ ≫ f₂) rfl (f₃ ≫ f₄) rfl
      n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃,
    πE_EMap φ f₁ f₂ n₂ f₃ n₁ n₃ hn₂ hn₃, Category.assoc,
    πE_EMap_assoc φ f₃ f₄ n₁ f₅ n₀ n₂ hn₁ hn₂, toCycles_cyclesMapOfHom_assoc,
    toCycles_cyclesMapOfHom_assoc, φ.comm_assoc,
    Y.toCycles_πE_d f₁ f₂ f₃ f₄ f₅ (f₁ ≫ f₂) rfl (f₃ ≫ f₄) rfl n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃]

end Differentials

end CategoryTheory.Abelian.SpectralObject
