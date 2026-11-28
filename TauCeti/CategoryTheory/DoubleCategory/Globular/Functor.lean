/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.DoubleCategory.Globular.Basic

/-!
# Strict double functors on globular cells

A strict double functor induces functors between the horizontal and vertical globular
hom-categories. The image of a globular cell is its image square, transported along
preservation of the identity edges. Thus invertible globular cells map to invertible
globular cells, and replacing any boundary of a square commutes with its image.

These operations let comparison isomorphisms for path representations be mapped using
ordinary functors and `Functor.mapIso`. Both directions are obtained from the horizontal
construction by transposing strict double functors.

The globular presentation follows A. D. Fairbanks and M. Shulman, *Doubly weak double
categories*, Applied Categorical Structures **34** (2026), article 26, Definitions 3.1–3.3.
-/

public section

universe s₁ s₂ s₃ u₁ u₂ u₃ h₁ h₂ h₃ v₁ v₂ v₃

namespace TauCeti.StrictDoubleFunctor

open CategoryTheory DoubleCategoryStruct StrictDoubleCategory

variable {O₁ : Type u₁} {H₁ : Category.{h₁} O₁} {V₁ : Category.{v₁} O₁}
  {O₂ : Type u₂} {H₂ : Category.{h₂} O₂} {V₂ : Category.{v₂} O₂}
  {O₃ : Type u₃} {H₃ : Category.{h₃} O₃} {V₃ : Category.{v₃} O₃}
  {D₁ : StrictDoubleCategory.{s₁} O₁ H₁ V₁}
  {D₂ : StrictDoubleCategory.{s₂} O₂ H₂ V₂}
  {D₃ : StrictDoubleCategory.{s₃} O₃ H₃ V₃}

/-- Transpose a strict double functor, exchanging its horizontal and vertical edge maps. -/
-- Exposure makes the object and edge endpoints of the transposed cell map compute.
@[expose]
def transpose (F : StrictDoubleFunctor D₁ D₂) :
    StrictDoubleFunctor D₁.transpose D₂.transpose where
  obj := F.obj
  hMap := F.vMap
  hMap_id := F.vMap_id
  hMap_comp := F.vMap_comp
  vMap := F.hMap
  vMap_id := F.hMap_id
  vMap_comp := F.hMap_comp
  map α := F.map α
  -- Unfolding the transpose and transport compares the same four boundary equalities
  -- in their exchanged order; no equality of cells is assumed.
  map_hId f := by
    simpa only [StrictDoubleCategory.transpose, DoubleCategoryStruct.transpose,
      Cell.cast] using F.map_vId f
  map_vId f := by
    simpa only [StrictDoubleCategory.transpose, DoubleCategoryStruct.transpose,
      Cell.cast] using F.map_hId f
  map_hComp α β := by
    simpa only [StrictDoubleCategory.transpose, DoubleCategoryStruct.transpose,
      Cell.cast] using F.map_vComp α β
  map_vComp α β := by
    simpa only [StrictDoubleCategory.transpose, DoubleCategoryStruct.transpose,
      Cell.cast] using F.map_hComp α β

@[simp]
theorem transpose_obj (F : StrictDoubleFunctor D₁ D₂) (a : O₁) :
    F.transpose.obj a = F.obj a := (rfl)

@[simp]
theorem transpose_hMap (F : StrictDoubleFunctor D₁ D₂) {a b : O₁} (f : Edge V₁ a b) :
    F.transpose.hMap f = F.vMap f := (rfl)

@[simp]
theorem transpose_vMap (F : StrictDoubleFunctor D₁ D₂) {a b : O₁} (f : Edge H₁ a b) :
    F.transpose.vMap f = F.hMap f := (rfl)

@[simp]
theorem transpose_map (F : StrictDoubleFunctor D₁ D₂) {a b c d : O₁}
    {p : Edge V₁ a b} {q : Edge V₁ c d} {l : Edge H₁ a c} {r : Edge H₁ b d}
    (α : D₁.transpose.Cell p q l r) : F.transpose.map α = F.map α := (rfl)

@[simp]
theorem transpose_id : (id D₁).transpose = id D₁.transpose := by
  apply hext <;> intros <;> rfl

@[simp]
theorem transpose_comp (F : StrictDoubleFunctor D₁ D₂) (G : StrictDoubleFunctor D₂ D₃) :
    (F.comp G).transpose = F.transpose.comp G.transpose := by
  apply hext <;> intros <;> rfl

/-- The functor on vertical globular cells, obtained by transposing both directions. -/
-- Exposure makes the vertical boundary endpoints of mapped cells compute.
@[expose]
def verticalGlobularFunctor (F : StrictDoubleFunctor D₁ D₂) (a b : O₁) :
    D₁.VerticalGlobular a b ⥤ D₂.VerticalGlobular (F.obj a) (F.obj b) :=
  F.transpose.horizontalGlobularFunctor a b

@[simp]
theorem verticalGlobularFunctor_obj_edge (F : StrictDoubleFunctor D₁ D₂) {a b : O₁}
    (p : D₁.VerticalGlobular a b) :
    ((F.verticalGlobularFunctor a b).obj p).edge = F.vMap p.edge := (rfl)

@[simp]
theorem verticalGlobularFunctor_map_cell (F : StrictDoubleFunctor D₁ D₂) {a b : O₁}
    {p q : D₁.VerticalGlobular a b} (α : p ⟶ q) :
    ((F.verticalGlobularFunctor a b).map α).cell =
      (F.map α.cell).cast (F.hMap_id a) (F.hMap_id b) rfl rfl := by
  -- Transposition swaps the order of the four equality eliminations in Cell.cast.
  simp only [verticalGlobularFunctor, horizontalGlobularFunctor, transpose,
    StrictDoubleCategory.transpose, DoubleCategoryStruct.transpose, Cell.cast]

/-- The identity double functor acts identically on vertical globular cells. -/
@[simp]
theorem id_verticalGlobularFunctor (a b : O₁) :
    (id D₁).verticalGlobularFunctor a b = 𝟭 (D₁.VerticalGlobular a b) := (rfl)

/-- Vertical globular action preserves composition of strict double functors. -/
@[simp]
theorem comp_verticalGlobularFunctor (F : StrictDoubleFunctor D₁ D₂)
    (G : StrictDoubleFunctor D₂ D₃) (a b : O₁) :
    (F.comp G).verticalGlobularFunctor a b =
      F.verticalGlobularFunctor a b ⋙ G.verticalGlobularFunctor (F.obj a) (F.obj b) := by
  -- The transposed functors have the same data; their preservation proofs are irrelevant.
  have h := comp_horizontalGlobularFunctor F.transpose G.transpose a b
  convert h using 1
  rfl

/-- The edge-composition equality of a strict double functor, as a natural comparison
between horizontal pasting before and after applying its globular action. -/
def horizontalCompComparison (F : StrictDoubleFunctor D₁ D₂) (a b c : O₁) :
    D₁.hCompFunctor ⋙ F.horizontalGlobularFunctor a c ≅
      (F.horizontalGlobularFunctor a b).prod (F.horizontalGlobularFunctor b c) ⋙
        D₂.hCompFunctor :=
  NatIso.ofComponents (fun pq ↦ eqToIso (HorizontalGlobular.ext
    (F.hMap_comp pq.1.edge pq.2.edge))) (by
      intro pq rs α
      dsimp only [Functor.comp_map, Functor.prod_map]
      apply (eqToIso (HorizontalGlobular.ext
        (F.hMap_comp pq.1.edge pq.2.edge))).inv_comp_eq.mp
      apply HorizontalGlobular.hom_ext
      dsimp only [horizontalGlobularFunctor, hCompFunctor, eqToIso]
      erw [HorizontalGlobular.eqToHom_comp_eqToHom_cell]
      simp)

/-- The comparison on a pair of edges is the equality morphism supplied by preservation
of horizontal composition. -/
@[simp]
theorem horizontalCompComparison_hom_app (F : StrictDoubleFunctor D₁ D₂) {a b c : O₁}
    (p : D₁.HorizontalGlobular a b) (q : D₁.HorizontalGlobular b c) :
    (F.horizontalCompComparison a b c).hom.app (p, q) =
      eqToHom (HorizontalGlobular.ext (F.hMap_comp p.edge q.edge)) := (rfl)

@[simp]
theorem horizontalCompComparison_inv_app (F : StrictDoubleFunctor D₁ D₂) {a b c : O₁}
    (p : D₁.HorizontalGlobular a b) (q : D₁.HorizontalGlobular b c) :
    (F.horizontalCompComparison a b c).inv.app (p, q) =
      eqToHom (HorizontalGlobular.ext (F.hMap_comp p.edge q.edge)).symm := (rfl)

/-- The natural comparison for vertical pasting of vertical globular cells. The pasting
bifunctors are the horizontal pasting bifunctors of the transposed double categories. -/
def verticalCompComparison (F : StrictDoubleFunctor D₁ D₂) (a b c : O₁) :
    D₁.transpose.hCompFunctor ⋙ F.verticalGlobularFunctor a c ≅
      (F.verticalGlobularFunctor a b).prod (F.verticalGlobularFunctor b c) ⋙
        D₂.transpose.hCompFunctor :=
  F.transpose.horizontalCompComparison a b c

/-- The vertical comparison on a pair of edges is the equality morphism supplied by
preservation of vertical composition. -/
@[simp]
theorem verticalCompComparison_hom_app (F : StrictDoubleFunctor D₁ D₂) {a b c : O₁}
    (p : D₁.VerticalGlobular a b) (q : D₁.VerticalGlobular b c) :
    (F.verticalCompComparison a b c).hom.app (p, q) =
      eqToHom (HorizontalGlobular.ext (F.vMap_comp p.edge q.edge)) := (rfl)

@[simp]
theorem verticalCompComparison_inv_app (F : StrictDoubleFunctor D₁ D₂) {a b c : O₁}
    (p : D₁.VerticalGlobular a b) (q : D₁.VerticalGlobular b c) :
    (F.verticalCompComparison a b c).inv.app (p, q) =
      eqToHom (HorizontalGlobular.ext (F.vMap_comp p.edge q.edge)).symm := (rfl)

section BoundaryChange

variable (F : StrictDoubleFunctor D₁ D₂) {a b c d : O₁}
  {p p' : Edge H₁ a b} {q q' : Edge H₁ c d}
  {l l' : Edge V₁ a c} {r r' : Edge V₁ b d}

/-- Mapping a square commutes with changing its top boundary by a globular isomorphism. -/
@[simp]
theorem map_changeTop (e : D₁.HorizontalIso p p') (α : D₁.Cell p q l r) :
    F.map (D₁.changeTop e α) =
      D₂.changeTop ((F.horizontalGlobularFunctor a b).mapIso e) (F.map α) := by
  dsimp only [horizontalGlobularFunctor, Functor.mapIso]
  simp [changeTop_def]

/-- Mapping a square commutes with changing its bottom boundary by a globular isomorphism. -/
@[simp]
theorem map_changeBottom (e : D₁.HorizontalIso q q') (α : D₁.Cell p q l r) :
    F.map (D₁.changeBottom e α) =
      D₂.changeBottom ((F.horizontalGlobularFunctor c d).mapIso e) (F.map α) := by
  dsimp only [horizontalGlobularFunctor, Functor.mapIso]
  simp [changeBottom_def]

/-- Mapping a square commutes with changing its left boundary by a globular isomorphism. -/
@[simp]
theorem map_changeLeft (e : D₁.VerticalIso l l') (α : D₁.Cell p q l r) :
    F.map (D₁.changeLeft e α) =
      D₂.changeLeft ((F.verticalGlobularFunctor a c).mapIso e) (F.map α) := by
  rw [D₁.changeLeft_def e α]
  erw [D₂.changeLeft_def]
  simp only [Functor.mapIso_inv, verticalGlobularFunctor_map_cell, map_cast]
  erw [map_hComp]
  erw [hComp_cast_left]
  erw [Cell.cast_cast, Cell.cast_cast]
  rfl

/-- Mapping a square commutes with changing its right boundary by a globular isomorphism. -/
@[simp]
theorem map_changeRight (e : D₁.VerticalIso r r') (α : D₁.Cell p q l r) :
    F.map (D₁.changeRight e α) =
      D₂.changeRight ((F.verticalGlobularFunctor b d).mapIso e) (F.map α) := by
  rw [D₁.changeRight_def e α]
  erw [D₂.changeRight_def]
  simp only [Functor.mapIso_hom, verticalGlobularFunctor_map_cell, map_cast]
  erw [map_hComp]
  erw [hComp_cast_right]
  erw [Cell.cast_cast, Cell.cast_cast]
  rfl

end BoundaryChange

end TauCeti.StrictDoubleFunctor
