/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Products.Basic
public import TauCeti.CategoryTheory.DoubleCategory.Basic

/-!
# Globular cells of a strict double category

A cell of a strict double category is *horizontally globular* when its two vertical boundaries
are identity edges. For objects `a` and `b` of a strict double category `D`, the horizontal edges
`a ⟶ b` and the horizontally globular cells between them form a category
`TauCeti.StrictDoubleCategory.HGlobular D a b`, with vertical pasting as composition (read from
top to bottom) and vertical identity cells as identities. Horizontal pasting of globular cells is
a functor `TauCeti.StrictDoubleCategory.hCompFunctor`, by the middle-four interchange law.

The isomorphisms of this category, `TauCeti.StrictDoubleCategory.HorizontalIso`, are the
invertible globular cells; they compare two horizontal edges with the same endpoints. Pasting a
globular cell onto the top or the bottom of an arbitrary cell changes that boundary, and an
invertible globular cell gives an equivalence `TauCeti.StrictDoubleCategory.changeTop` or
`TauCeti.StrictDoubleCategory.changeBottom` between the cells with the two boundaries.

The vertical counterparts are obtained by applying these constructions to the transpose
`TauCeti.StrictDoubleCategory.transpose`: a vertically globular cell, with identity horizontal
boundaries, read from left to right, is a horizontally globular cell of the transpose. This gives
`TauCeti.StrictDoubleCategory.VerticalIso`, `TauCeti.StrictDoubleCategory.changeLeft` and
`TauCeti.StrictDoubleCategory.changeRight`.

These categories and comparisons are the setting for the representations of the paths of an
implicit double category by single generators, in the sense of Fairbanks and Shulman.

## Main declarations

* `TauCeti.StrictDoubleCategory.HGlobular`: the category of horizontal edges and horizontally
  globular cells between two objects.
* `TauCeti.StrictDoubleCategory.hCompFunctor`: horizontal pasting of globular cells.
* `TauCeti.StrictDoubleCategory.HorizontalIso`, `TauCeti.StrictDoubleCategory.VerticalIso`:
  invertible globular cells.
* `TauCeti.StrictDoubleCategory.changeTop`, `TauCeti.StrictDoubleCategory.changeBottom`,
  `TauCeti.StrictDoubleCategory.changeLeft`, `TauCeti.StrictDoubleCategory.changeRight`:
  changing one boundary of a cell along an invertible globular cell.

## References

* A. D. Fairbanks and M. Shulman, *Doubly weak double categories*, Applied Categorical
  Structures **34** (2026), article 26; arXiv:2506.23651, Definitions 3.1–3.3.
-/

@[expose] public section

universe s u h v

namespace TauCeti

open CategoryTheory DoubleCategoryStruct

namespace StrictDoubleCategory

variable {O : Type u} {H : Category.{h} O} {V : Category.{v} O}

/-- A horizontal edge `a ⟶ b` of the strict double category `D`, as an object of the category of
horizontally globular cells from `a` to `b`. -/
@[ext]
structure HGlobular (D : StrictDoubleCategory.{s} O H V) (a b : O) : Type h where
  /-- The underlying horizontal edge. -/
  edge : Edge H a b

variable {D : StrictDoubleCategory.{s} O H V} {a b c : O}

/-- The category of horizontally globular cells from `a` to `b`: a morphism from `p` to `q` is
a cell with top `p`, bottom `q` and identity vertical boundaries, composition is vertical
pasting and the identities are the vertical identity cells. -/
instance : Category.{s} (D.HGlobular a b) where
  Hom p q := D.Cell p.edge q.edge (edgeId V a) (edgeId V b)
  id p := D.vId p.edge
  comp α β := (D.vComp α β).cast rfl rfl (Category.id_comp (self := V) _)
    (Category.id_comp (self := V) _)
  id_comp α := by simp
  comp_id α := by simp
  assoc α β γ := by simp [vComp_assoc]

namespace HGlobular

theorem id_def (p : D.HGlobular a b) : 𝟙 p = D.vId p.edge :=
  rfl

theorem comp_def {p q r : D.HGlobular a b} (α : p ⟶ q) (β : q ⟶ r) :
    α ≫ β = (D.vComp α β).cast rfl rfl (Category.id_comp (self := V) _)
      (Category.id_comp (self := V) _) :=
  rfl

/-- The horizontal composite of two horizontal edges, as an object of the globular category. -/
def hComp (p : D.HGlobular a b) (q : D.HGlobular b c) : D.HGlobular a c :=
  ⟨edgeComp H p.edge q.edge⟩

@[simp]
theorem hComp_edge (p : D.HGlobular a b) (q : D.HGlobular b c) :
    (p.hComp q).edge = edgeComp H p.edge q.edge :=
  rfl

end HGlobular

variable (D) in
/-- Horizontal pasting of horizontally globular cells, as a functor on pairs. Its functoriality
is the middle-four interchange law together with the compatibility of vertical identity cells
with composition of horizontal edges. -/
def hCompFunctor (a b c : O) : D.HGlobular a b × D.HGlobular b c ⥤ D.HGlobular a c where
  obj p := p.1.hComp p.2
  map α := D.hComp α.1 α.2
  map_id p := (D.vId_comp p.1.edge p.2.edge).symm
  map_comp α β := by
    simp only [prod_comp, HGlobular.comp_def, hComp_cast_cast]
    rw [← D.interchange]
    rfl

@[simp]
theorem hCompFunctor_obj (p : D.HGlobular a b × D.HGlobular b c) :
    (D.hCompFunctor a b c).obj p = p.1.hComp p.2 :=
  rfl

@[simp]
theorem hCompFunctor_map {p q : D.HGlobular a b × D.HGlobular b c} (α : p ⟶ q) :
    (D.hCompFunctor a b c).map α = D.hComp α.1 α.2 :=
  rfl

variable (D) in
/-- An invertible horizontally globular cell from `p` to `q`: an isomorphism in the category of
horizontally globular cells. -/
abbrev HorizontalIso (p q : Edge H a b) : Type s :=
  (⟨p⟩ : D.HGlobular a b) ≅ ⟨q⟩

section Paste

variable {c d : O} {l : Edge V a c} {r : Edge V b d}

/-- Paste a horizontally globular cell `σ` onto the top of a cell `α`, so that the top boundary
of `α` changes from the target of `σ` to its source. -/
def pasteTop {p p' : D.HGlobular a b} {q : Edge H c d} (σ : p ⟶ p')
    (α : D.Cell p'.edge q l r) : D.Cell p.edge q l r :=
  (D.vComp σ α).cast rfl rfl (Category.id_comp (self := V) l) (Category.id_comp (self := V) r)

/-- Paste a horizontally globular cell `τ` onto the bottom of a cell `α`, so that the bottom
boundary of `α` changes from the source of `τ` to its target. -/
def pasteBottom {p : Edge H a b} {q q' : D.HGlobular c d} (α : D.Cell p q.edge l r)
    (τ : q ⟶ q') : D.Cell p q'.edge l r :=
  (D.vComp α τ).cast rfl rfl (Category.comp_id (self := V) l) (Category.comp_id (self := V) r)

@[simp]
theorem pasteTop_id {p : D.HGlobular a b} {q : Edge H c d} (α : D.Cell p.edge q l r) :
    D.pasteTop (𝟙 p) α = α := by
  simp [pasteTop, HGlobular.id_def]

@[simp]
theorem pasteTop_comp {p p' p'' : D.HGlobular a b} {q : Edge H c d} (σ : p ⟶ p')
    (σ' : p' ⟶ p'') (α : D.Cell p''.edge q l r) :
    D.pasteTop (σ ≫ σ') α = D.pasteTop σ (D.pasteTop σ' α) := by
  simp [pasteTop, HGlobular.comp_def, vComp_assoc]

@[simp]
theorem pasteBottom_id {p : Edge H a b} {q : D.HGlobular c d} (α : D.Cell p q.edge l r) :
    D.pasteBottom α (𝟙 q) = α := by
  simp [pasteBottom, HGlobular.id_def]

@[simp]
theorem pasteBottom_comp {p : Edge H a b} {q q' q'' : D.HGlobular c d} (α : D.Cell p q.edge l r)
    (τ : q ⟶ q') (τ' : q' ⟶ q'') :
    D.pasteBottom α (τ ≫ τ') = D.pasteBottom (D.pasteBottom α τ) τ' := by
  simp [pasteBottom, HGlobular.comp_def, vComp_assoc]

/-- Pasting globular cells onto the top and onto the bottom of a cell commute. -/
theorem pasteBottom_pasteTop {p p' : D.HGlobular a b} {q q' : D.HGlobular c d} (σ : p ⟶ p')
    (α : D.Cell p'.edge q.edge l r) (τ : q ⟶ q') :
    D.pasteBottom (D.pasteTop σ α) τ = D.pasteTop σ (D.pasteBottom α τ) := by
  simp [pasteTop, pasteBottom, vComp_assoc]

/-- On horizontally globular cells, pasting onto the top is composition in the globular
category. -/
theorem pasteTop_eq_comp {p p' p'' : D.HGlobular a b} (σ : p ⟶ p') (α : p' ⟶ p'') :
    D.pasteTop σ α = σ ≫ α :=
  rfl

/-- On horizontally globular cells, pasting onto the bottom is composition in the globular
category. -/
theorem pasteBottom_eq_comp {p p' p'' : D.HGlobular a b} (α : p ⟶ p') (τ : p' ⟶ p'') :
    D.pasteBottom α τ = α ≫ τ :=
  rfl

/-- Changing the top boundary of cells along an invertible horizontally globular cell. -/
def changeTop {p p' : Edge H a b} (e : D.HorizontalIso p p') {q : Edge H c d} :
    D.Cell p q l r ≃ D.Cell p' q l r where
  toFun := D.pasteTop e.inv
  invFun := D.pasteTop e.hom
  left_inv α := by simp [← pasteTop_comp]
  right_inv α := by simp [← pasteTop_comp]

/-- Changing the bottom boundary of cells along an invertible horizontally globular cell. -/
def changeBottom {q q' : Edge H c d} (e : D.HorizontalIso q q') {p : Edge H a b} :
    D.Cell p q l r ≃ D.Cell p q' l r where
  toFun α := D.pasteBottom α e.hom
  invFun α := D.pasteBottom α e.inv
  left_inv α := by simp [← pasteBottom_comp]
  right_inv α := by simp [← pasteBottom_comp]

variable {p p' p'' : Edge H a b} {q q' q'' : Edge H c d}

@[simp]
theorem changeTop_apply (e : D.HorizontalIso p p') (α : D.Cell p q l r) :
    D.changeTop e α = D.pasteTop e.inv α :=
  rfl

@[simp]
theorem changeTop_symm_apply (e : D.HorizontalIso p p') (α : D.Cell p' q l r) :
    (D.changeTop e).symm α = D.pasteTop e.hom α :=
  rfl

@[simp]
theorem changeBottom_apply (e : D.HorizontalIso q q') (α : D.Cell p q l r) :
    D.changeBottom e α = D.pasteBottom α e.hom :=
  rfl

@[simp]
theorem changeBottom_symm_apply (e : D.HorizontalIso q q') (α : D.Cell p q' l r) :
    (D.changeBottom e).symm α = D.pasteBottom α e.inv :=
  rfl

@[simp]
theorem changeTop_refl :
    D.changeTop (Iso.refl (⟨p⟩ : D.HGlobular a b)) = Equiv.refl (D.Cell p q l r) := by
  ext α
  exact D.pasteTop_id α

theorem changeTop_trans (e : D.HorizontalIso p p') (e' : D.HorizontalIso p' p'') :
    D.changeTop (e ≪≫ e') = (D.changeTop e).trans (D.changeTop e' (q := q) (l := l) (r := r)) := by
  ext α
  simp

@[simp]
theorem changeTop_symm (e : D.HorizontalIso p p') :
    D.changeTop e.symm = (D.changeTop e (q := q) (l := l) (r := r)).symm :=
  rfl

@[simp]
theorem changeBottom_refl :
    D.changeBottom (Iso.refl (⟨q⟩ : D.HGlobular c d)) = Equiv.refl (D.Cell p q l r) := by
  ext α
  exact D.pasteBottom_id α

theorem changeBottom_trans (e : D.HorizontalIso q q') (e' : D.HorizontalIso q' q'') :
    D.changeBottom (e ≪≫ e') =
      (D.changeBottom e).trans (D.changeBottom e' (p := p) (l := l) (r := r)) := by
  ext α
  simp

@[simp]
theorem changeBottom_symm (e : D.HorizontalIso q q') :
    D.changeBottom e.symm = (D.changeBottom e (p := p) (l := l) (r := r)).symm :=
  rfl

/-- Changing the top and the bottom boundary of a cell commute. -/
theorem changeBottom_changeTop (e : D.HorizontalIso p p') (e' : D.HorizontalIso q q')
    (α : D.Cell p q l r) :
    D.changeBottom e' (D.changeTop e α) = D.changeTop e (D.changeBottom e' α) :=
  D.pasteBottom_pasteTop e.inv α e'.hom

end Paste

/-! ### Vertically globular cells -/

variable (D) in
/-- An invertible vertically globular cell from `l` to `r`, read from left to right: a cell with
left boundary `l`, right boundary `r` and identity horizontal boundaries, invertible for
horizontal pasting. It is an invertible horizontally globular cell of the transpose. -/
abbrev VerticalIso (l r : Edge V a b) : Type s :=
  D.transpose.HorizontalIso l r

section Vertical

variable {c d : O} {p : Edge H a b} {q : Edge H c d} {l l' l'' : Edge V a c}
  {r r' r'' : Edge V b d}

/-- Changing the left boundary of cells along an invertible vertically globular cell. -/
def changeLeft (e : D.VerticalIso l l') : D.Cell p q l r ≃ D.Cell p q l' r :=
  D.transpose.changeTop e

/-- Changing the right boundary of cells along an invertible vertically globular cell. -/
def changeRight (e : D.VerticalIso r r') : D.Cell p q l r ≃ D.Cell p q l r' :=
  D.transpose.changeBottom e

/-- Changing the left boundary is horizontal pasting with the inverse cell, followed by the unit
law for horizontal edges. -/
@[simp]
theorem changeLeft_apply (e : D.VerticalIso l l') (α : D.Cell p q l r) :
    D.changeLeft e α = (D.hComp e.inv α).cast (Category.id_comp (self := H) p)
      (Category.id_comp (self := H) q) rfl rfl :=
  transpose_cast (D := D.toDoubleCategoryStruct) rfl rfl (Category.id_comp (self := H) p)
    (Category.id_comp (self := H) q) (D.hComp e.inv α)

/-- Changing the right boundary is horizontal pasting with the cell, followed by the unit law
for horizontal edges. -/
@[simp]
theorem changeRight_apply (e : D.VerticalIso r r') (α : D.Cell p q l r) :
    D.changeRight e α = (D.hComp α e.hom).cast (Category.comp_id (self := H) p)
      (Category.comp_id (self := H) q) rfl rfl :=
  transpose_cast (D := D.toDoubleCategoryStruct) rfl rfl (Category.comp_id (self := H) p)
    (Category.comp_id (self := H) q) (D.hComp α e.hom)

/-- Undoing a change of the left boundary is horizontal pasting with the cell, followed by the
unit law for horizontal edges. -/
@[simp]
theorem changeLeft_symm_apply (e : D.VerticalIso l l') (α : D.Cell p q l' r) :
    (D.changeLeft e).symm α = (D.hComp e.hom α).cast (Category.id_comp (self := H) p)
      (Category.id_comp (self := H) q) rfl rfl :=
  transpose_cast (D := D.toDoubleCategoryStruct) rfl rfl (Category.id_comp (self := H) p)
    (Category.id_comp (self := H) q) (D.hComp e.hom α)

/-- Undoing a change of the right boundary is horizontal pasting with the inverse cell, followed
by the unit law for horizontal edges. -/
@[simp]
theorem changeRight_symm_apply (e : D.VerticalIso r r') (α : D.Cell p q l r') :
    (D.changeRight e).symm α = (D.hComp α e.inv).cast (Category.comp_id (self := H) p)
      (Category.comp_id (self := H) q) rfl rfl :=
  transpose_cast (D := D.toDoubleCategoryStruct) rfl rfl (Category.comp_id (self := H) p)
    (Category.comp_id (self := H) q) (D.hComp α e.inv)

@[simp]
theorem changeLeft_refl :
    D.changeLeft (Iso.refl (⟨l⟩ : D.transpose.HGlobular a c)) =
      Equiv.refl (D.Cell p q l r) :=
  D.transpose.changeTop_refl

theorem changeLeft_trans (e : D.VerticalIso l l') (e' : D.VerticalIso l' l'') :
    D.changeLeft (e ≪≫ e') = (D.changeLeft e).trans (D.changeLeft e' (p := p) (q := q) (r := r)) :=
  D.transpose.changeTop_trans e e'

@[simp]
theorem changeLeft_symm (e : D.VerticalIso l l') :
    D.changeLeft e.symm = (D.changeLeft e (p := p) (q := q) (r := r)).symm :=
  rfl

@[simp]
theorem changeRight_refl :
    D.changeRight (Iso.refl (⟨r⟩ : D.transpose.HGlobular b d)) =
      Equiv.refl (D.Cell p q l r) :=
  D.transpose.changeBottom_refl

theorem changeRight_trans (e : D.VerticalIso r r') (e' : D.VerticalIso r' r'') :
    D.changeRight (e ≪≫ e') =
      (D.changeRight e).trans (D.changeRight e' (p := p) (q := q) (l := l)) :=
  D.transpose.changeBottom_trans e e'

@[simp]
theorem changeRight_symm (e : D.VerticalIso r r') :
    D.changeRight e.symm = (D.changeRight e (p := p) (q := q) (l := l)).symm :=
  rfl

/-- Changing the left and the right boundary of a cell commute. -/
theorem changeRight_changeLeft (e : D.VerticalIso l l') (e' : D.VerticalIso r r')
    (α : D.Cell p q l r) :
    D.changeRight e' (D.changeLeft e α) = D.changeLeft e (D.changeRight e' α) :=
  D.transpose.changeBottom_changeTop e e' α

end Vertical

end StrictDoubleCategory

end TauCeti
