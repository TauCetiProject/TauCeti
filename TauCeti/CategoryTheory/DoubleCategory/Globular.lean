/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Iso
public import TauCeti.CategoryTheory.DoubleCategory.Transpose

/-!
# Globular cells of a strict double category

A horizontal globular cell of a strict double category `D` is a cell whose two vertical
boundaries are identity edges:

```text
       p
  a ──────→ b
  ‖         ‖
  ‖    α    ‖
  ‖         ‖
  a ──────→ b
       q
```

For fixed objects `a` and `b`, the horizontal edges `a ⟶ b` and the horizontal globular cells
between them form a category `D.HorizontalGlobular a b`, composed by vertical pasting and read
from top to bottom. Pasting horizontally with the vertical identity cell of an edge gives the
whiskering functors `D.hWhiskerLeft` and `D.hWhiskerRight` between these categories.

Dually, a vertical globular cell has identity horizontal boundaries; these form the category
`D.VerticalGlobular a b` of vertical edges `a ⟶ b`, composed by horizontal pasting and read from
left to right. It is the horizontal globular category of the transpose of `D`, so that every
construction on horizontal globular cells applies to vertical ones.

Isomorphisms in these categories are the invertible globular cells, through which a represented
double category compares an edge path with a single generating edge.

## Main declarations

* `TauCeti.StrictDoubleCategory.HorizontalGlobular` and its `Category` instance;
* `TauCeti.StrictDoubleCategory.hComp_comp_cell`: horizontal pasting of horizontal globular
  cells is functorial in both arguments;
* `TauCeti.StrictDoubleCategory.hWhiskerLeft` and `TauCeti.StrictDoubleCategory.hWhiskerRight`;
* `TauCeti.StrictDoubleCategory.VerticalGlobular`, with `VerticalGlobular.homEquiv_comp`
  describing its composition by horizontal pasting;
* `TauCeti.StrictDoubleCategory.HorizontalIso` and `TauCeti.StrictDoubleCategory.VerticalIso`:
  invertible globular cells.

## References

* A. D. Fairbanks and M. Shulman, *Doubly weak double categories*, Applied Categorical
  Structures **34** (2026), article 26; arXiv:2506.23651.
-/

public section

universe s u h v

namespace TauCeti

open CategoryTheory DoubleCategoryStruct

namespace StrictDoubleCategory

variable {O : Type u} {H : Category.{h} O} {V : Category.{v} O}
  (D : StrictDoubleCategory.{s} O H V)

/-- The horizontal edges from `a` to `b` of a strict double category `D`, as the objects of the
category of horizontal globular cells between them. -/
@[ext]
structure HorizontalGlobular (D : StrictDoubleCategory.{s} O H V) (a b : O) : Type h where
  /-- Regard a horizontal edge as an object of the horizontal globular category. -/
  mk ::
  /-- The underlying horizontal edge. -/
  edge : Edge H a b

/-- A horizontal globular cell from `p` to `q`: a cell with top `p`, bottom `q` and identity
vertical boundaries. -/
@[ext]
structure HorizontalGlobular.Hom {a b : O} (p q : D.HorizontalGlobular a b) where
  /-- The underlying cell of `D`. -/
  cell : D.Cell p.edge q.edge (edgeId V a) (edgeId V b)

/-- The horizontal globular cells between horizontal edges `a ⟶ b`, composed by vertical
pasting. The composite cell has vertical boundaries `𝟙 ≫ 𝟙`, which are transported back to
the identity edges. -/
instance (a b : O) : Category.{s} (D.HorizontalGlobular a b) where
  Hom := HorizontalGlobular.Hom D
  id p := ⟨D.vId p.edge⟩
  comp α β := ⟨(D.vComp α.cell β.cell).cast rfl rfl (Category.id_comp (self := V) _)
    (Category.id_comp (self := V) _)⟩
  id_comp α := by
    ext
    simp
  comp_id α := by
    ext
    simp
  assoc α β γ := by
    ext
    simp [vComp_assoc]

namespace HorizontalGlobular

variable {D} {a b : O}

@[ext]
theorem hom_ext {p q : D.HorizontalGlobular a b} {α β : p ⟶ q} (h : α.cell = β.cell) :
    α = β :=
  Hom.ext h

@[simp]
theorem id_cell (p : D.HorizontalGlobular a b) : (𝟙 p : p ⟶ p).cell = D.vId p.edge :=
  rfl

@[simp]
theorem comp_cell {p q r : D.HorizontalGlobular a b} (α : p ⟶ q) (β : q ⟶ r) :
    (α ≫ β).cell = (D.vComp α.cell β.cell).cast rfl rfl (Category.id_comp (self := V) _)
      (Category.id_comp (self := V) _) :=
  rfl

/-- Horizontal globular cells from `p` to `q` are the cells of `D` with boundary
`(p, q, 𝟙, 𝟙)`. -/
def homEquiv (p q : D.HorizontalGlobular a b) :
    (p ⟶ q) ≃ D.Cell p.edge q.edge (edgeId V a) (edgeId V b) where
  toFun α := α.cell
  invFun α := ⟨α⟩

@[simp]
theorem homEquiv_apply {p q : D.HorizontalGlobular a b} (α : p ⟶ q) :
    homEquiv p q α = α.cell :=
  (rfl)

@[simp]
theorem homEquiv_symm_apply_cell {p q : D.HorizontalGlobular a b}
    (α : D.Cell p.edge q.edge (edgeId V a) (edgeId V b)) :
    ((homEquiv p q).symm α).cell = α :=
  (rfl)

end HorizontalGlobular

variable {a b c : O}

/-- Horizontal pasting of horizontal globular cells is functorial in both arguments: pasting two
vertical composites side by side is the vertical composite of the side-by-side pastings. -/
theorem hComp_comp_cell {p q t : D.HorizontalGlobular a b} {p' q' t' : D.HorizontalGlobular b c}
    (α : p ⟶ q) (β : q ⟶ t) (γ : p' ⟶ q') (δ : q' ⟶ t') :
    D.hComp (α ≫ β).cell (γ ≫ δ).cell =
      (D.vComp (D.hComp α.cell γ.cell) (D.hComp β.cell δ.cell)).cast rfl rfl
        (Category.id_comp (self := V) _) (Category.id_comp (self := V) _) := by
  rw [HorizontalGlobular.comp_cell, HorizontalGlobular.comp_cell, hComp_cast_cast,
    ← D.interchange]

/-- Right whiskering of horizontal globular cells by a horizontal edge `r`: composition with
`r` on edges, and horizontal pasting with the vertical identity cell of `r` on cells. -/
@[expose]
def hWhiskerRight (r : Edge H b c) : D.HorizontalGlobular a b ⥤ D.HorizontalGlobular a c where
  obj p := ⟨edgeComp H p.edge r⟩
  map α := ⟨D.hComp α.cell (D.vId r)⟩
  map_id p := by
    ext
    exact (D.vId_comp p.edge r).symm
  map_comp α β := by
    ext
    have h := D.hComp_comp_cell α β (𝟙 (⟨r⟩ : D.HorizontalGlobular b c)) (𝟙 _)
    rwa [Category.comp_id] at h

/-- Left whiskering of horizontal globular cells by a horizontal edge `p`: composition with
`p` on edges, and horizontal pasting with the vertical identity cell of `p` on cells. -/
@[expose]
def hWhiskerLeft (p : Edge H a b) : D.HorizontalGlobular b c ⥤ D.HorizontalGlobular a c where
  obj q := ⟨edgeComp H p q.edge⟩
  map α := ⟨D.hComp (D.vId p) α.cell⟩
  map_id q := by
    ext
    exact (D.vId_comp p q.edge).symm
  map_comp α β := by
    ext
    have h := D.hComp_comp_cell (𝟙 (⟨p⟩ : D.HorizontalGlobular a b)) (𝟙 _) α β
    rwa [Category.comp_id] at h

@[simp]
theorem hWhiskerRight_obj (r : Edge H b c) (p : D.HorizontalGlobular a b) :
    (D.hWhiskerRight r).obj p = ⟨edgeComp H p.edge r⟩ :=
  rfl

@[simp]
theorem hWhiskerRight_map_cell (r : Edge H b c) {p q : D.HorizontalGlobular a b} (α : p ⟶ q) :
    ((D.hWhiskerRight r).map α).cell = D.hComp α.cell (D.vId r) :=
  rfl

@[simp]
theorem hWhiskerLeft_obj (p : Edge H a b) (q : D.HorizontalGlobular b c) :
    (D.hWhiskerLeft p).obj q = ⟨edgeComp H p q.edge⟩ :=
  rfl

@[simp]
theorem hWhiskerLeft_map_cell (p : Edge H a b) {q r : D.HorizontalGlobular b c} (α : q ⟶ r) :
    ((D.hWhiskerLeft p).map α).cell = D.hComp (D.vId p) α.cell :=
  rfl

/-- An invertible horizontal globular cell between the horizontal edges `p` and `q`: an
isomorphism from `p` to `q` in the horizontal globular category. -/
abbrev HorizontalIso (p q : Edge H a b) : Type s :=
  (⟨p⟩ : D.HorizontalGlobular a b) ≅ ⟨q⟩

/-- The vertical edges from `a` to `b` of a strict double category `D`, as the objects of the
category of vertical globular cells between them: cells with identity horizontal boundaries,
composed by horizontal pasting. It is the horizontal globular category of the transpose of
`D`. -/
abbrev VerticalGlobular (a b : O) : Type v :=
  D.transpose.HorizontalGlobular a b

namespace VerticalGlobular

variable {D} {a b : O}

/-- Vertical globular cells from `l` to `r` are the cells of `D` with boundary
`(𝟙, 𝟙, l, r)`. -/
def homEquiv (l r : D.VerticalGlobular a b) :
    (l ⟶ r) ≃ D.Cell (edgeId H a) (edgeId H b) l.edge r.edge :=
  HorizontalGlobular.homEquiv l r

theorem homEquiv_apply {l r : D.VerticalGlobular a b} (α : l ⟶ r) :
    homEquiv l r α = α.cell :=
  (rfl)

@[simp]
theorem homEquiv_symm_apply_cell {l r : D.VerticalGlobular a b}
    (α : D.Cell (edgeId H a) (edgeId H b) l.edge r.edge) :
    ((homEquiv l r).symm α).cell = α :=
  (rfl)

@[simp]
theorem homEquiv_id (l : D.VerticalGlobular a b) : homEquiv l l (𝟙 l) = D.hId l.edge :=
  (rfl)

/-- Composition of vertical globular cells is horizontal pasting, transported back from the
horizontal boundaries `𝟙 ≫ 𝟙` to identity edges. -/
@[simp]
theorem homEquiv_comp {l r t : D.VerticalGlobular a b} (α : l ⟶ r) (β : r ⟶ t) :
    homEquiv l t (α ≫ β) = (D.hComp (homEquiv l r α) (homEquiv r t β)).cast
      (Category.id_comp (self := H) _) (Category.id_comp (self := H) _) rfl rfl := by
  rw [homEquiv_apply, HorizontalGlobular.comp_cell]
  exact DoubleCategoryStruct.transpose_cast D.toDoubleCategoryStruct _ _ _ _ _

end VerticalGlobular

/-- An invertible vertical globular cell between the vertical edges `l` and `r`: an isomorphism
from `l` to `r` in the vertical globular category. -/
abbrev VerticalIso (l r : Edge V a b) : Type s :=
  D.transpose.HorizontalIso l r

end StrictDoubleCategory

end TauCeti
