/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Products.Basic
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
from top to bottom. Horizontal pasting is a functor `D.hCompFunctor` from the product of two
such categories, and restricting it to the vertical identity cell of a fixed edge gives the
whiskering functors `D.hWhiskerLeft` and `D.hWhiskerRight`.

Dually, a vertical globular cell has identity horizontal boundaries; these form the category
`D.VerticalGlobular a b` of vertical edges `a ⟶ b`, composed by horizontal pasting and read from
left to right. It is the horizontal globular category of the transpose of `D`, so that every
construction on horizontal globular cells applies to vertical ones.

Isomorphisms in these categories are the invertible globular cells, through which a represented
double category compares an edge path with a single generating edge. Pasting an invertible
globular cell onto a side of an arbitrary cell replaces that boundary edge by an isomorphic one.

## Main declarations

* `TauCeti.StrictDoubleCategory.HorizontalGlobular` and its `Category` instance;
* `TauCeti.StrictDoubleCategory.hCompFunctor`: horizontal pasting of horizontal globular cells,
  as a functor in both arguments;
* `TauCeti.StrictDoubleCategory.hWhiskerLeft` and `TauCeti.StrictDoubleCategory.hWhiskerRight`;
* `TauCeti.StrictDoubleCategory.VerticalGlobular`, with `VerticalGlobular.homEquiv_comp`
  describing its composition by horizontal pasting;
* `TauCeti.StrictDoubleCategory.HorizontalIso` and `TauCeti.StrictDoubleCategory.VerticalIso`:
  invertible globular cells.
* `TauCeti.StrictDoubleCategory.changeTop`, `changeBottom`, `changeLeft` and `changeRight`:
  replacing a boundary of a cell along an invertible globular cell. `changeTop_vComp`,
  `changeBottom_vComp`, `changeLeft_hComp` and `changeRight_hComp` move a change of an outer
  edge of a pasting onto the cell carrying that edge, and `vComp_changeBottom_changeTop` and
  `hComp_changeRight_changeLeft` show that changing a shared edge on both sides leaves a
  pasting unchanged. Changes of two different boundaries commute: `changeBottom_changeTop` and
  `changeRight_changeLeft` for opposite boundaries, and `changeLeft_changeTop`,
  `changeRight_changeTop`, `changeRight_changeBottom` and `changeLeft_changeBottom` for adjacent
  ones.

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

/-- Horizontal pasting of horizontal globular cells, as a functor of both arguments: composition
on edges and horizontal pasting on cells. -/
@[expose]
def hCompFunctor :
    D.HorizontalGlobular a b × D.HorizontalGlobular b c ⥤ D.HorizontalGlobular a c where
  obj p := ⟨edgeComp H p.1.edge p.2.edge⟩
  map α := ⟨D.hComp α.1.cell α.2.cell⟩
  map_id p := by
    ext
    rw [prod_id, HorizontalGlobular.id_cell, HorizontalGlobular.id_cell,
      HorizontalGlobular.id_cell, D.vId_comp]
  map_comp α β := by
    ext
    rw [prod_comp, HorizontalGlobular.comp_cell, HorizontalGlobular.comp_cell,
      HorizontalGlobular.comp_cell, hComp_cast_cast, ← D.interchange]

@[simp]
theorem hCompFunctor_obj (p : D.HorizontalGlobular a b × D.HorizontalGlobular b c) :
    D.hCompFunctor.obj p = ⟨edgeComp H p.1.edge p.2.edge⟩ :=
  rfl

@[simp]
theorem hCompFunctor_map_cell {p q : D.HorizontalGlobular a b × D.HorizontalGlobular b c}
    (α : p ⟶ q) : (D.hCompFunctor.map α).cell = D.hComp α.1.cell α.2.cell :=
  rfl

/-- Right whiskering of horizontal globular cells by a horizontal edge `r`: composition with
`r` on edges, and horizontal pasting with the vertical identity cell of `r` on cells. It is the
restriction of `D.hCompFunctor` to the identity of `r` in the second argument. -/
@[expose]
def hWhiskerRight (r : Edge H b c) : D.HorizontalGlobular a b ⥤ D.HorizontalGlobular a c :=
  Prod.sectL _ (⟨r⟩ : D.HorizontalGlobular b c) ⋙ D.hCompFunctor

/-- Left whiskering of horizontal globular cells by a horizontal edge `p`: composition with
`p` on edges, and horizontal pasting with the vertical identity cell of `p` on cells. It is the
restriction of `D.hCompFunctor` to the identity of `p` in the first argument. -/
@[expose]
def hWhiskerLeft (p : Edge H a b) : D.HorizontalGlobular b c ⥤ D.HorizontalGlobular a c :=
  Prod.sectR (⟨p⟩ : D.HorizontalGlobular a b) _ ⋙ D.hCompFunctor

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
theorem homEquiv_id (l : D.VerticalGlobular a b) : homEquiv l l (𝟙 l) = D.hId l.edge := by
  rw [homEquiv_apply, HorizontalGlobular.id_cell]
  exact DoubleCategoryStruct.transpose_vId D.toDoubleCategoryStruct l.edge

/-- Composition of vertical globular cells is horizontal pasting, transported back from the
horizontal boundaries `𝟙 ≫ 𝟙` to identity edges. -/
@[simp]
theorem homEquiv_comp {l r t : D.VerticalGlobular a b} (α : l ⟶ r) (β : r ⟶ t) :
    homEquiv l t (α ≫ β) = (D.hComp (homEquiv l r α) (homEquiv r t β)).cast
      (Category.id_comp (self := H) _) (Category.id_comp (self := H) _) rfl rfl := by
  rw [homEquiv_apply, homEquiv_apply, homEquiv_apply, HorizontalGlobular.comp_cell]
  exact (DoubleCategoryStruct.transpose_cast D.toDoubleCategoryStruct _ _ _ _ _).trans
    (congrArg _ (DoubleCategoryStruct.transpose_vComp D.toDoubleCategoryStruct α.cell β.cell))

end VerticalGlobular

/-- An invertible vertical globular cell between the vertical edges `l` and `r`: an isomorphism
from `l` to `r` in the vertical globular category. -/
abbrev VerticalIso (l r : Edge V a b) : Type s :=
  D.transpose.HorizontalIso l r

section BoundaryChange

variable {a b c d : O} {p p' p'' : Edge H a b} {q q' q'' : Edge H c d} {l l' l'' : Edge V a c}
  {r r' r'' : Edge V b d}

/-- Replace the top boundary `p` of a cell by `p'` along an invertible horizontal globular cell
`e : p ≅ p'`, by pasting the inverse of `e` on top of the cell. -/
def changeTop (e : D.HorizontalIso p p') (α : D.Cell p q l r) : D.Cell p' q l r :=
  (D.vComp e.inv.cell α).cast rfl rfl (Category.id_comp (self := V) l)
    (Category.id_comp (self := V) r)

/-- Replace the bottom boundary `q` of a cell by `q'` along an invertible horizontal globular cell
`e : q ≅ q'`, by pasting `e` below the cell. -/
def changeBottom (e : D.HorizontalIso q q') (α : D.Cell p q l r) : D.Cell p q' l r :=
  (D.vComp α e.hom.cell).cast rfl rfl (Category.comp_id (self := V) l)
    (Category.comp_id (self := V) r)

/-- Replace the left boundary `l` of a cell by `l'` along an invertible vertical globular cell
`e : l ≅ l'`, by pasting the inverse of `e` to the left of the cell. It is the change of top
boundary in the transpose. -/
def changeLeft (e : D.VerticalIso l l') (α : D.Cell p q l r) : D.Cell p q l' r :=
  D.transpose.changeTop e α

/-- Replace the right boundary `r` of a cell by `r'` along an invertible vertical globular cell
`e : r ≅ r'`, by pasting `e` to the right of the cell. It is the change of bottom boundary in the
transpose. -/
def changeRight (e : D.VerticalIso r r') (α : D.Cell p q l r) : D.Cell p q l r' :=
  D.transpose.changeBottom e α

/-- Changing the top boundary pastes the inverse globular cell on top. -/
theorem changeTop_def (e : D.HorizontalIso p p') (α : D.Cell p q l r) :
    D.changeTop e α = (D.vComp e.inv.cell α).cast rfl rfl (Category.id_comp (self := V) l)
      (Category.id_comp (self := V) r) :=
  (rfl)

/-- Changing the bottom boundary pastes the globular cell below. -/
theorem changeBottom_def (e : D.HorizontalIso q q') (α : D.Cell p q l r) :
    D.changeBottom e α = (D.vComp α e.hom.cell).cast rfl rfl (Category.comp_id (self := V) l)
      (Category.comp_id (self := V) r) :=
  (rfl)

/-- Changing the left boundary pastes the inverse vertical globular cell on the left, by
horizontal pasting in `D`. -/
theorem changeLeft_def (e : D.VerticalIso l l') (α : D.Cell p q l r) :
    D.changeLeft e α = (D.hComp e.inv.cell α).cast (Category.id_comp (self := H) p)
      (Category.id_comp (self := H) q) rfl rfl :=
  (D.transpose.changeTop_def e α).trans
    (DoubleCategoryStruct.transpose_cast D.toDoubleCategoryStruct _ _ _ _ _)

/-- Changing the right boundary pastes the vertical globular cell on the right, by horizontal
pasting in `D`. -/
theorem changeRight_def (e : D.VerticalIso r r') (α : D.Cell p q l r) :
    D.changeRight e α = (D.hComp α e.hom.cell).cast (Category.comp_id (self := H) p)
      (Category.comp_id (self := H) q) rfl rfl :=
  (D.transpose.changeBottom_def e α).trans
    (DoubleCategoryStruct.transpose_cast D.toDoubleCategoryStruct _ _ _ _ _)

@[simp]
theorem changeTop_refl (α : D.Cell p q l r) : D.changeTop (Iso.refl _) α = α := by
  simp [changeTop_def]

@[simp]
theorem changeBottom_refl (α : D.Cell p q l r) : D.changeBottom (Iso.refl _) α = α := by
  simp [changeBottom_def]

@[simp]
theorem changeTop_trans (e : D.HorizontalIso p p') (e' : D.HorizontalIso p' p'')
    (α : D.Cell p q l r) : D.changeTop (e ≪≫ e') α = D.changeTop e' (D.changeTop e α) := by
  simp [changeTop_def, vComp_assoc]

@[simp]
theorem changeBottom_trans (e : D.HorizontalIso q q') (e' : D.HorizontalIso q' q'')
    (α : D.Cell p q l r) :
    D.changeBottom (e ≪≫ e') α = D.changeBottom e' (D.changeBottom e α) := by
  simp [changeBottom_def, vComp_assoc]

@[simp]
theorem changeTop_symm_changeTop (e : D.HorizontalIso p p') (α : D.Cell p q l r) :
    D.changeTop e.symm (D.changeTop e α) = α := by
  rw [← changeTop_trans, Iso.self_symm_id, changeTop_refl]

@[simp]
theorem changeTop_changeTop_symm (e : D.HorizontalIso p p') (α : D.Cell p' q l r) :
    D.changeTop e (D.changeTop e.symm α) = α := by
  rw [← changeTop_trans, Iso.symm_self_id, changeTop_refl]

@[simp]
theorem changeBottom_symm_changeBottom (e : D.HorizontalIso q q') (α : D.Cell p q l r) :
    D.changeBottom e.symm (D.changeBottom e α) = α := by
  rw [← changeBottom_trans, Iso.self_symm_id, changeBottom_refl]

@[simp]
theorem changeBottom_changeBottom_symm (e : D.HorizontalIso q q') (α : D.Cell p q' l r) :
    D.changeBottom e (D.changeBottom e.symm α) = α := by
  rw [← changeBottom_trans, Iso.symm_self_id, changeBottom_refl]

@[simp]
theorem changeLeft_refl (α : D.Cell p q l r) : D.changeLeft (Iso.refl _) α = α :=
  D.transpose.changeTop_refl α

@[simp]
theorem changeRight_refl (α : D.Cell p q l r) : D.changeRight (Iso.refl _) α = α :=
  D.transpose.changeBottom_refl α

@[simp]
theorem changeLeft_trans (e : D.VerticalIso l l') (e' : D.VerticalIso l' l'')
    (α : D.Cell p q l r) : D.changeLeft (e ≪≫ e') α = D.changeLeft e' (D.changeLeft e α) :=
  D.transpose.changeTop_trans e e' α

@[simp]
theorem changeRight_trans (e : D.VerticalIso r r') (e' : D.VerticalIso r' r'')
    (α : D.Cell p q l r) : D.changeRight (e ≪≫ e') α = D.changeRight e' (D.changeRight e α) :=
  D.transpose.changeBottom_trans e e' α

@[simp]
theorem changeLeft_symm_changeLeft (e : D.VerticalIso l l') (α : D.Cell p q l r) :
    D.changeLeft e.symm (D.changeLeft e α) = α :=
  D.transpose.changeTop_symm_changeTop e α

@[simp]
theorem changeLeft_changeLeft_symm (e : D.VerticalIso l l') (α : D.Cell p q l' r) :
    D.changeLeft e (D.changeLeft e.symm α) = α :=
  D.transpose.changeTop_changeTop_symm e α

@[simp]
theorem changeRight_symm_changeRight (e : D.VerticalIso r r') (α : D.Cell p q l r) :
    D.changeRight e.symm (D.changeRight e α) = α :=
  D.transpose.changeBottom_symm_changeBottom e α

@[simp]
theorem changeRight_changeRight_symm (e : D.VerticalIso r r') (α : D.Cell p q l r') :
    D.changeRight e (D.changeRight e.symm α) = α :=
  D.transpose.changeBottom_changeBottom_symm e α

/-- Changing the top boundary along the globular isomorphism induced by an equality of edges
transports the cell along that equality. -/
@[simp]
theorem changeTop_eqToIso (h : (⟨p⟩ : D.HorizontalGlobular a b) = ⟨p'⟩) (α : D.Cell p q l r) :
    D.changeTop (eqToIso h) α = α.cast (congrArg HorizontalGlobular.edge h) rfl rfl rfl := by
  cases h
  simp

/-- Changing the bottom boundary along the globular isomorphism induced by an equality of edges
transports the cell along that equality. -/
@[simp]
theorem changeBottom_eqToIso (h : (⟨q⟩ : D.HorizontalGlobular c d) = ⟨q'⟩)
    (α : D.Cell p q l r) :
    D.changeBottom (eqToIso h) α = α.cast rfl (congrArg HorizontalGlobular.edge h) rfl rfl := by
  cases h
  simp

/-- Changing the left boundary along the globular isomorphism induced by an equality of edges
transports the cell along that equality. -/
@[simp]
theorem changeLeft_eqToIso (h : (⟨l⟩ : D.VerticalGlobular a c) = ⟨l'⟩) (α : D.Cell p q l r) :
    D.changeLeft (eqToIso h) α = α.cast rfl rfl (congrArg HorizontalGlobular.edge h) rfl :=
  (D.transpose.changeTop_eqToIso h α).trans
    (DoubleCategoryStruct.transpose_cast D.toDoubleCategoryStruct _ _ _ _ _)

/-- Changing the right boundary along the globular isomorphism induced by an equality of edges
transports the cell along that equality. -/
@[simp]
theorem changeRight_eqToIso (h : (⟨r⟩ : D.VerticalGlobular b d) = ⟨r'⟩) (α : D.Cell p q l r) :
    D.changeRight (eqToIso h) α = α.cast rfl rfl rfl (congrArg HorizontalGlobular.edge h) :=
  (D.transpose.changeBottom_eqToIso h α).trans
    (DoubleCategoryStruct.transpose_cast D.toDoubleCategoryStruct _ _ _ _ _)

/-- Changing the top boundary of a vertical pasting changes the top boundary of its upper
cell. -/
theorem changeTop_vComp {x y : O} {s : Edge H x y} {n : Edge V c x} {t : Edge V d y}
    (e : D.HorizontalIso p p') (α : D.Cell p q l r) (β : D.Cell q s n t) :
    D.changeTop e (D.vComp α β) = D.vComp (D.changeTop e α) β := by
  simp only [changeTop_def, vComp_cast_top, vComp_assoc, Cell.cast_cast]

/-- Changing the bottom boundary of a vertical pasting changes the bottom boundary of its lower
cell. -/
theorem changeBottom_vComp {x y : O} {s s' : Edge H x y} {n : Edge V c x} {t : Edge V d y}
    (e : D.HorizontalIso s s') (α : D.Cell p q l r) (β : D.Cell q s n t) :
    D.changeBottom e (D.vComp α β) = D.vComp α (D.changeBottom e β) := by
  simp only [changeBottom_def, vComp_cast_bottom, vComp_assoc, Cell.cast_cast]

/-- Changing the left boundary of a horizontal pasting changes the left boundary of its left
cell. -/
theorem changeLeft_hComp {x y : O} {s : Edge H b x} {t : Edge H d y} {n : Edge V x y}
    (e : D.VerticalIso l l') (α : D.Cell p q l r) (β : D.Cell s t r n) :
    D.changeLeft e (D.hComp α β) = D.hComp (D.changeLeft e α) β :=
  D.transpose.changeTop_vComp e α β

/-- Changing the right boundary of a horizontal pasting changes the right boundary of its right
cell. -/
theorem changeRight_hComp {x y : O} {s : Edge H b x} {t : Edge H d y} {n n' : Edge V x y}
    (e : D.VerticalIso n n') (α : D.Cell p q l r) (β : D.Cell s t r n) :
    D.changeRight e (D.hComp α β) = D.hComp α (D.changeRight e β) :=
  D.transpose.changeBottom_vComp e α β

/-- Pasting an invertible globular cell `e` on top of a cell whose top boundary was changed along
`e` recovers the original cell, up to the unit law on the vertical boundaries. This is
`changeTop_symm_changeTop` written as a pasting. -/
theorem vComp_hom_cell_changeTop {x y : O} {s : Edge H x y} {n : Edge V c x} {t : Edge V d y}
    (e : D.HorizontalIso q q') (β : D.Cell q s n t) :
    D.vComp e.hom.cell (D.changeTop e β) =
      β.cast rfl rfl (Category.id_comp (self := V) n).symm
        (Category.id_comp (self := V) t).symm := by
  have h := D.changeTop_def e.symm (D.changeTop e β)
  rw [changeTop_symm_changeTop, Iso.symm_inv, eq_comm, Cell.cast_eq_iff] at h
  exact h

/-- Pasting an invertible vertical globular cell `e` to the left of a cell whose left boundary
was changed along `e` recovers the original cell, up to the unit law on the horizontal
boundaries. -/
theorem hComp_hom_cell_changeLeft {x y : O} {s : Edge H b x} {t : Edge H d y} {n : Edge V x y}
    (e : D.VerticalIso r r') (β : D.Cell s t r n) :
    D.hComp e.hom.cell (D.changeLeft e β) =
      β.cast (Category.id_comp (self := H) s).symm (Category.id_comp (self := H) t).symm rfl
        rfl :=
  (D.transpose.vComp_hom_cell_changeTop e β).trans
    (DoubleCategoryStruct.transpose_cast D.toDoubleCategoryStruct _ _ _ _ _)

/-- Changing the edge shared by two vertically pasted cells along the same invertible globular
cell, at the bottom of the upper cell and at the top of the lower cell, does not change their
vertical pasting. -/
@[simp]
theorem vComp_changeBottom_changeTop {x y : O} {s : Edge H x y} {n : Edge V c x}
    {t : Edge V d y} (e : D.HorizontalIso q q') (α : D.Cell p q l r) (β : D.Cell q s n t) :
    D.vComp (D.changeBottom e α) (D.changeTop e β) = D.vComp α β := by
  rw [changeBottom_def, vComp_cast_top, vComp_assoc, vComp_hom_cell_changeTop,
    vComp_cast_bottom]
  simp only [Cell.cast_cast, Cell.cast_rfl]

/-- Changing the edge shared by two horizontally pasted cells along the same invertible globular
cell, on the right of the left cell and on the left of the right cell, does not change their
horizontal pasting. -/
@[simp]
theorem hComp_changeRight_changeLeft {x y : O} {s : Edge H b x} {t : Edge H d y}
    {n : Edge V x y} (e : D.VerticalIso r r') (α : D.Cell p q l r) (β : D.Cell s t r n) :
    D.hComp (D.changeRight e α) (D.changeLeft e β) = D.hComp α β :=
  D.transpose.vComp_changeBottom_changeTop e α β

/-- Changing the top and the bottom boundary of a cell commute. -/
theorem changeBottom_changeTop (e : D.HorizontalIso p p') (e' : D.HorizontalIso q q')
    (α : D.Cell p q l r) :
    D.changeBottom e' (D.changeTop e α) = D.changeTop e (D.changeBottom e' α) := by
  simp only [changeTop_def, changeBottom_def, vComp_cast_top, vComp_cast_bottom, vComp_assoc,
    Cell.cast_cast]

/-- Changing the left and the right boundary of a cell commute. -/
theorem changeRight_changeLeft (e : D.VerticalIso l l') (e' : D.VerticalIso r r')
    (α : D.Cell p q l r) :
    D.changeRight e' (D.changeLeft e α) = D.changeLeft e (D.changeRight e' α) :=
  D.transpose.changeBottom_changeTop e e' α

/-- Changing the top and the left boundary of a cell commute. -/
theorem changeLeft_changeTop (e : D.HorizontalIso p p') (e' : D.VerticalIso l l')
    (α : D.Cell p q l r) :
    D.changeLeft e' (D.changeTop e α) = D.changeTop e (D.changeLeft e' α) := by
  rw [changeLeft_def, changeTop_def, changeLeft_def, changeTop_def,
    ← VerticalGlobular.homEquiv_apply e'.inv]
  generalize e.inv.cell = σ
  generalize VerticalGlobular.homEquiv _ _ e'.inv = τ
  have hσ : (D.hComp (D.vId (edgeId H a)) σ).cast (Category.id_comp (self := H) p')
      (Category.id_comp (self := H) p) rfl rfl = σ := by
    simp
  have hτ : (D.vComp (D.vId (edgeId H a)) τ).cast rfl rfl (Category.id_comp (self := V) l')
      (Category.id_comp (self := V) l) = τ := by
    simp
  conv_lhs => rw [← hτ]
  conv_rhs => rw [← hσ]
  rw [hComp_cast_cast, vComp_cast_cast, ← D.interchange, Cell.cast_cast, Cell.cast_cast]

/-- Changing the top and the right boundary of a cell commute. -/
theorem changeRight_changeTop (e : D.HorizontalIso p p') (e' : D.VerticalIso r r')
    (α : D.Cell p q l r) :
    D.changeRight e' (D.changeTop e α) = D.changeTop e (D.changeRight e' α) := by
  rw [changeRight_def, changeTop_def, changeRight_def, changeTop_def,
    ← VerticalGlobular.homEquiv_apply e'.hom]
  generalize e.inv.cell = σ
  generalize VerticalGlobular.homEquiv _ _ e'.hom = τ
  have hσ : (D.hComp σ (D.vId (edgeId H b))).cast (Category.comp_id (self := H) p')
      (Category.comp_id (self := H) p) rfl rfl = σ := by
    simp
  have hτ : (D.vComp (D.vId (edgeId H b)) τ).cast rfl rfl (Category.id_comp (self := V) r)
      (Category.id_comp (self := V) r') = τ := by
    simp
  conv_lhs => rw [← hτ]
  conv_rhs => rw [← hσ]
  rw [hComp_cast_cast, vComp_cast_cast, ← D.interchange, Cell.cast_cast, Cell.cast_cast]

/-- Changing the bottom and the right boundary of a cell commute. -/
theorem changeRight_changeBottom (e : D.HorizontalIso q q') (e' : D.VerticalIso r r')
    (α : D.Cell p q l r) :
    D.changeRight e' (D.changeBottom e α) = D.changeBottom e (D.changeRight e' α) := by
  rw [changeRight_def, changeBottom_def, changeRight_def, changeBottom_def,
    ← VerticalGlobular.homEquiv_apply e'.hom]
  generalize e.hom.cell = σ
  generalize VerticalGlobular.homEquiv _ _ e'.hom = τ
  have hσ : (D.hComp σ (D.vId (edgeId H d))).cast (Category.comp_id (self := H) q)
      (Category.comp_id (self := H) q') rfl rfl = σ := by
    simp
  have hτ : (D.vComp τ (D.vId (edgeId H d))).cast rfl rfl (Category.comp_id (self := V) r)
      (Category.comp_id (self := V) r') = τ := by
    simp
  conv_lhs => rw [← hτ]
  conv_rhs => rw [← hσ]
  rw [hComp_cast_cast, vComp_cast_cast, ← D.interchange, Cell.cast_cast, Cell.cast_cast]

/-- Changing the bottom and the left boundary of a cell commute. -/
theorem changeLeft_changeBottom (e : D.HorizontalIso q q') (e' : D.VerticalIso l l')
    (α : D.Cell p q l r) :
    D.changeLeft e' (D.changeBottom e α) = D.changeBottom e (D.changeLeft e' α) :=
  (D.transpose.changeRight_changeTop e' e α).symm

end BoundaryChange

end StrictDoubleCategory

end TauCeti
