/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.DoubleCategory.Basic

/-!
# The transpose of a strict double category

Reflecting every cell in the diagonal through its top left corner exchanges the two edge
directions of a double category: a cell with boundary `(p, q, l, r)` becomes a cell with boundary
`(l, r, p, q)`, horizontal pasting becomes vertical pasting, and the two identity-cell
assignments are exchanged.

```text
       p                        l
  a ──────→ b              a ──────→ c
  │         │              │         │
  l    α    r     ↦        p    α    q
  │         │              │         │
  ↓         ↓              ↓         ↓
  c ──────→ d              b ──────→ d
       q                        r
```

Transposition lets every construction made in the horizontal direction be read in the vertical
direction as well; for instance, the vertical globular cells of a double category are the
horizontal globular cells of its transpose.

## Main declarations

* `TauCeti.DoubleCategoryStruct.transpose`: the transposed cells, identities and pastings.
* `TauCeti.StrictDoubleCategory.transpose`: the transpose of a strict double category.
* `TauCeti.StrictDoubleCategory.transpose_transpose`: transposition is an involution.
-/

@[expose] public section

universe s u h v

namespace TauCeti

open CategoryTheory StrictDoubleCategory

variable {O : Type u} {H : Category.{h} O} {V : Category.{v} O}

namespace DoubleCategoryStruct

/-- The transpose of the data of a double category: its horizontal and vertical edges are the
vertical and horizontal edges of `D`, a cell with boundary `(p, q, l, r)` is a cell of `D` with
boundary `(l, r, p, q)`, and the two identity cells and the two pastings are exchanged. -/
def transpose (D : DoubleCategoryStruct.{s} O H V) : DoubleCategoryStruct.{s} O V H where
  Cell p q l r := D.Cell l r p q
  hId f := D.vId f
  vId f := D.hId f
  hComp α β := D.vComp α β
  vComp α β := D.hComp α β

variable (D : DoubleCategoryStruct.{s} O H V)

@[simp]
theorem transpose_Cell {a b c d : O} (p : Edge V a b) (q : Edge V c d) (l : Edge H a c)
    (r : Edge H b d) : D.transpose.Cell p q l r = D.Cell l r p q :=
  rfl

@[simp]
theorem transpose_hId {a b : O} (f : Edge H a b) : D.transpose.hId f = D.vId f :=
  rfl

@[simp]
theorem transpose_vId {a b : O} (f : Edge V a b) : D.transpose.vId f = D.hId f :=
  rfl

@[simp]
theorem transpose_hComp {a b c d e f : O} {p : Edge V a b} {q : Edge V b c} {r : Edge V d e}
    {t : Edge V e f} {l : Edge H a d} {m : Edge H b e} {n : Edge H c f}
    (α : D.transpose.Cell p r l m) (β : D.transpose.Cell q t m n) :
    D.transpose.hComp α β = D.vComp (q := m) α β :=
  rfl

@[simp]
theorem transpose_vComp {a b c d e f : O} {p : Edge V a b} {q : Edge V c d} {r : Edge V e f}
    {l : Edge H a c} {m : Edge H b d} {n : Edge H c e} {t : Edge H d f}
    (α : D.transpose.Cell p q l m) (β : D.transpose.Cell q r n t) :
    D.transpose.vComp α β = D.hComp (m := q) α β :=
  rfl

/-- Transporting a cell of the transpose transports the same cell of `D`, with the boundary
equalities permuted accordingly. -/
@[simp]
theorem transpose_cast {a b c d : O} {p p' : Edge V a b} {q q' : Edge V c d}
    {l l' : Edge H a c} {r r' : Edge H b d} (hp : p = p') (hq : q = q') (hl : l = l')
    (hr : r = r') (α : D.transpose.Cell p q l r) :
    Cell.cast (D := D.transpose) hp hq hl hr α = Cell.cast (D := D) hl hr hp hq α := by
  subst hp hq hl hr
  rfl

@[simp]
theorem transpose_transpose : D.transpose.transpose = D :=
  rfl

end DoubleCategoryStruct

namespace StrictDoubleCategory

open DoubleCategoryStruct

/-- The transpose of a strict double category `D`: the double category with horizontal edges the
vertical edges of `D`, vertical edges the horizontal edges of `D`, and a cell with boundary
`(p, q, l, r)` for each cell of `D` with boundary `(l, r, p, q)`. Horizontal pasting in the
transpose is vertical pasting in `D` and conversely. -/
def transpose (D : StrictDoubleCategory.{s} O H V) : StrictDoubleCategory.{s} O V H where
  toDoubleCategoryStruct := D.toDoubleCategoryStruct.transpose
  hId_hComp α := by rw [transpose_cast]; exact D.vId_vComp α
  hComp_hId α := by rw [transpose_cast]; exact D.vComp_vId α
  vId_vComp α := by rw [transpose_cast]; exact D.hId_hComp α
  vComp_vId α := by rw [transpose_cast]; exact D.hComp_hId α
  hComp_assoc α β γ := by rw [transpose_cast]; exact D.vComp_assoc α β γ
  vComp_assoc α β γ := by rw [transpose_cast]; exact D.hComp_assoc α β γ
  interchange α β γ δ := (D.interchange α γ β δ).symm
  hId_comp f g := D.vId_comp f g
  vId_comp f g := D.hId_comp f g
  hId_id a := (D.hId_id a).symm

variable (D : StrictDoubleCategory.{s} O H V)

@[simp]
theorem transpose_toDoubleCategoryStruct :
    D.transpose.toDoubleCategoryStruct = D.toDoubleCategoryStruct.transpose :=
  rfl

@[simp]
theorem transpose_transpose : D.transpose.transpose = D :=
  rfl

end StrictDoubleCategory

end TauCeti
