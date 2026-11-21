/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Category.Basic

/-!
# Strict double categories

A strict double category on an object type `O` has two categories of edges on `O`, the
horizontal edges and the vertical edges, and a type of cells for every boundary
`(top, bottom, left, right)`:

```text
       p
  a ──────→ b
  │         │
  l         r
  │         │
  ↓         ↓
  c ──────→ d
       q
```

Cells paste horizontally (along a common vertical edge) and vertically (along a common
horizontal edge). Both pastings are strictly associative and unital, they satisfy the middle-four
interchange law, the identity cells are compatible with composition of edges, and the two
identity cells on an object agree.

The two edge categories are explicit arguments rather than instances, since they are two
category structures on the same type `O`. `TauCeti.StrictDoubleCategory.Edge`,
`TauCeti.StrictDoubleCategory.edgeId` and `TauCeti.StrictDoubleCategory.edgeComp` name the
morphisms, identities and composition of such an explicitly supplied category. Composition is
written in diagrammatic order throughout.

The cell types are indexed by their boundaries, so the unit and associativity laws relate cells
whose boundaries are only propositionally equal: for instance `𝟙 ≫ p` and `p`. These laws are
stated with `TauCeti.DoubleCategoryStruct.Cell.cast`, which changes the four boundary edges of a
cell along equalities, in the manner of `Quiver.Hom.cast`. The file supplies the identity,
composition and cancellation laws of this transport, its comparison with heterogeneous equality,
and its interaction with both pastings and both identity cells, so that the laws can be used by
rewriting without manipulating heterogeneous equalities.

## Main declarations

* `TauCeti.DoubleCategoryStruct`: boundary-indexed cells with identities and both pastings.
* `TauCeti.DoubleCategoryStruct.Cell.cast`: transport of a cell along equalities of its
  boundary edges.
* `TauCeti.StrictDoubleCategory`: the laws of a strict double category, including
  `TauCeti.StrictDoubleCategory.interchange` and `TauCeti.StrictDoubleCategory.hId_id`.

## References

* C. Ehresmann, *Catégories structurées*, Annales scientifiques de l'École Normale Supérieure
  **80** (1963), 349–426.
* A. D. Fairbanks and M. Shulman, *Doubly weak double categories*, Applied Categorical
  Structures **34** (2026), article 26; arXiv:2506.23651.

## Related formalizations

* The Geb project formalizes strict double categories in Lean as internal categories in `Cat`:
  https://github.com/anoma/geb/blob/main/geb-lean/GebLean/Utilities/DoubleCategory.lean.
  The boundary-indexed presentation in this file was developed independently of it, from the
  mathematical sources above.
-/

@[expose] public section

universe s u h v

namespace TauCeti

open CategoryTheory

namespace StrictDoubleCategory

/-- The morphisms `a ⟶ b` of an explicitly supplied category structure `C` on `O`. The edges of
a double category in one direction are the morphisms of such a category. -/
abbrev Edge {O : Type u} (C : Category.{h} O) (a b : O) : Type h :=
  @Quiver.Hom O C.toCategoryStruct.toQuiver a b

/-- The identity morphism of `a` in an explicitly supplied category structure `C`. -/
abbrev edgeId {O : Type u} (C : Category.{h} O) (a : O) : Edge C a a :=
  @CategoryStruct.id O C.toCategoryStruct a

/-- Composition in an explicitly supplied category structure `C`, in diagrammatic order. -/
abbrev edgeComp {O : Type u} (C : Category.{h} O) {a b c : O} (f : Edge C a b)
    (g : Edge C b c) : Edge C a c :=
  @CategoryStruct.comp O C.toCategoryStruct a b c f g

end StrictDoubleCategory

open StrictDoubleCategory

/-- The data of a double category on objects `O` with horizontal edge category `H` and vertical
edge category `V`: a type of cells for every boundary `(top, bottom, left, right)`, the identity
cells for both pastings, and the two pastings. -/
structure DoubleCategoryStruct (O : Type u) (H : Category.{h} O) (V : Category.{v} O) where
  /-- The cells with top `p`, bottom `q`, left `l` and right `r`. -/
  Cell : {a b c d : O} → Edge H a b → Edge H c d → Edge V a c → Edge V b d → Type s
  /-- The identity cell for horizontal pasting on a vertical edge `f`. -/
  hId : {a b : O} → (f : Edge V a b) → Cell (edgeId H a) (edgeId H b) f f
  /-- The identity cell for vertical pasting on a horizontal edge `f`. -/
  vId : {a b : O} → (f : Edge H a b) → Cell f f (edgeId V a) (edgeId V b)
  /-- Horizontal pasting of two cells along a common vertical edge, left to right. -/
  hComp : {a b c d e f : O} → {p : Edge H a b} → {q : Edge H b c} → {r : Edge H d e} →
    {t : Edge H e f} → {l : Edge V a d} → {m : Edge V b e} → {n : Edge V c f} →
    Cell p r l m → Cell q t m n → Cell (edgeComp H p q) (edgeComp H r t) l n
  /-- Vertical pasting of two cells along a common horizontal edge, top to bottom. -/
  vComp : {a b c d e f : O} → {p : Edge H a b} → {q : Edge H c d} → {r : Edge H e f} →
    {l : Edge V a c} → {m : Edge V b d} → {n : Edge V c e} → {t : Edge V d f} →
    Cell p q l m → Cell q r n t → Cell p r (edgeComp V l n) (edgeComp V m t)

namespace DoubleCategoryStruct

variable {O : Type u} {H : Category.{h} O} {V : Category.{v} O}
  {D : DoubleCategoryStruct.{s} O H V}

section Cast

variable {a b c d : O} {p p' p'' : Edge H a b} {q q' q'' : Edge H c d}
  {l l' l'' : Edge V a c} {r r' r'' : Edge V b d}

/-- Change the four boundary edges of a cell along equalities. -/
def _root_.TauCeti.DoubleCategoryStruct.Cell.cast
    (hp : p = p') (hq : q = q') (hl : l = l') (hr : r = r') (α : D.Cell p q l r) :
    D.Cell p' q' l' r' := by
  subst hp hq hl hr
  exact α

@[simp]
theorem _root_.TauCeti.DoubleCategoryStruct.Cell.cast_rfl (α : D.Cell p q l r) :
    α.cast rfl rfl rfl rfl = α :=
  rfl

@[simp]
theorem _root_.TauCeti.DoubleCategoryStruct.Cell.cast_cast
    (hp : p = p') (hq : q = q') (hl : l = l') (hr : r = r')
    (hp' : p' = p'') (hq' : q' = q'') (hl' : l' = l'') (hr' : r' = r'') (α : D.Cell p q l r) :
    (α.cast hp hq hl hr).cast hp' hq' hl' hr' =
      α.cast (hp.trans hp') (hq.trans hq') (hl.trans hl') (hr.trans hr') := by
  subst hp hq hl hr hp' hq' hl' hr'
  rfl

theorem _root_.TauCeti.DoubleCategoryStruct.Cell.cast_heq
    (hp : p = p') (hq : q = q') (hl : l = l') (hr : r = r')
    (α : D.Cell p q l r) : α.cast hp hq hl hr ≍ α := by
  subst hp hq hl hr
  rfl

theorem _root_.TauCeti.DoubleCategoryStruct.Cell.cast_eq_iff_heq
    (hp : p = p') (hq : q = q') (hl : l = l') (hr : r = r')
    (α : D.Cell p q l r) (β : D.Cell p' q' l' r') : α.cast hp hq hl hr = β ↔ α ≍ β := by
  subst hp hq hl hr
  exact heq_iff_eq.symm

theorem _root_.TauCeti.DoubleCategoryStruct.Cell.eq_cast_iff_heq
    (hp : p = p') (hq : q = q') (hl : l = l') (hr : r = r')
    (α : D.Cell p q l r) (β : D.Cell p' q' l' r') : β = α.cast hp hq hl hr ↔ β ≍ α := by
  subst hp hq hl hr
  exact heq_iff_eq.symm

/-- Transport of cells along equalities of boundaries is injective. -/
@[simp]
theorem Cell.cast_inj (hp : p = p') (hq : q = q') (hl : l = l') (hr : r = r')
    {α β : D.Cell p q l r} : α.cast hp hq hl hr = β.cast hp hq hl hr ↔ α = β := by
  subst hp hq hl hr
  rfl

theorem Cell.cast_injective (hp : p = p') (hq : q = q') (hl : l = l') (hr : r = r') :
    Function.Injective (Cell.cast (D := D) hp hq hl hr) :=
  fun _ _ ↦ (Cell.cast_inj hp hq hl hr).1

end Cast

section Pasting

variable {a b c d e f : O}

/-- Transport commutes with horizontal pasting: transporting both cells, with the same equality
on their common vertical edge, transports the pasted cell. -/
@[simp]
theorem hComp_cast_cast {p p' : Edge H a b} {q q' : Edge H b c} {r r' : Edge H d e}
    {t t' : Edge H e f} {l l' : Edge V a d} {m m' : Edge V b e} {n n' : Edge V c f}
    (hp : p = p') (hq : q = q') (hr : r = r') (ht : t = t') (hl : l = l') (hm : m = m')
    (hn : n = n') (α : D.Cell p r l m) (β : D.Cell q t m n) :
    D.hComp (α.cast hp hr hl hm) (β.cast hq ht hm hn) =
      (D.hComp α β).cast (by rw [hp, hq]) (by rw [hr, ht]) hl hn := by
  subst hp hq hr ht hl hm hn
  rfl

/-- Transporting the left factor of a horizontal pasting, away from the common edge. -/
@[simp]
theorem hComp_cast_left {p p' : Edge H a b} {q : Edge H b c} {r r' : Edge H d e}
    {t : Edge H e f} {l l' : Edge V a d} {m : Edge V b e} {n : Edge V c f}
    (hp : p = p') (hr : r = r') (hl : l = l') (α : D.Cell p r l m) (β : D.Cell q t m n) :
    D.hComp (α.cast hp hr hl rfl) β =
      (D.hComp α β).cast (by rw [hp]) (by rw [hr]) hl rfl := by
  subst hp hr hl
  rfl

/-- Transporting the right factor of a horizontal pasting, away from the common edge. -/
@[simp]
theorem hComp_cast_right {p : Edge H a b} {q q' : Edge H b c} {r : Edge H d e}
    {t t' : Edge H e f} {l : Edge V a d} {m : Edge V b e} {n n' : Edge V c f}
    (hq : q = q') (ht : t = t') (hn : n = n') (α : D.Cell p r l m) (β : D.Cell q t m n) :
    D.hComp α (β.cast hq ht rfl hn) =
      (D.hComp α β).cast (by rw [hq]) (by rw [ht]) rfl hn := by
  subst hq ht hn
  rfl

/-- Transport commutes with vertical pasting: transporting both cells, with the same equality
on their common horizontal edge, transports the pasted cell. -/
@[simp]
theorem vComp_cast_cast {p p' : Edge H a b} {q q' : Edge H c d} {r r' : Edge H e f}
    {l l' : Edge V a c} {m m' : Edge V b d} {n n' : Edge V c e} {t t' : Edge V d f}
    (hp : p = p') (hq : q = q') (hr : r = r') (hl : l = l') (hm : m = m') (hn : n = n')
    (ht : t = t') (α : D.Cell p q l m) (β : D.Cell q r n t) :
    D.vComp (α.cast hp hq hl hm) (β.cast hq hr hn ht) =
      (D.vComp α β).cast hp hr (by rw [hl, hn]) (by rw [hm, ht]) := by
  subst hp hq hr hl hm hn ht
  rfl

/-- Transporting the upper factor of a vertical pasting, away from the common edge. -/
@[simp]
theorem vComp_cast_top {p p' : Edge H a b} {q : Edge H c d} {r : Edge H e f}
    {l l' : Edge V a c} {m m' : Edge V b d} {n : Edge V c e} {t : Edge V d f}
    (hp : p = p') (hl : l = l') (hm : m = m') (α : D.Cell p q l m) (β : D.Cell q r n t) :
    D.vComp (α.cast hp rfl hl hm) β =
      (D.vComp α β).cast hp rfl (by rw [hl]) (by rw [hm]) := by
  subst hp hl hm
  rfl

/-- Transporting the lower factor of a vertical pasting, away from the common edge. -/
@[simp]
theorem vComp_cast_bottom {p : Edge H a b} {q : Edge H c d} {r r' : Edge H e f}
    {l : Edge V a c} {m : Edge V b d} {n n' : Edge V c e} {t t' : Edge V d f}
    (hr : r = r') (hn : n = n') (ht : t = t') (α : D.Cell p q l m) (β : D.Cell q r n t) :
    D.vComp α (β.cast rfl hr hn ht) =
      (D.vComp α β).cast rfl hr (by rw [hn]) (by rw [ht]) := by
  subst hr hn ht
  rfl

/-- The horizontal identity cell on a vertical edge depends on that edge only through
equality. -/
@[simp]
theorem cast_hId {f f' : Edge V a b} (hf : f = f') :
    (D.hId f).cast rfl rfl hf hf = D.hId f' := by
  subst hf
  rfl

/-- The vertical identity cell on a horizontal edge depends on that edge only through
equality. -/
@[simp]
theorem cast_vId {f f' : Edge H a b} (hf : f = f') :
    (D.vId f).cast hf hf rfl rfl = D.vId f' := by
  subst hf
  rfl

end Pasting

end DoubleCategoryStruct

open DoubleCategoryStruct

/-- A strict double category on objects `O` with horizontal edge category `H` and vertical edge
category `V`. Horizontal and vertical pasting of cells are associative and unital, after
transporting along the corresponding laws of `H` and `V` on the boundaries; they satisfy the
middle-four interchange law; the horizontal identity cells respect composition of vertical
edges and the vertical identity cells respect composition of horizontal edges; and the two
identity cells on an object agree. -/
structure StrictDoubleCategory (O : Type u) (H : Category.{h} O) (V : Category.{v} O) extends
    DoubleCategoryStruct.{s} O H V where
  /-- Left unit law for horizontal pasting. -/
  hId_hComp {a b c d : O} {p : Edge H a b} {q : Edge H c d} {l : Edge V a c} {r : Edge V b d}
    (α : Cell p q l r) :
    hComp (hId l) α = DoubleCategoryStruct.Cell.cast (D := toDoubleCategoryStruct)
      (Category.id_comp (self := H) p).symm (Category.id_comp (self := H) q).symm rfl rfl α
  /-- Right unit law for horizontal pasting. -/
  hComp_hId {a b c d : O} {p : Edge H a b} {q : Edge H c d} {l : Edge V a c} {r : Edge V b d}
    (α : Cell p q l r) :
    hComp α (hId r) = DoubleCategoryStruct.Cell.cast (D := toDoubleCategoryStruct)
      (Category.comp_id (self := H) p).symm (Category.comp_id (self := H) q).symm rfl rfl α
  /-- Left unit law for vertical pasting. -/
  vId_vComp {a b c d : O} {p : Edge H a b} {q : Edge H c d} {l : Edge V a c} {r : Edge V b d}
    (α : Cell p q l r) :
    vComp (vId p) α = DoubleCategoryStruct.Cell.cast (D := toDoubleCategoryStruct) rfl rfl
      (Category.id_comp (self := V) l).symm (Category.id_comp (self := V) r).symm α
  /-- Right unit law for vertical pasting. -/
  vComp_vId {a b c d : O} {p : Edge H a b} {q : Edge H c d} {l : Edge V a c} {r : Edge V b d}
    (α : Cell p q l r) :
    vComp α (vId q) = DoubleCategoryStruct.Cell.cast (D := toDoubleCategoryStruct) rfl rfl
      (Category.comp_id (self := V) l).symm (Category.comp_id (self := V) r).symm α
  /-- Associativity of horizontal pasting. -/
  hComp_assoc {a b c d e f g k : O} {p : Edge H a b} {q : Edge H b c} {r : Edge H c d}
    {p' : Edge H e f} {q' : Edge H f g} {r' : Edge H g k} {l : Edge V a e} {m : Edge V b f}
    {n : Edge V c g} {t : Edge V d k} (α : Cell p p' l m) (β : Cell q q' m n)
    (γ : Cell r r' n t) :
    hComp (hComp α β) γ = DoubleCategoryStruct.Cell.cast (D := toDoubleCategoryStruct)
      (Category.assoc (self := H) p q r).symm (Category.assoc (self := H) p' q' r').symm rfl rfl
      (hComp α (hComp β γ))
  /-- Associativity of vertical pasting. -/
  vComp_assoc {a b c d e f g k : O} {p : Edge H a b} {q : Edge H c d} {r : Edge H e f}
    {t : Edge H g k} {l : Edge V a c} {m : Edge V c e} {n : Edge V e g} {l' : Edge V b d}
    {m' : Edge V d f} {n' : Edge V f k} (α : Cell p q l l') (β : Cell q r m m')
    (γ : Cell r t n n') :
    vComp (vComp α β) γ = DoubleCategoryStruct.Cell.cast (D := toDoubleCategoryStruct) rfl rfl
      (Category.assoc (self := V) l m n).symm (Category.assoc (self := V) l' m' n').symm
      (vComp α (vComp β γ))
  /-- The middle-four interchange law: a two-by-two grid of cells has the same pasting whether
  its rows or its columns are pasted first. -/
  interchange {a b c d e f g k i : O} {p : Edge H a b} {q : Edge H b c} {r : Edge H d e}
    {t : Edge H e f} {x : Edge H g k} {y : Edge H k i} {l : Edge V a d} {m : Edge V b e}
    {n : Edge V c f} {l' : Edge V d g} {m' : Edge V e k} {n' : Edge V f i}
    (α : Cell p r l m) (β : Cell q t m n) (γ : Cell r x l' m') (δ : Cell t y m' n') :
    vComp (hComp α β) (hComp γ δ) = hComp (vComp α γ) (vComp β δ)
  /-- The horizontal identity cell on a composite of vertical edges is the vertical pasting of
  the horizontal identity cells. -/
  hId_comp {a b c : O} (f : Edge V a b) (g : Edge V b c) :
    hId (edgeComp V f g) = vComp (hId f) (hId g)
  /-- The vertical identity cell on a composite of horizontal edges is the horizontal pasting of
  the vertical identity cells. -/
  vId_comp {a b c : O} (f : Edge H a b) (g : Edge H b c) :
    vId (edgeComp H f g) = hComp (vId f) (vId g)
  /-- The horizontal identity cell on the identity vertical edge of an object is the vertical
  identity cell on its identity horizontal edge. -/
  hId_id (a : O) : hId (edgeId V a) = vId (edgeId H a)

namespace StrictDoubleCategory

attribute [simp] hId_hComp hComp_hId vId_vComp vComp_vId

end StrictDoubleCategory

namespace DoubleCategoryStruct

variable {O : Type u} {H : Category.{h} O} {V : Category.{v} O}

/-- The transpose of the data of a double category: its horizontal and vertical edges are the
vertical and horizontal edges of `D`, a cell with boundary `(p, q, l, r)` is a cell of `D` with
boundary `(l, r, p, q)`, and horizontal and vertical identity cells and pastings are exchanged. -/
@[simps hId vId hComp vComp]
def transpose (D : DoubleCategoryStruct.{s} O H V) : DoubleCategoryStruct.{s} O V H where
  Cell p q l r := D.Cell l r p q
  hId := D.vId
  vId := D.hId
  hComp := D.vComp
  vComp := D.hComp

variable {D : DoubleCategoryStruct.{s} O H V}

/-- A cell of the transpose with boundary `(p, q, l, r)` is a cell with boundary `(l, r, p, q)`. -/
theorem transpose_Cell {a b c d : O} (p : Edge V a b) (q : Edge V c d) (l : Edge H a c)
    (r : Edge H b d) : D.transpose.Cell p q l r = D.Cell l r p q :=
  rfl

/-- Transport of a cell of the transpose is transport in the original double category, with the
horizontal and vertical boundary equalities exchanged. -/
@[simp]
theorem transpose_cast {a b c d : O} {p p' : Edge V a b} {q q' : Edge V c d} {l l' : Edge H a c}
    {r r' : Edge H b d} (hp : p = p') (hq : q = q') (hl : l = l') (hr : r = r')
    (α : D.transpose.Cell p q l r) :
    Cell.cast (D := D.transpose) hp hq hl hr α = Cell.cast (D := D) hl hr hp hq α := by
  subst hp hq hl hr
  rfl

@[simp]
theorem transpose_transpose : D.transpose.transpose = D :=
  rfl

end DoubleCategoryStruct

namespace StrictDoubleCategory

variable {O : Type u} {H : Category.{h} O} {V : Category.{v} O}

/-- The transpose of a strict double category, exchanging the roles of horizontal and vertical
edges, of horizontal and vertical identity cells, and of horizontal and vertical pasting. A
statement about the horizontal direction of a strict double category gives the corresponding
statement about the vertical direction when applied to its transpose. -/
@[simps! toDoubleCategoryStruct]
def transpose (D : StrictDoubleCategory.{s} O H V) : StrictDoubleCategory.{s} O V H where
  toDoubleCategoryStruct := D.toDoubleCategoryStruct.transpose
  hId_hComp α := (D.vId_vComp α).trans (transpose_cast _ _ _ _ α).symm
  hComp_hId α := (D.vComp_vId α).trans (transpose_cast _ _ _ _ α).symm
  vId_vComp α := (D.hId_hComp α).trans (transpose_cast _ _ _ _ α).symm
  vComp_vId α := (D.hComp_hId α).trans (transpose_cast _ _ _ _ α).symm
  hComp_assoc α β γ := (D.vComp_assoc α β γ).trans (transpose_cast _ _ _ _ _).symm
  vComp_assoc α β γ := (D.hComp_assoc α β γ).trans (transpose_cast _ _ _ _ _).symm
  interchange α β γ δ := (D.interchange α γ β δ).symm
  hId_comp := D.vId_comp
  vId_comp := D.hId_comp
  hId_id a := (D.hId_id a).symm

@[simp]
theorem transpose_transpose (D : StrictDoubleCategory.{s} O H V) : D.transpose.transpose = D :=
  rfl

end StrictDoubleCategory

end TauCeti
