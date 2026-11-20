/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Category.Basic

/-!
# Boundary-indexed strict double categories

A strict double category has two explicitly supplied edge categories on the same objects.
Its cells are indexed by their top, bottom, left, and right edges. Horizontal arrows point
right and vertical arrows point down; both compositions are in diagrammatic order.
The edge categories and the cells have independent universe levels.

`StrictDoubleCategory` includes both cell compositions, their unit and associativity laws,
interchange, and the compatibility of the two identity assignments. Its heterogeneous
axioms express equality after boundary transport, rather than additional coherence cells.
`StrictDoubleCategory.cast` and the pasting lemmas express these laws as ordinary equalities.

For a related presentation, see the Geb project's
`GebLean/Utilities/DoubleCategory.lean` (https://github.com/anoma/geb).
The boundary-indexed development here is independent of that implementation.
-/

public section

universe u h v s

namespace TauCeti

open CategoryTheory

/-- Morphisms in one explicitly supplied edge category. -/
abbrev Edge {O : Type u} (C : Category.{h} O) (a b : O) :=
  @Quiver.Hom O C.toCategoryStruct.toQuiver a b

/-- Identity in one edge direction. -/
abbrev edgeId {O : Type u} (C : Category.{h} O) (a : O) : Edge C a a :=
  @CategoryStruct.id O C.toCategoryStruct a

/-- Composition in one edge direction, in diagrammatic order. -/
abbrev edgeComp {O : Type u} (C : Category.{h} O) {a b c : O}
    (f : Edge C a b) (g : Edge C b c) : Edge C a c :=
  @CategoryStruct.comp O C.toCategoryStruct a b c f g

/-- A boundary-indexed strict double category with common object type `O`.
The arguments of `Cell` are top, bottom, left, right, in that order. -/
structure StrictDoubleCategory (O : Type u) (H : Category.{h} O)
    (V : Category.{v} O) where
  /-- Cells with the specified top, bottom, left, and right boundary arrows. -/
  Cell : {a b c d : O} → Edge H a b → Edge H c d → Edge V a c → Edge V b d → Type s
  /-- The horizontal identity cell on a vertical arrow. -/
  hId : {a b : O} → (f : Edge V a b) → Cell (edgeId H a) (edgeId H b) f f
  /-- The vertical identity cell on a horizontal arrow. -/
  vId : {a b : O} → (f : Edge H a b) → Cell f f (edgeId V a) (edgeId V b)
  /-- Horizontal pasting of cells with a common vertical boundary. -/
  hComp : {a b c d e f : O} →
    {p : Edge H a b} → {q : Edge H b c} → {r : Edge H d e} → {t : Edge H e f} →
    {l : Edge V a d} → {m : Edge V b e} → {n : Edge V c f} →
    Cell p r l m → Cell q t m n → Cell (edgeComp H p q) (edgeComp H r t) l n
  /-- Vertical pasting of cells with a common horizontal boundary. -/
  vComp : {a b c d e f : O} →
    {p : Edge H a b} → {q : Edge H c d} → {r : Edge H e f} →
    {l : Edge V a c} → {m : Edge V b d} → {n : Edge V c e} → {t : Edge V d f} →
    Cell p q l m → Cell q r n t → Cell p r (edgeComp V l n) (edgeComp V m t)
  h_id_comp_heq : ∀ {a b c d : O} {p : Edge H a b} {q : Edge H c d}
    {l : Edge V a c} {r : Edge V b d} (α : Cell p q l r), HEq (hComp (hId l) α) α
  h_comp_id_heq : ∀ {a b c d : O} {p : Edge H a b} {q : Edge H c d}
    {l : Edge V a c} {r : Edge V b d} (α : Cell p q l r), HEq (hComp α (hId r)) α
  v_id_comp_heq : ∀ {a b c d : O} {p : Edge H a b} {q : Edge H c d}
    {l : Edge V a c} {r : Edge V b d} (α : Cell p q l r), HEq (vComp (vId p) α) α
  v_comp_id_heq : ∀ {a b c d : O} {p : Edge H a b} {q : Edge H c d}
    {l : Edge V a c} {r : Edge V b d} (α : Cell p q l r), HEq (vComp α (vId q)) α
  h_assoc_heq : ∀ {a b c d e f g k : O}
    {p : Edge H a b} {q : Edge H b c} {r : Edge H c d}
    {p' : Edge H e f} {q' : Edge H f g} {r' : Edge H g k}
    {l : Edge V a e} {m : Edge V b f} {n : Edge V c g} {t : Edge V d k}
    (α : Cell p p' l m) (β : Cell q q' m n) (γ : Cell r r' n t),
    HEq (hComp (hComp α β) γ) (hComp α (hComp β γ))
  v_assoc_heq : ∀ {a b c d e f g k : O}
    {p : Edge H a b} {q : Edge H c d} {r : Edge H e f} {t : Edge H g k}
    {l : Edge V a c} {m : Edge V c e} {n : Edge V e g}
    {l' : Edge V b d} {m' : Edge V d f} {n' : Edge V f k}
    (α : Cell p q l l') (β : Cell q r m m') (γ : Cell r t n n'),
    HEq (vComp (vComp α β) γ) (vComp α (vComp β γ))
  interchange : ∀ {a b c d e f g k i : O}
    {p : Edge H a b} {q : Edge H b c} {r : Edge H d e}
    {t : Edge H e f} {x : Edge H g k} {y : Edge H k i}
    {l : Edge V a d} {m : Edge V b e} {n : Edge V c f}
    {l' : Edge V d g} {m' : Edge V e k} {n' : Edge V f i}
    (α : Cell p r l m) (β : Cell q t m n) (γ : Cell r x l' m') (δ : Cell t y m' n'),
    vComp (hComp α β) (hComp γ δ) = hComp (vComp α γ) (vComp β δ)
  hId_vComp : ∀ {a b c : O} (f : Edge V a b) (g : Edge V b c),
    hId (edgeComp V f g) = vComp (hId f) (hId g)
  vId_hComp : ∀ {a b c : O} (f : Edge H a b) (g : Edge H b c),
    vId (edgeComp H f g) = hComp (vId f) (vId g)
  id_id : ∀ a : O, hId (edgeId V a) = vId (edgeId H a)

namespace StrictDoubleCategory

variable {O : Type u} {H : Category.{h} O} {V : Category.{v} O}
  (D : StrictDoubleCategory.{u, h, v, s} O H V)

/-- Transport a cell along equalities of its four boundary arrows. The corner objects
stay fixed; arguments are ordered top, bottom, left, right. -/
def cast {a b c d : O} {p p' : Edge H a b} {q q' : Edge H c d}
    {l l' : Edge V a c} {r r' : Edge V b d}
    (hp : p = p') (hq : q = q') (hl : l = l') (hr : r = r')
    (α : D.Cell p q l r) : D.Cell p' q' l' r' :=
  hp ▸ hq ▸ hl ▸ hr ▸ α

@[simp]
theorem cast_rfl {a b c d : O} {p : Edge H a b} {q : Edge H c d}
    {l : Edge V a c} {r : Edge V b d} (α : D.Cell p q l r) :
    D.cast rfl rfl rfl rfl α = α := (rfl)

/-- Successive boundary transports compose componentwise. -/
@[simp]
theorem cast_cast {a b c d : O} {p p' p'' : Edge H a b} {q q' q'' : Edge H c d}
    {l l' l'' : Edge V a c} {r r' r'' : Edge V b d}
    (hp : p = p') (hq : q = q') (hl : l = l') (hr : r = r')
    (hp' : p' = p'') (hq' : q' = q'') (hl' : l' = l'') (hr' : r' = r'')
    (α : D.Cell p q l r) :
    D.cast hp' hq' hl' hr' (D.cast hp hq hl hr α) =
      D.cast (hp.trans hp') (hq.trans hq') (hl.trans hl') (hr.trans hr') α := by
  cases hp; cases hq; cases hl; cases hr
  cases hp'; cases hq'; cases hl'; cases hr'
  rfl

/-- Transport does not change the heterogeneous value of a cell. -/
theorem cast_heq {a b c d : O} {p p' : Edge H a b} {q q' : Edge H c d}
    {l l' : Edge V a c} {r r' : Edge V b d}
    (hp : p = p') (hq : q = q') (hl : l = l') (hr : r = r')
    (α : D.Cell p q l r) : HEq (D.cast hp hq hl hr α) α := by
  cases hp; cases hq; cases hl; cases hr
  rfl

/-- Equality after a specified transport is equivalent to heterogeneous equality.
This is the bridge from the strict axioms to ordinary equality rewriting. -/
theorem cast_eq_iff_heq {a b c d : O} {p p' : Edge H a b} {q q' : Edge H c d}
    {l l' : Edge V a c} {r r' : Edge V b d}
    (hp : p = p') (hq : q = q') (hl : l = l') (hr : r = r')
    (α : D.Cell p q l r) (β : D.Cell p' q' l' r') :
    D.cast hp hq hl hr α = β ↔ HEq α β := by
  cases hp; cases hq; cases hl; cases hr
  exact heq_iff_eq.symm

/-- Move a boundary transport across an equality using its inverse, without
introducing heterogeneous equality in the statement. -/
theorem cast_eq_iff {a b c d : O} {p p' : Edge H a b} {q q' : Edge H c d}
    {l l' : Edge V a c} {r r' : Edge V b d}
    (hp : p = p') (hq : q = q') (hl : l = l') (hr : r = r')
    (α : D.Cell p q l r) (β : D.Cell p' q' l' r') :
    D.cast hp hq hl hr α = β ↔ α = D.cast hp.symm hq.symm hl.symm hr.symm β := by
  cases hp; cases hq; cases hl; cases hr
  rfl

/-- Boundary transport is injective. -/
@[simp]
theorem cast_inj {a b c d : O} {p p' : Edge H a b} {q q' : Edge H c d}
    {l l' : Edge V a c} {r r' : Edge V b d}
    (hp : p = p') (hq : q = q') (hl : l = l') (hr : r = r')
    (α β : D.Cell p q l r) :
    D.cast hp hq hl hr α = D.cast hp hq hl hr β ↔ α = β := by
  cases hp; cases hq; cases hl; cases hr
  rfl

/-- Horizontal pasting commutes with transport of every external and shared edge. -/
@[simp]
theorem hComp_cast {a b c d e f : O}
    {p p' : Edge H a b} {q q' : Edge H b c}
    {r r' : Edge H d e} {t t' : Edge H e f}
    {l l' : Edge V a d} {m m' : Edge V b e} {n n' : Edge V c f}
    (hp : p = p') (hq : q = q') (hr : r = r') (ht : t = t')
    (hl : l = l') (hm : m = m') (hn : n = n')
    (α : D.Cell p r l m) (β : D.Cell q t m n) :
    D.hComp (D.cast hp hr hl hm α) (D.cast hq ht hm hn β) =
      D.cast (congrArg₂ (edgeComp H) hp hq) (congrArg₂ (edgeComp H) hr ht) hl hn
        (D.hComp α β) := by
  cases hp; cases hq; cases hr; cases ht
  cases hl; cases hm; cases hn
  rfl

/-- Vertical pasting commutes with transport of every external and shared edge. -/
@[simp]
theorem vComp_cast {a b c d e f : O}
    {p p' : Edge H a b} {q q' : Edge H c d} {r r' : Edge H e f}
    {l l' : Edge V a c} {m m' : Edge V b d}
    {n n' : Edge V c e} {t t' : Edge V d f}
    (hp : p = p') (hq : q = q') (hr : r = r')
    (hl : l = l') (hm : m = m') (hn : n = n') (ht : t = t')
    (α : D.Cell p q l m) (β : D.Cell q r n t) :
    D.vComp (D.cast hp hq hl hm α) (D.cast hq hr hn ht β) =
      D.cast hp hr (congrArg₂ (edgeComp V) hl hn) (congrArg₂ (edgeComp V) hm ht)
        (D.vComp α β) := by
  cases hp; cases hq; cases hr
  cases hl; cases hm; cases hn; cases ht
  rfl

/-- Horizontal identity cells respect equality of their vertical edge. -/
@[simp]
theorem cast_hId {a b : O} {f g : Edge V a b} (hfg : f = g) :
    D.cast rfl rfl hfg hfg (D.hId f) = D.hId g := by
  cases hfg
  rfl

/-- Vertical identity cells respect equality of their horizontal edge. -/
@[simp]
theorem cast_vId {a b : O} {f g : Edge H a b} (hfg : f = g) :
    D.cast hfg hfg rfl rfl (D.vId f) = D.vId g := by
  cases hfg
  rfl

/-- The horizontal left unit law after identifying its two horizontal boundaries. -/
@[simp]
theorem h_id_comp {a b c d : O} {p : Edge H a b} {q : Edge H c d}
    {l : Edge V a c} {r : Edge V b d} (α : D.Cell p q l r) :
    D.cast (@Category.id_comp O H _ _ p) (@Category.id_comp O H _ _ q) rfl rfl
      (D.hComp (D.hId l) α) = α :=
  (D.cast_eq_iff_heq _ _ _ _ _ _).mpr (D.h_id_comp_heq α)

/-- The horizontal right unit law after identifying its two horizontal boundaries. -/
@[simp]
theorem h_comp_id {a b c d : O} {p : Edge H a b} {q : Edge H c d}
    {l : Edge V a c} {r : Edge V b d} (α : D.Cell p q l r) :
    D.cast (@Category.comp_id O H _ _ p) (@Category.comp_id O H _ _ q) rfl rfl
      (D.hComp α (D.hId r)) = α :=
  (D.cast_eq_iff_heq _ _ _ _ _ _).mpr (D.h_comp_id_heq α)

/-- The vertical top unit law after identifying its two vertical boundaries. -/
@[simp]
theorem v_id_comp {a b c d : O} {p : Edge H a b} {q : Edge H c d}
    {l : Edge V a c} {r : Edge V b d} (α : D.Cell p q l r) :
    D.cast rfl rfl (@Category.id_comp O V _ _ l) (@Category.id_comp O V _ _ r)
      (D.vComp (D.vId p) α) = α :=
  (D.cast_eq_iff_heq _ _ _ _ _ _).mpr (D.v_id_comp_heq α)

/-- The vertical bottom unit law after identifying its two vertical boundaries. -/
@[simp]
theorem v_comp_id {a b c d : O} {p : Edge H a b} {q : Edge H c d}
    {l : Edge V a c} {r : Edge V b d} (α : D.Cell p q l r) :
    D.cast rfl rfl (@Category.comp_id O V _ _ l) (@Category.comp_id O V _ _ r)
      (D.vComp α (D.vId q)) = α :=
  (D.cast_eq_iff_heq _ _ _ _ _ _).mpr (D.v_comp_id_heq α)

/-- Horizontal associativity with the two horizontal boundary transports explicit. -/
theorem h_assoc {a b c d e f g k : O}
    {p : Edge H a b} {q : Edge H b c} {r : Edge H c d}
    {p' : Edge H e f} {q' : Edge H f g} {r' : Edge H g k}
    {l : Edge V a e} {m : Edge V b f} {n : Edge V c g} {t : Edge V d k}
    (α : D.Cell p p' l m) (β : D.Cell q q' m n) (γ : D.Cell r r' n t) :
    D.cast (@Category.assoc O H _ _ _ _ p q r) (@Category.assoc O H _ _ _ _ p' q' r')
      rfl rfl (D.hComp (D.hComp α β) γ) = D.hComp α (D.hComp β γ) :=
  (D.cast_eq_iff_heq _ _ _ _ _ _).mpr (D.h_assoc_heq α β γ)

/-- Vertical associativity with the two vertical boundary transports explicit. -/
theorem v_assoc {a b c d e f g k : O}
    {p : Edge H a b} {q : Edge H c d} {r : Edge H e f} {t : Edge H g k}
    {l : Edge V a c} {m : Edge V c e} {n : Edge V e g}
    {l' : Edge V b d} {m' : Edge V d f} {n' : Edge V f k}
    (α : D.Cell p q l l') (β : D.Cell q r m m') (γ : D.Cell r t n n') :
    D.cast rfl rfl (@Category.assoc O V _ _ _ _ l m n)
      (@Category.assoc O V _ _ _ _ l' m' n') (D.vComp (D.vComp α β) γ) =
        D.vComp α (D.vComp β γ) :=
  (D.cast_eq_iff_heq _ _ _ _ _ _).mpr (D.v_assoc_heq α β γ)

end StrictDoubleCategory

end TauCeti
