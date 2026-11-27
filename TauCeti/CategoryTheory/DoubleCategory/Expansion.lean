/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.DoubleCategory.Implicit

/-!
# Expansion to path boundaries

Every arrow of a strict double category can be regarded as a generating edge. A cell on four
paths is then an original cell whose boundaries are the composites of those paths. Pasting
uses the original pasting, transported along evaluation of concatenation. This gives a strict
double category on the two free path categories, without identifying different paths having
the same composite.

Evaluation is Mathlib's `CategoryTheory.composePath`: its empty, singleton and concatenation
formulas apply separately with the explicitly supplied horizontal and vertical categories.
`StrictDoubleCategory.expand` supplies the expanded implicit double category; the computation
lemmas describe its cells, identities, pastings and boundary transport in the original category.

## References

* A. D. Fairbanks and M. Shulman, *Doubly weak double categories*, Applied Categorical
  Structures **34** (2026), article 26; arXiv:2506.23651, Definition 3.12.
-/

public section

universe s u h v

namespace TauCeti

open CategoryTheory StrictDoubleCategory

variable {O : Type u} {H : Category.{h} O} {V : Category.{v} O}

namespace DoubleCategoryStruct

variable (D : DoubleCategoryStruct.{s} O H V)

/-- Expand double-category data to path boundaries, evaluating each path in its edge category.
The body is exposed so that the cell family computes at evaluated boundaries. -/
@[expose]
def expand : DoubleCategoryStruct.{s} O (pathCategory O H.toQuiver)
    (pathCategory O V.toQuiver) where
  Cell p q l r := D.Cell (@composePath O H _ _ p) (@composePath O H _ _ q)
    (@composePath O V _ _ l) (@composePath O V _ _ r)
  hId f := D.hId (@composePath O V _ _ f)
  vId f := D.vId (@composePath O H _ _ f)
  hComp α β := (D.hComp α β).cast
    (composePath_comp _ _).symm (composePath_comp _ _).symm rfl rfl
  vComp α β := (D.vComp α β).cast
    rfl rfl (composePath_comp _ _).symm (composePath_comp _ _).symm

/-- Expanded cells are original cells on the four evaluated boundaries. -/
@[simp]
theorem expand_Cell {a b c d : O} (p : @Quiver.Path O H.toQuiver a b)
    (q : @Quiver.Path O H.toQuiver c d) (l : @Quiver.Path O V.toQuiver a c)
    (r : @Quiver.Path O V.toQuiver b d) :
    D.expand.Cell p q l r = D.Cell (@composePath O H _ _ p) (@composePath O H _ _ q)
      (@composePath O V _ _ l) (@composePath O V _ _ r) :=
  (rfl)

/-- The horizontal identity on a vertical path is the identity on its evaluated edge. -/
@[simp]
theorem expand_hId {a b : O} (f : @Quiver.Path O V.toQuiver a b) :
    D.expand.hId f = D.hId (@composePath O V _ _ f) :=
  (rfl)

/-- The vertical identity on a horizontal path is the identity on its evaluated edge. -/
@[simp]
theorem expand_vId {a b : O} (f : @Quiver.Path O H.toQuiver a b) :
    D.expand.vId f = D.vId (@composePath O H _ _ f) :=
  (rfl)

/-- Horizontal pasting evaluates to original pasting, transported on the top and bottom. -/
@[simp]
theorem expand_hComp {a b c d e f : O}
    {p : @Quiver.Path O H.toQuiver a b} {q : @Quiver.Path O H.toQuiver b c}
    {r : @Quiver.Path O H.toQuiver d e} {t : @Quiver.Path O H.toQuiver e f}
    {l : @Quiver.Path O V.toQuiver a d} {m : @Quiver.Path O V.toQuiver b e}
    {n : @Quiver.Path O V.toQuiver c f}
    (α : D.expand.Cell p r l m) (β : D.expand.Cell q t m n) :
    D.expand.hComp α β = Cell.cast (D := D)
      (composePath_comp p q).symm (composePath_comp r t).symm rfl rfl
      (D.hComp (p := @composePath O H _ _ p) (q := @composePath O H _ _ q)
        (r := @composePath O H _ _ r) (t := @composePath O H _ _ t) α β) :=
  (rfl)

/-- Vertical pasting evaluates to original pasting, transported on the left and right. -/
@[simp]
theorem expand_vComp {a b c d e f : O}
    {p : @Quiver.Path O H.toQuiver a b} {q : @Quiver.Path O H.toQuiver c d}
    {r : @Quiver.Path O H.toQuiver e f}
    {l : @Quiver.Path O V.toQuiver a c} {m : @Quiver.Path O V.toQuiver b d}
    {n : @Quiver.Path O V.toQuiver c e} {t : @Quiver.Path O V.toQuiver d f}
    (α : D.expand.Cell p q l m) (β : D.expand.Cell q r n t) :
    D.expand.vComp α β = Cell.cast (D := D)
      rfl rfl (composePath_comp l n).symm (composePath_comp m t).symm
      (D.vComp α β) :=
  (rfl)

/-- Boundary transport in the expansion is transport along the evaluated equalities. -/
theorem expand_cast {a b c d : O}
    {p p' : @Quiver.Path O H.toQuiver a b} {q q' : @Quiver.Path O H.toQuiver c d}
    {l l' : @Quiver.Path O V.toQuiver a c} {r r' : @Quiver.Path O V.toQuiver b d}
    (hp : p = p') (hq : q = q') (hl : l = l') (hr : r = r')
    (α : D.expand.Cell p q l r) :
    Cell.cast (D := D.expand) hp hq hl hr α = α.cast
      (congrArg (@composePath O H a b) hp) (congrArg (@composePath O H c d) hq)
      (congrArg (@composePath O V a c) hl) (congrArg (@composePath O V b d) hr) := by
  subst hp hq hl hr
  rfl

end DoubleCategoryStruct

namespace StrictDoubleCategory

open DoubleCategoryStruct

variable (D : StrictDoubleCategory.{s} O H V)

/-- Regard all edges of a strict double category as generators. Cells are indexed by paths,
and their values are the original cells on the evaluated boundaries. No representation choices
are needed for this construction. The body is exposed so that expanded cells compute at
their evaluated boundaries. -/
@[expose]
def expand : ImplicitDoubleCategory.{s} O H.toQuiver V.toQuiver where
  toDoubleCategoryStruct := D.toDoubleCategoryStruct.expand
  -- Unfold just the expansion data, then use the original laws and normalize transports.
  -- `erw` passes through the path category on `Paths O`, read here on the original objects `O`.
  hId_hComp α := by
    erw [expand_cast D.toDoubleCategoryStruct]
    dsimp only [DoubleCategoryStruct.expand]
    erw [D.hId_hComp, Cell.cast_cast]
  hComp_hId α := by
    erw [expand_cast D.toDoubleCategoryStruct]
    dsimp only [DoubleCategoryStruct.expand]
    erw [D.hComp_hId, Cell.cast_cast]
  vId_vComp α := by
    erw [expand_cast D.toDoubleCategoryStruct]
    dsimp only [DoubleCategoryStruct.expand]
    erw [D.vId_vComp, Cell.cast_cast]
  vComp_vId α := by
    erw [expand_cast D.toDoubleCategoryStruct]
    dsimp only [DoubleCategoryStruct.expand]
    erw [D.vComp_vId, Cell.cast_cast]
  hComp_assoc α β γ := by
    erw [expand_cast D.toDoubleCategoryStruct]
    dsimp only [DoubleCategoryStruct.expand]
    erw [hComp_cast_left, hComp_cast_right, D.hComp_assoc]
    repeat erw [Cell.cast_cast]
  vComp_assoc α β γ := by
    erw [expand_cast D.toDoubleCategoryStruct]
    dsimp only [DoubleCategoryStruct.expand]
    erw [vComp_cast_top, vComp_cast_bottom, D.vComp_assoc]
    repeat erw [Cell.cast_cast]
  interchange α β γ δ := by
    dsimp only [DoubleCategoryStruct.expand]
    erw [vComp_cast_cast, hComp_cast_cast, D.interchange]
    repeat erw [Cell.cast_cast]
  hId_comp f g := by
    dsimp only [DoubleCategoryStruct.expand]
    erw [← D.hId_comp, cast_hId]
  vId_comp f g := by
    dsimp only [DoubleCategoryStruct.expand]
    erw [← D.vId_comp, cast_vId]
  hId_id a := D.hId_id a

/-- The data of the expanded strict double category are the expansion of its original data. -/
@[simp]
theorem expand_toDoubleCategoryStruct :
    D.expand.toDoubleCategoryStruct = D.toDoubleCategoryStruct.expand :=
  (rfl)

/-- Expanded cells are original cells on evaluated paths. -/
theorem expand_Cell {a b c d : O} (p : @Quiver.Path O H.toQuiver a b)
    (q : @Quiver.Path O H.toQuiver c d) (l : @Quiver.Path O V.toQuiver a c)
    (r : @Quiver.Path O V.toQuiver b d) :
    D.expand.Cell p q l r = D.Cell (@composePath O H _ _ p) (@composePath O H _ _ q)
      (@composePath O V _ _ l) (@composePath O V _ _ r) :=
  D.toDoubleCategoryStruct.expand_Cell p q l r

/-- The expanded horizontal identity is the original identity on the evaluated vertical path. -/
@[simp]
theorem expand_hId {a b : O} (f : @Quiver.Path O V.toQuiver a b) :
    D.expand.hId f = D.hId (@composePath O V _ _ f) :=
  D.toDoubleCategoryStruct.expand_hId f

/-- The expanded vertical identity is the original identity on the evaluated horizontal path. -/
@[simp]
theorem expand_vId {a b : O} (f : @Quiver.Path O H.toQuiver a b) :
    D.expand.vId f = D.vId (@composePath O H _ _ f) :=
  D.toDoubleCategoryStruct.expand_vId f

/-- Expanded horizontal pasting is original pasting with the evaluated concatenation boundaries. -/
@[simp]
theorem expand_hComp {a b c d e f : O}
    {p : @Quiver.Path O H.toQuiver a b} {q : @Quiver.Path O H.toQuiver b c}
    {r : @Quiver.Path O H.toQuiver d e} {t : @Quiver.Path O H.toQuiver e f}
    {l : @Quiver.Path O V.toQuiver a d} {m : @Quiver.Path O V.toQuiver b e}
    {n : @Quiver.Path O V.toQuiver c f}
    (α : D.expand.Cell p r l m) (β : D.expand.Cell q t m n) :
    D.expand.hComp α β = Cell.cast (D := D.toDoubleCategoryStruct)
      (composePath_comp p q).symm (composePath_comp r t).symm rfl rfl
      (D.hComp (p := @composePath O H _ _ p) (q := @composePath O H _ _ q)
        (r := @composePath O H _ _ r) (t := @composePath O H _ _ t) α β) :=
  D.toDoubleCategoryStruct.expand_hComp α β

/-- Expanded vertical pasting is original pasting with the evaluated concatenation boundaries. -/
@[simp]
theorem expand_vComp {a b c d e f : O}
    {p : @Quiver.Path O H.toQuiver a b} {q : @Quiver.Path O H.toQuiver c d}
    {r : @Quiver.Path O H.toQuiver e f}
    {l : @Quiver.Path O V.toQuiver a c} {m : @Quiver.Path O V.toQuiver b d}
    {n : @Quiver.Path O V.toQuiver c e} {t : @Quiver.Path O V.toQuiver d f}
    (α : D.expand.Cell p q l m) (β : D.expand.Cell q r n t) :
    D.expand.vComp α β = Cell.cast (D := D.toDoubleCategoryStruct)
      rfl rfl (composePath_comp l n).symm (composePath_comp m t).symm (D.vComp α β) :=
  D.toDoubleCategoryStruct.expand_vComp α β

end StrictDoubleCategory

end TauCeti
