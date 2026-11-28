/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.DoubleCategory.Expansion.Representation

/-!
# Evaluation of expanded double categories

Composing each path boundary defines a strict double functor from the expansion of a strict
double category back to that category. Its cell map retains the original cell, and it
preserves both pastings with their evaluation transports. On horizontal globular categories
it is the fully faithful evaluation functor used to construct the representation comparisons.

## References

* A. D. Fairbanks and M. Shulman, *Doubly weak double categories*, Applied Categorical
  Structures **34** (2026), article 26; Definition 3.12 and Proposition 3.13.
-/

public section

universe s u h v

namespace TauCeti.StrictDoubleCategory

open CategoryTheory DoubleCategoryStruct

variable {O : Type u} {H : Category.{h} O} {V : Category.{v} O}
  (D : StrictDoubleCategory.{s} O H V)

/-- Evaluate all four path boundaries, retaining the underlying original cell.
The body is exposed so that the evaluated boundaries compute in cell types. -/
@[expose]
def expandEval : StrictDoubleFunctor D.expand D where
  obj a := a
  hMap p := @composePath O H _ _ p
  hMap_id _ := rfl
  hMap_comp p q := @composePath_comp O H _ _ _ p q
  vMap p := @composePath O V _ _ p
  vMap_id _ := rfl
  vMap_comp p q := @composePath_comp O V _ _ _ p q
  map α := α
  map_hId _ := rfl
  map_vId _ := rfl
  map_hComp α β := D.expand_hComp α β
  map_vComp α β := D.expand_vComp α β

@[simp]
theorem expandEval_obj (a : O) : D.expandEval.obj a = a := (rfl)

@[simp]
theorem expandEval_hMap {a b : O} (p : Edge (pathCategory O H.toQuiver) a b) :
    D.expandEval.hMap p = @composePath O H _ _ p := (rfl)

@[simp]
theorem expandEval_vMap {a b : O} (p : Edge (pathCategory O V.toQuiver) a b) :
    D.expandEval.vMap p = @composePath O V _ _ p := (rfl)

@[simp]
theorem expandEval_map {a b c d : O} {p : Edge (pathCategory O H.toQuiver) a b}
    {q : Edge (pathCategory O H.toQuiver) c d} {l : Edge (pathCategory O V.toQuiver) a c}
    {r : Edge (pathCategory O V.toQuiver) b d} (α : D.expand.Cell p q l r) :
    D.expandEval.map α = α := (rfl)

/-- The globular action of evaluation agrees with the existing fully faithful evaluation. -/
@[simp]
theorem expandEval_horizontalGlobularFunctor (a b : O) :
    D.expandEval.horizontalGlobularFunctor a b = D.expandHorizontalEval a b := by
  rfl

end TauCeti.StrictDoubleCategory
