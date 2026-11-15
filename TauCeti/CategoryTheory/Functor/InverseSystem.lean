/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# Transitions of inverse systems

An inverse system indexed by a preorder `ι` is a functor `F : ιᵒᵖ ⥤ C`; for `i ≤ j` its transition
is `F.map (homOfLE h).op : F.obj (op j) ⟶ F.obj (op i)`. Towers are the case `ι = ℕ`. This file
records two facts used to manipulate transitions without unfolding the index category: composite
transitions compose, and the transitions out of two equal terms of a product agree, which absorbs
index arithmetic such as `n + 1 + k = n + (k + 1)`.

## Main declarations

* `CategoryTheory.Functor.map_homOfLE_op_comp_map_homOfLE_op`: transitions compose.
* `CategoryTheory.Functor.π_comp_map_homOfLE_op_congr`: a projection from the product of the
  terms followed by a transition depends only on the index of the projection, not on how it is
  written.
-/

public section

namespace CategoryTheory

open Limits Opposite

namespace Functor

variable {C : Type*} [Category* C] {ι : Type*} [Preorder ι] (F : ιᵒᵖ ⥤ C)

/-- The transitions of an inverse system compose: for `i ≤ j ≤ k`, the transition
`F k ⟶ F j` followed by `F j ⟶ F i` is the transition `F k ⟶ F i`. -/
@[reassoc]
lemma map_homOfLE_op_comp_map_homOfLE_op {i j k : ι} (hij : i ≤ j) (hjk : j ≤ k) :
    F.map (homOfLE hjk).op ≫ F.map (homOfLE hij).op = F.map (homOfLE (hij.trans hjk)).op := by
  rw [← F.map_comp, ← op_comp, homOfLE_comp]

/-- Projections from the product of the terms of an inverse system to two equal terms, followed by
the transitions to a fixed term, agree. This absorbs index arithmetic such as
`n + 1 + k = n + (k + 1)`, which does not hold definitionally. -/
lemma π_comp_map_homOfLE_op_congr [HasProduct fun i : ι ↦ F.obj (op i)] {n i j : ι} (h : i = j)
    (hi : n ≤ i) (hj : n ≤ j) :
    Pi.π (fun i : ι ↦ F.obj (op i)) i ≫ F.map (homOfLE hi).op =
      Pi.π (fun i : ι ↦ F.obj (op i)) j ≫ F.map (homOfLE hj).op := by
  subst h
  rfl

end Functor

end CategoryTheory
