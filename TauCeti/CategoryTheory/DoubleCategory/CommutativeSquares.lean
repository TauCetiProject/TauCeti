/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.DoubleCategory.Basic
public import Mathlib.CategoryTheory.CommSq

/-!
# The strict double category of commutative squares

Every category gives a strict double category whose horizontal and vertical arrows are
its morphisms and whose cells are commutative squares. This construction reuses Mathlib's
`CommSq`, `CommSq.horiz_comp`, and `CommSq.vert_comp`. The lift to `Type` only accommodates
the cell universe of `StrictDoubleCategory`; it adds no data to a square.

`commutativeSquares.cellEquiv` identifies the cells with Mathlib's commutative squares,
giving construction and elimination of cells without unfolding the double-category structure.
-/

public section

universe u v

namespace TauCeti.StrictDoubleCategory

open CategoryTheory

/-- The strict double category of commutative squares in a category. Both edge
categories are the given category, supplied explicitly to the double-category structure. -/
def commutativeSquares (C : Type u) [Category.{v} C] :
    StrictDoubleCategory C (inferInstance : Category.{v} C) (inferInstance : Category.{v} C) where
  Cell p q l r := PLift (CommSq p l r q)
  hId f := ⟨⟨by simp⟩⟩
  vId f := ⟨⟨by simp⟩⟩
  hComp α β := ⟨α.down.horiz_comp β.down⟩
  vComp α β := ⟨α.down.vert_comp β.down⟩
  hId_hComp _ := Subsingleton.elim _ _
  hComp_hId _ := Subsingleton.elim _ _
  vId_vComp _ := Subsingleton.elim _ _
  vComp_vId _ := Subsingleton.elim _ _
  hComp_assoc _ _ _ := Subsingleton.elim _ _
  vComp_assoc _ _ _ := Subsingleton.elim _ _
  interchange _ _ _ _ := Subsingleton.elim _ _
  hId_comp _ _ := Subsingleton.elim _ _
  vId_comp _ _ := Subsingleton.elim _ _
  hId_id _ := Subsingleton.elim _ _

namespace commutativeSquares

variable {C : Type u} [Category.{v} C]

instance {a b c d : C} (p : a ⟶ b) (q : c ⟶ d) (l : a ⟶ c) (r : b ⟶ d) :
    Subsingleton ((commutativeSquares C).Cell p q l r) :=
  inferInstanceAs (Subsingleton (PLift (CommSq p l r q)))

/-- Cells in the double category are exactly commutative squares, with the arguments
reordered from top/bottom/left/right to Mathlib's top/left/right/bottom convention. -/
noncomputable def cellEquiv {a b c d : C} (p : a ⟶ b) (q : c ⟶ d) (l : a ⟶ c) (r : b ⟶ d) :
    (commutativeSquares C).Cell p q l r ≃ CommSq p l r q :=
  Equiv.plift

/-- The square equation of a cell. -/
theorem w {a b c d : C} {p : a ⟶ b} {q : c ⟶ d} {l : a ⟶ c} {r : b ⟶ d}
    (α : (commutativeSquares C).Cell p q l r) : p ≫ r = l ≫ q :=
  (cellEquiv p q l r α).w

end commutativeSquares

end TauCeti.StrictDoubleCategory
