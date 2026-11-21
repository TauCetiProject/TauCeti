/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.DoubleCategory.Basic
public import Mathlib.CategoryTheory.CommSq

import Mathlib.CategoryTheory.Types.Basic
import TauCeti.CategoryTheory.DoubleCategory.Functor

/-!
# The strict double category of commutative squares

Every category gives a strict double category whose horizontal and vertical arrows are
its morphisms and whose cells are commutative squares. This construction reuses Mathlib's
`CommSq`, `CommSq.horiz_comp`, and `CommSq.vert_comp`. The lift to `Type` only accommodates
the cell universe of `StrictDoubleCategory`; it adds no data to a square.

`commutativeSquares.cellEquiv` identifies the cells with Mathlib's commutative squares,
giving construction and elimination of cells without unfolding the double-category structure.

The final section checks boundary indexing and transport on a grid of nonidentity
natural-number translations, identity cells, and double-isomorphism inverse laws. Its cells
at a fixed boundary form a subsingleton, so these checks cannot test interchange on distinct
cell values. They do not supply a model with nonsubsingleton cell types.
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
@[reassoc]
theorem w {a b c d : C} {p : a ⟶ b} {q : c ⟶ d} {l : a ⟶ c} {r : b ⟶ d}
    (α : (commutativeSquares C).Cell p q l r) : p ≫ r = l ≫ q :=
  (cellEquiv p q l r α).w

end commutativeSquares

end TauCeti.StrictDoubleCategory

end -- public section

/-! ## Boundary checks

The four squares below have natural-number translations as edges. Both orders of pasting
give a cell with top, bottom, left and right edges translating by 3, 15, 30 and 42,
respectively. All twelve edges in the grid are nonidentity.

These examples check boundaries and transport only: equality of cells with a fixed
boundary is automatic in this model.
-/

open CategoryTheory TauCeti TauCeti.StrictDoubleCategory

noncomputable section

namespace TauCeti.StrictDoubleCategory.commutativeSquares

private def shift (k : ℕ) : ℕ ⟶ ℕ := ↾fun n => n + k

private lemma shift_comp (k l : ℕ) : shift k ≫ shift l = shift (k + l) := by
  ext n
  simp [shift, Nat.add_assoc]

private def translationSquare (p q l r : ℕ) (h : p + r = l + q) :
    (commutativeSquares (Type)).Cell (shift p) (shift q) (shift l) (shift r) :=
  (cellEquiv _ _ _ _).symm ⟨by
    ext n
    simpa [shift, Nat.add_assoc] using congrArg (n + ·) h⟩

-- Each of the twelve arrows in the grid is nonidentity.
example : ∀ k ∈ ([1, 2, 4, 5, 7, 8, 10, 13, 16, 20, 23, 26] : List ℕ),
    shift k ≠ 𝟙 ℕ := by
  intro k hk heq
  have hz : k = 0 := by
    simpa [shift] using congrArg (fun f : ℕ ⟶ ℕ => f 0) heq
  subst k
  simp at hk

-- Both pasting orders have the asserted outside boundary, after transport.
-- Cell equality itself is automatic in this model; use the interchange API explicitly.
example :
    let D := commutativeSquares (Type)
    let α := translationSquare 1 4 10 13 (by decide)
    let β := translationSquare 2 5 13 16 (by decide)
    let γ := translationSquare 4 7 20 23 (by decide)
    let δ := translationSquare 5 8 23 26 (by decide)
    let rows : D.Cell (shift 3) (shift 15) (shift 30) (shift 42) :=
      DoubleCategoryStruct.Cell.cast (D := D.toDoubleCategoryStruct)
        (shift_comp 1 2) (shift_comp 7 8) (shift_comp 10 20) (shift_comp 16 26)
        (D.vComp (D.hComp α β) (D.hComp γ δ))
    let columns : D.Cell (shift 3) (shift 15) (shift 30) (shift 42) :=
      DoubleCategoryStruct.Cell.cast (D := D.toDoubleCategoryStruct)
        (shift_comp 1 2) (shift_comp 7 8) (shift_comp 10 20) (shift_comp 16 26)
        (D.hComp (D.vComp α γ) (D.vComp β δ))
    rows = columns := by
  dsimp only
  exact congrArg
    (DoubleCategoryStruct.Cell.cast
      (D := (commutativeSquares (Type)).toDoubleCategoryStruct)
      (shift_comp 1 2) (shift_comp 7 8) (shift_comp 10 20) (shift_comp 16 26))
    ((commutativeSquares (Type)).interchange _ _ _ _)

-- Eliminate the pasted cell to a square in Mathlib with the computed boundary.
example : CommSq (shift 3) (shift 30) (shift 42) (shift 15) := by
  let D := commutativeSquares (Type)
  let pasted := D.vComp
    (D.hComp (translationSquare 1 4 10 13 (by decide))
      (translationSquare 2 5 13 16 (by decide)))
    (D.hComp (translationSquare 4 7 20 23 (by decide))
      (translationSquare 5 8 23 26 (by decide)))
  exact cellEquiv _ _ _ _
    (DoubleCategoryStruct.Cell.cast (D := D.toDoubleCategoryStruct)
      (shift_comp 1 2) (shift_comp 7 8) (shift_comp 10 20) (shift_comp 16 26) pasted)

-- Both identity cells lie over four identity edges and agree.
example :
    ((commutativeSquares (Type)).hId (𝟙 ℕ) :
      (commutativeSquares (Type)).Cell (𝟙 ℕ) (𝟙 ℕ) (𝟙 ℕ) (𝟙 ℕ)) =
      (commutativeSquares (Type)).vId (𝟙 ℕ) :=
  (commutativeSquares (Type)).hId_id ℕ

-- The unit-law simp lemmas cancel transport on a concrete nonidentity boundary.
example :
    let D := commutativeSquares (Type)
    let α := translationSquare 1 4 10 13 (by decide)
    DoubleCategoryStruct.Cell.cast (D := D.toDoubleCategoryStruct)
      (Category.id_comp (shift 1)) (Category.id_comp (shift 4)) rfl rfl
      (D.hComp (D.hId (shift 10)) α) = α := by
  dsimp only
  simp

-- A noncommuting boundary has no cell: its two routes translate by 6 and 5.
example : IsEmpty ((commutativeSquares (Type)).Cell
    (shift 1) (shift 2) (shift 3) (shift 5)) where
  false α := by
    have h := congrArg (fun f : ℕ ⟶ ℕ => f 0) (w α)
    simp [shift] at h

-- Exercise both inverse laws, including the heterogeneous boundary equalities.
example (e : StrictDoubleIso (commutativeSquares (Type)) (commutativeSquares (Type))) :
    e.inv.map (e.hom.map (translationSquare 1 4 10 13 (by decide))) ≍
      translationSquare 1 4 10 13 (by decide) :=
  e.inv_map_hom_map_heq _

example (e : StrictDoubleIso (commutativeSquares (Type)) (commutativeSquares (Type))) :
    e.hom.map (e.inv.map (translationSquare 1 4 10 13 (by decide))) ≍
      translationSquare 1 4 10 13 (by decide) :=
  e.hom_map_inv_map_heq _

-- The reassociated equation rewrites inside a longer composite.
example : shift 1 ≫ shift 13 ≫ shift 2 = shift 10 ≫ shift 4 ≫ shift 2 := by
  rw [w_assoc (translationSquare 1 4 10 13 (by decide))]

end TauCeti.StrictDoubleCategory.commutativeSquares
