/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Pi.Basic
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Contracting two adjacent entries of a tuple of objects, as a functor

For a monoidal category `C` and `i : Fin n`, `TauCeti.piContractNth C i` is the functor
`(Fin (n + 1) → C) ⥤ (Fin n → C)` that tensors the entries `i` and `i + 1` of a tuple together.
On objects it is Mathlib's `Fin.contractNth` for the operation `⊗` (`TauCeti.piContractNth_obj`).
It is the companion of `TauCeti.piInsertNth`; the tensor powers of a monoidal functor are
compatible with it (`CategoryTheory.Functor.tensorPowContractNthIso`).

The functor is defined by recursion on `i`. Contracting at `0` tensors the first two entries, and
contracting at `i.succ` keeps the first entry and contracts the remaining ones at `i`
(`TauCeti.piContractNth_zero_obj`, `TauCeti.piContractNth_succ_obj`). The entries of the result
are described by `TauCeti.piContractNth_obj_of_lt`, `TauCeti.piContractNth_obj_self` and
`TauCeti.piContractNth_obj_of_gt`.
-/

@[expose] public section

open CategoryTheory MonoidalCategory

universe v u

namespace TauCeti

variable (C : Type u) [Category.{v} C] [MonoidalCategory C]

-- Exposed: tensor powers compute on the image of this functor without rewriting its objects.
/-- The functor `(Fin (n + 1) → C) ⥤ (Fin n → C)` tensoring the entries `i` and `i + 1` of a
tuple together: `(X₀, …, Xₙ) ↦ (X₀, …, X_{i-1}, X_i ⊗ X_{i+1}, X_{i+2}, …, Xₙ)`. On objects it
is Mathlib's `Fin.contractNth` for the operation `⊗` (`TauCeti.piContractNth_obj`). -/
def piContractNth {n : ℕ} (i : Fin n) : (Fin (n + 1) → C) ⥤ (Fin n → C) :=
  go i.val i.isLt
where
  /-- The recursion behind `piContractNth`, on the value of the position. -/
  go : (k : ℕ) → {n : ℕ} → k < n → (Fin (n + 1) → C) ⥤ (Fin n → C)
    | _, 0, h => absurd h (by omega)
    | 0, _ + 1, _ => Functor.pi' (Fin.cons
        ((Pi.eval _ 0).prod' (Pi.eval _ 1) ⋙ tensor C) fun j ↦ Pi.eval _ j.succ.succ)
    | k + 1, _ + 1, h => Functor.pi' (Fin.cons (Pi.eval _ 0)
        fun j ↦ Pi.comap _ Fin.succ ⋙ go k (by omega) ⋙ Pi.eval _ j)
  termination_by structural k => k

variable {C}

/-- Contracting at position `0` tensors the first two entries. -/
theorem piContractNth_zero_obj {n : ℕ} (X : Fin (n + 2) → C) :
    (piContractNth C 0).obj X = Fin.cons (X 0 ⊗ X 1) fun j ↦ X j.succ.succ := by
  funext j
  cases j using Fin.cases <;> rfl

/-- Contracting at position `i.succ` keeps the first entry and contracts the others at
position `i`. -/
theorem piContractNth_succ_obj {n : ℕ} (i : Fin (n + 1)) (X : Fin (n + 3) → C) :
    (piContractNth C i.succ).obj X = Fin.cons (X 0) ((piContractNth C i).obj fun j ↦ X j.succ) := by
  funext j
  cases j using Fin.cases <;> rfl

/-- Before the contracted position, contracting keeps the entries of the tuple. -/
@[simp]
theorem piContractNth_obj_of_lt {n : ℕ} {i j : Fin n} (h : j < i) (X : Fin (n + 1) → C) :
    (piContractNth C i).obj X j = X j.castSucc := by
  induction n with
  | zero => exact j.elim0
  | succ n ih =>
    cases i using Fin.cases with
    | zero => exact absurd h (Fin.not_lt_zero j)
    | succ i =>
      cases j using Fin.cases with
      | zero => rfl
      | succ j => exact ih (Fin.succ_lt_succ_iff.mp h) _

/-- At the contracted position, contracting tensors the two entries `i` and `i + 1` together. -/
@[simp]
theorem piContractNth_obj_self {n : ℕ} (i : Fin n) (X : Fin (n + 1) → C) :
    (piContractNth C i).obj X i = X i.castSucc ⊗ X i.succ := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    cases i using Fin.cases with
    | zero => rfl
    | succ i => exact ih i _

/-- After the contracted position, contracting shifts the entries of the tuple down by one. -/
@[simp]
theorem piContractNth_obj_of_gt {n : ℕ} {i j : Fin n} (h : i < j) (X : Fin (n + 1) → C) :
    (piContractNth C i).obj X j = X j.succ := by
  induction n with
  | zero => exact j.elim0
  | succ n ih =>
    cases j using Fin.cases with
    | zero => exact absurd h (Fin.not_lt_zero i)
    | succ j =>
      cases i using Fin.cases with
      | zero => rfl
      | succ i => exact ih (Fin.succ_lt_succ_iff.mp h) _

-- Not `@[simp]`: rewriting the tuple first would block the entry lemmas above.
/-- On objects, `piContractNth C i` is Mathlib's `Fin.contractNth i.castSucc` for the operation
`⊗`. -/
theorem piContractNth_obj {n : ℕ} (i : Fin n) (X : Fin (n + 1) → C) :
    (piContractNth C i).obj X = Fin.contractNth i.castSucc (· ⊗ ·) X := by
  funext j
  rcases lt_trichotomy j i with h | rfl | h
  · exact (piContractNth_obj_of_lt h X).trans (Fin.contractNth_apply_of_lt _ _ _ _ h).symm
  · exact (piContractNth_obj_self j X).trans (Fin.contractNth_apply_of_eq _ _ _ _ rfl).symm
  · exact (piContractNth_obj_of_gt h X).trans (Fin.contractNth_apply_of_gt _ _ _ _ h).symm

/-- Contracting at position `0`, the first entry of the morphism is the tensor product of the first
two. -/
@[simp]
theorem piContractNth_zero_map_zero {n : ℕ} {X Y : Fin (n + 2) → C} (f : X ⟶ Y) :
    (piContractNth C 0).map f 0 = f 0 ⊗ₘ f 1 :=
  (rfl)

/-- Contracting at position `0`, the later entries of the morphism are shifted down by one. -/
@[simp]
theorem piContractNth_zero_map_succ {n : ℕ} {X Y : Fin (n + 2) → C} (f : X ⟶ Y) (j : Fin n) :
    (piContractNth C 0).map f j.succ = f j.succ.succ :=
  (rfl)

/-- Contracting at position `i.succ`, the first entry of the morphism is kept. -/
@[simp]
theorem piContractNth_succ_map_zero {n : ℕ} (i : Fin (n + 1)) {X Y : Fin (n + 3) → C} (f : X ⟶ Y) :
    (piContractNth C i.succ).map f 0 = f 0 :=
  (rfl)

/-- Contracting at position `i.succ`, the later entries of the morphism are those of the
contraction at position `i` of the remaining entries. -/
@[simp]
theorem piContractNth_succ_map_succ {n : ℕ} (i : Fin (n + 1)) {X Y : Fin (n + 3) → C} (f : X ⟶ Y)
    (j : Fin (n + 1)) :
    (piContractNth C i.succ).map f j.succ = (piContractNth C i).map (fun k ↦ f k.succ) j :=
  (rfl)

end TauCeti
