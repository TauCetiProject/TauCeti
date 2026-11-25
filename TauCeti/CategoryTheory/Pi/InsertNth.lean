/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Pi.Basic
public import Mathlib.CategoryTheory.Products.Basic
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Inserting an entry into a tuple of objects, as a functor

For a category `C` and `i : Fin (n + 1)`, `TauCeti.piInsertNth C i` is the functor
`C × (Fin n → C) ⥤ (Fin (n + 1) → C)` that inserts its first argument into the tuple at position
`i`. On objects it is Mathlib's `Fin.insertNth` (`TauCeti.piInsertNth_obj`).

Fixing the tuple gives the functor `C ⥤ (Fin (n + 1) → C)` that varies only the entry in slot
`i`; through it, a functor out of a product of `n + 1` copies of `C` can be asked to be additive
or linear in each slot separately. Fixing the inserted object instead gives a functor
`(Fin n → C) ⥤ (Fin (n + 1) → C)`, for instance the insertion of the monoidal unit.

The functor is defined by recursion on `i`. Entry by entry, inserting at `0` agrees definitionally
with `Fin.cons`, and inserting at `i.succ` keeps the first entry and inserts at `i` into the
remaining ones. The corresponding equations of whole tuples, proved entry by entry, are
`TauCeti.piInsertNth_zero_obj` and `TauCeti.piInsertNth_succ_obj`.
-/

@[expose] public section

open CategoryTheory

universe v u

namespace TauCeti

variable (C : Type u) [Category.{v} C]

-- Exposed: functors out of `Fin (n + 1) → C` defined by recursion on `n`, such as tensor powers,
-- compute on the image of this functor without rewriting its objects.
/-- The functor `C × (Fin n → C) ⥤ (Fin (n + 1) → C)` inserting an object into a tuple at
position `i`; on objects it is `Fin.insertNth i` (`TauCeti.piInsertNth_obj`). -/
def piInsertNth {n : ℕ} (i : Fin (n + 1)) : C × (Fin n → C) ⥤ (Fin (n + 1) → C) :=
  go i.val i.isLt
where
  /-- The recursion behind `piInsertNth`, on the value of the position. -/
  go : (k : ℕ) → {n : ℕ} → k < n + 1 → C × (Fin n → C) ⥤ (Fin (n + 1) → C)
    | 0, _, _ => Functor.pi' (Fin.cons (CategoryTheory.Prod.fst C _) fun j ↦
        CategoryTheory.Prod.snd C _ ⋙ Pi.eval _ j)
    | _ + 1, 0, h => absurd h (by omega)
    | k + 1, _ + 1, h => Functor.pi' (Fin.cons (CategoryTheory.Prod.snd C _ ⋙ Pi.eval _ 0)
        fun j ↦ (𝟭 C).prod (Pi.comap _ Fin.succ) ⋙ go k (by omega) ⋙ Pi.eval _ j)
  termination_by structural k => k

variable {C}

/-- Inserting at position `0` prepends the object. -/
theorem piInsertNth_zero_obj {n : ℕ} (p : C × (Fin n → C)) :
    (piInsertNth C 0).obj p = Fin.cons p.1 p.2 := by
  funext j
  cases j using Fin.cases <;> rfl

/-- Inserting at position `i.succ` keeps the first entry and inserts at `i` into the others. -/
theorem piInsertNth_succ_obj {n : ℕ} (i : Fin (n + 1)) (p : C × (Fin (n + 1) → C)) :
    (piInsertNth C i.succ).obj p =
      Fin.cons (p.2 0) ((piInsertNth C i).obj (p.1, fun j ↦ p.2 j.succ)) := by
  funext j
  cases j using Fin.cases <;> rfl

/-- Inserting at position `0`, the new first entry of the morphism is the inserted morphism. -/
@[simp]
theorem piInsertNth_zero_map_zero {n : ℕ} {p q : C × (Fin n → C)} (f : p ⟶ q) :
    (piInsertNth C 0).map f 0 = f.1 :=
  (rfl)

/-- Inserting at position `0`, the later entries of the morphism are those of the tuple. -/
@[simp]
theorem piInsertNth_zero_map_succ {n : ℕ} {p q : C × (Fin n → C)} (f : p ⟶ q) (j : Fin n) :
    (piInsertNth C 0).map f j.succ = f.2 j :=
  (rfl)

/-- Inserting at position `i.succ`, the first entry of the morphism is that of the tuple. -/
@[simp]
theorem piInsertNth_succ_map_zero {n : ℕ} (i : Fin (n + 1)) {p q : C × (Fin (n + 1) → C)}
    (f : p ⟶ q) :
    (piInsertNth C i.succ).map f 0 = f.2 0 :=
  (rfl)

/-- Inserting at position `i.succ`, the later entries of the morphism are those of the insertion
at position `i` into the remaining entries. -/
@[simp]
theorem piInsertNth_succ_map_succ {n : ℕ} (i : Fin (n + 1)) {p q : C × (Fin (n + 1) → C)}
    (f : p ⟶ q) (j : Fin (n + 1)) :
    (piInsertNth C i.succ).map f j.succ =
      (piInsertNth C i).map (Prod.mkHom f.1 fun k ↦ f.2 k.succ) j :=
  (rfl)

/-- On objects, `piInsertNth C i` is `Fin.insertNth i`. -/
@[simp]
theorem piInsertNth_obj {n : ℕ} (i : Fin (n + 1)) (p : C × (Fin n → C)) :
    (piInsertNth C i).obj p = Fin.insertNth i p.1 p.2 := by
  induction n with
  | zero =>
    obtain rfl : i = 0 := Fin.fin_one_eq_zero i
    rw [piInsertNth_zero_obj, Fin.insertNth_zero']
  | succ n ih =>
    cases i using Fin.cases with
    | zero => rw [piInsertNth_zero_obj, Fin.insertNth_zero']
    | succ i =>
      rw [piInsertNth_succ_obj, ih, ← Fin.insertNth_succ_cons]
      exact congrArg _ (Fin.cons_self_tail p.2)

end TauCeti
