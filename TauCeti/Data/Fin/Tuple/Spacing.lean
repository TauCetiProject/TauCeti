/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.BigOperators.Fin
public import Mathlib.Order.Fin.Tuple
public import Mathlib.Order.Fin.Basic
public import Mathlib.Algebra.Order.Group.Unbundled.Basic

/-!
# Gaps between points of an interval

`tupleSpacings a b x` takes successive differences after adjoining endpoints `a` and
`b` to a finite tuple. Its entries sum to `b - a`, and initial sums recover the points.
For an increasing tuple in the open interval, every gap is positive.
-/

public section

namespace TauCeti

open Finset

variable {R : Type*} [AddCommGroup R] {n : ℕ}

/-- The successive gaps after adjoining endpoints `a` and `b` to the tuple `x`.
No sorting is performed; unordered points can give negative gaps. -/
def tupleSpacings (a b : R) (x : Fin n → R) (i : Fin (n + 1)) : R :=
  (Fin.cons a (Fin.snoc x b) : Fin (n + 2) → R) i.succ -
    (Fin.cons a (Fin.snoc x b) : Fin (n + 2) → R) i.castSucc

/-- The defining successive-difference formula. -/
theorem tupleSpacings_apply (a b : R) (x : Fin n → R) (i : Fin (n + 1)) :
    tupleSpacings a b x i =
      (Fin.cons a (Fin.snoc x b) : Fin (n + 2) → R) i.succ -
        (Fin.cons a (Fin.snoc x b) : Fin (n + 2) → R) i.castSucc := (rfl)

@[simp]
theorem tupleSpacings_zero (a b : R) (x : Fin (n + 1) → R) :
    tupleSpacings a b x 0 = x 0 - a := by
  simp [tupleSpacings, Fin.snoc_apply_zero]

@[simp]
theorem tupleSpacings_last (a b : R) (x : Fin (n + 1) → R) :
    tupleSpacings a b x (Fin.last (n + 1)) = b - x (Fin.last n) := by
  simp only [tupleSpacings, Fin.cons_succ, Fin.snoc_last]
  rw [← Fin.succ_last, Fin.castSucc_succ, Fin.cons_succ, Fin.snoc_castSucc]

@[simp]
theorem tupleSpacings_castSucc_succ (a b : R) (x : Fin (n + 1) → R) (i : Fin n) :
    tupleSpacings a b x i.castSucc.succ = x i.succ - x i.castSucc := by
  simp only [tupleSpacings, Fin.castSucc_succ, Fin.cons_succ, Fin.snoc_castSucc]
  rw [← Fin.castSucc_succ, Fin.snoc_castSucc]

/-- Initial sums of the gaps recover the corresponding point, relative to the left endpoint. -/
theorem sum_Iic_tupleSpacings (a b : R) (x : Fin n → R) (i : Fin (n + 1)) :
    ∑ j ∈ Finset.Iic i, tupleSpacings a b x j = (Fin.snoc x b : Fin (n + 1) → R) i - a := by
  simpa [tupleSpacings] using Fin.sum_Iic_sub i (Fin.cons a (Fin.snoc x b))

/-- All the gaps together have the length of the original interval. -/
@[simp]
theorem sum_tupleSpacings (a b : R) (x : Fin n → R) :
    ∑ i, tupleSpacings a b x i = b - a := by
  simpa [tupleSpacings] using
    Fin.sum_univ_succ_sub_castSucc (Fin.cons a (Fin.snoc x b) : Fin (n + 2) → R)

@[simp]
theorem tupleSpacings_empty (a b : R) (x : Fin 0 → R) :
    tupleSpacings a b x = fun _ ↦ b - a := by
  ext i
  induction i using Fin.lastCases with
  | last => rfl
  | cast i => exact Fin.elim0 i

/-- Every gap is positive exactly when the points, with their endpoints, increase strictly. -/
theorem tupleSpacings_pos_iff [LinearOrder R] [IsOrderedAddMonoid R]
    (a b : R) (x : Fin n → R) :
    (∀ i, 0 < tupleSpacings a b x i) ↔
      StrictMono x ∧ (∀ i, a < x i) ∧ (∀ i, x i < b) ∧ a < b := by
  have hsnoc : StrictMono (Fin.snoc x b : Fin (n + 1) → R) ↔
      StrictMono x ∧ ∀ i, x i < b := by
    simpa using Fin.strictMono_insertNth_iff (Fin.last n) b x
  simp only [tupleSpacings, sub_pos, ← Fin.strictMono_iff_lt_succ, Fin.strictMono_cons]
  rw [hsnoc]
  constructor
  · rintro ⟨ha, hx, hb⟩
    exact ⟨hx, fun i ↦ by simpa using ha i.castSucc, hb,
      by simpa using ha (Fin.last n)⟩
  · rintro ⟨hx, ha, hb, hab⟩
    refine ⟨?_, hx, hb⟩
    intro i
    induction i using Fin.lastCases with
    | last => simpa using hab
    | cast i => simpa using ha i

end TauCeti
