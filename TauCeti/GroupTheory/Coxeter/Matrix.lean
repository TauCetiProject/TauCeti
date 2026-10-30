/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Coxeter.Matrix

/-!
# Elementary facts about Coxeter matrices

This file gives convenient equations for entries of Mathlib's type-`A` Coxeter matrix, and defines
the Coxeter matrix `TauCeti.coxeterMatrixAInfty` of type `A_∞` on `ℕ`, whose Coxeter group is the
group of finitary permutations of `ℕ` and whose Hecke algebra is the infinite type-A Hecke algebra.
The type-`A` matrix on `Fin m` is its restriction to the first `m` indices
(`TauCeti.coxeterMatrixA_eq_coxeterMatrixAInfty`).
-/

public section

namespace TauCeti

variable {m : ℕ} {i j : Fin m}

/-- The entries of Mathlib's type-`A` Coxeter matrix, unfolded. -/
theorem coxeterMatrixA_apply (i j : Fin m) :
    CoxeterMatrix.A m i j =
      if i = j then 1 else if (j : ℕ) + 1 = i ∨ (i : ℕ) + 1 = j then 3 else 2 :=
  rfl

/-- Neighbouring indices of the type-`A` Coxeter matrix carry the entry `3`. -/
theorem coxeterMatrixA_eq_three (h : (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i) :
    CoxeterMatrix.A m i j = 3 := by
  rw [coxeterMatrixA_apply]
  split_ifs <;> simp_all

/-- Indices of the type-`A` Coxeter matrix at distance at least two carry the entry `2`. -/
theorem coxeterMatrixA_eq_two (h : (i : ℕ) + 2 ≤ j ∨ (j : ℕ) + 2 ≤ i) :
    CoxeterMatrix.A m i j = 2 := by
  rw [coxeterMatrixA_apply]
  split_ifs <;> simp_all
  all_goals omega

/-- The Coxeter matrix of type `A_∞` on `ℕ`: neighbouring indices carry the entry `3` and indices
at distance at least two carry the entry `2`. Its Coxeter group is the group of finitary
permutations of `ℕ`, with simple reflections the adjacent transpositions. -/
def coxeterMatrixAInfty : CoxeterMatrix ℕ where
  M := Matrix.of fun i j : ℕ ↦ if i = j then 1 else if j + 1 = i ∨ i + 1 = j then 3 else 2
  isSymm := by
    ext i j
    simp only [Matrix.transpose_apply, Matrix.of_apply]
    split_ifs <;> omega
  diagonal := by simp
  off_diagonal := by
    intro i j h
    simp only [Matrix.of_apply]
    split_ifs <;> simp_all

/-- The entries of the Coxeter matrix of type `A_∞`, unfolded. -/
theorem coxeterMatrixAInfty_apply (i j : ℕ) :
    coxeterMatrixAInfty i j = if i = j then 1 else if j + 1 = i ∨ i + 1 = j then 3 else 2 :=
  (rfl)

/-- Neighbouring indices of the Coxeter matrix of type `A_∞` carry the entry `3`. -/
theorem coxeterMatrixAInfty_eq_three {i j : ℕ} (h : i + 1 = j ∨ j + 1 = i) :
    coxeterMatrixAInfty i j = 3 := by
  rw [coxeterMatrixAInfty_apply]
  split_ifs <;> omega

/-- Indices of the Coxeter matrix of type `A_∞` at distance at least two carry the entry `2`. -/
theorem coxeterMatrixAInfty_eq_two {i j : ℕ} (h : i + 2 ≤ j ∨ j + 2 ≤ i) :
    coxeterMatrixAInfty i j = 2 := by
  rw [coxeterMatrixAInfty_apply]
  split_ifs <;> omega

/-- The type-`A` Coxeter matrix on `Fin m` is the restriction of the Coxeter matrix of type `A_∞`
to the first `m` indices. -/
theorem coxeterMatrixA_eq_coxeterMatrixAInfty (i j : Fin m) :
    CoxeterMatrix.A m i j = coxeterMatrixAInfty i j := by
  simp only [coxeterMatrixA_apply, coxeterMatrixAInfty_apply, Fin.ext_iff]

end TauCeti
