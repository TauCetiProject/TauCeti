/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Basic determinant formulas

Additions to Mathlib's `Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean`.

Mathlib computes the determinant of a matrix indexed by a singleton type (`Matrix.det_unique`)
and of a `Fin 2`-indexed matrix (`Matrix.det_fin_two`). A two-by-two matrix also arises indexed
by `m ⊕ n` with `m` and `n` singletons, for instance as `fromBlocks` of four `1 × 1` blocks or on
the `l ⊕ l` index of the standard symplectic form `Matrix.J l R`. `Matrix.det_sum_unique` gives
its determinant in coordinates, so that such a matrix need not be reindexed along `Fin 2` by hand.

## Main results

* `Matrix.det_sum_unique`: the determinant of a matrix on `m ⊕ n`, for singletons `m` and `n`.
-/

public section

namespace Matrix

variable {m n R : Type*} [Unique m] [Unique n] [DecidableEq m] [DecidableEq n] [Fintype m]
  [Fintype n] [CommRing R]

/-- The determinant of a matrix indexed by `m ⊕ n`, for singleton types `m` and `n`, is the
two-by-two determinant of its entries. -/
theorem det_sum_unique (A : Matrix (m ⊕ n) (m ⊕ n) R) :
    A.det = A (Sum.inl default) (Sum.inl default) * A (Sum.inr default) (Sum.inr default)
      - A (Sum.inl default) (Sum.inr default) * A (Sum.inr default) (Sum.inl default) := by
  -- Reindex along `Fin 2 ≃ m ⊕ n`. It sends `0` to `Sum.inl default` and `1` to `Sum.inr default`
  -- by definition, so `det_fin_two` is the claim up to `rfl`; `simp` cannot see through the
  -- numerals `0, 1 : Fin 2` to evaluate `finSumFinEquiv.symm` on them.
  rw [← det_submatrix_equiv_self (finSumFinEquiv.symm.trans <|
    (Equiv.ofUnique (Fin 1) m).sumCongr (Equiv.ofUnique (Fin 1) n)) A, det_fin_two]
  rfl

end Matrix
