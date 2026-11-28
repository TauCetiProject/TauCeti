/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Elementary

/-!
# Orders of products of general linear groups

Extending matrices by the identity increases the order of a finite product of general linear
groups by an integer factor. Bounding the invertible matrices by all matrices gives an upper
bound in terms of the matrix size and the product of the coefficient cardinalities. These
bounds apply to the groups obtained by reduction at a family of primes.
-/

public section

open scoped BigOperators MatrixGroups

namespace Matrix

/-- The order of a product of general linear groups is bounded by the number of tuples of
underlying matrices. The coefficient semirings need not be fields. -/
theorem natCard_pi_GL_le {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]
    (R : ι → Type*) [∀ i, Semiring (R i)] [∀ i, Finite (R i)] :
    Nat.card (∀ i, GL n (R i)) ≤ (∏ i, Nat.card (R i)) ^ (Nat.card n ^ 2) := by
  classical
  let f (i : ι) (g : GL n (R i)) : Matrix n n (R i) := g.val
  have hf (i : ι) : Function.Injective (f i) := fun _ _ h ↦ Units.ext h
  calc
    _ ≤ Nat.card (∀ i, Matrix n n (R i)) := Nat.card_le_card_of_injective _ (.piMap hf)
    _ = _ := by simp only [Nat.card_pi, card_matrix, ← Finset.prod_pow, pow_two]

/-- The logarithm of the order of a product of general linear groups is bounded by the square
of the common matrix size times the logarithm of the product of the coefficient cardinalities. -/
theorem log_natCard_pi_GL_le {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]
    (R : ι → Type*) [∀ i, Semiring (R i)] [∀ i, Finite (R i)] :
    Real.log (Nat.card (∀ i, GL n (R i))) ≤
      (Nat.card n : ℝ) ^ 2 * Real.log (∏ i, (Nat.card (R i) : ℝ)) := by
  have h := Real.log_le_log (Nat.cast_pos.mpr (Nat.card_pos (α := ∀ i, GL n (R i))))
    (Nat.cast_le.mpr (natCard_pi_GL_le (n := n) R))
  simpa only [Nat.cast_pow, Nat.cast_prod, Real.log_pow] using h

end Matrix

namespace Function.Embedding

/-- Extending the matrix indices by the identity along `e` gives divisibility of the orders
of the corresponding products of general linear groups. -/
theorem natCard_pi_GL_dvd {ι n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (e : n ↪ m) (R : ι → Type*) [∀ i, Ring (R i)] :
    Nat.card (∀ i, GL n (R i)) ∣ Nat.card (∀ i, GL m (R i)) := by
  exact Subgroup.card_dvd_of_injective (MonoidHom.piMap fun i ↦ e.extendGL (R i))
    (.piMap fun i ↦ e.extendGL_injective (R i))

end Function.Embedding
