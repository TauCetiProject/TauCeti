/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Heisenberg Reindexing Lemma

Key coefficient identity for the Chevalley commutator via Heisenberg conjugation.
The reindexing transforms a sum over k with a k/(k!) coefficient into a sum
over j=k-1 with a 1/(j!) coefficient, using (j+1)/(j+1)! = 1/j!.

This is the technical core for the Heisenberg conjugation formula:
  exp(uX) * (vY) * exp(-uX) = vY + uv[X,Y]
which yields the Chevalley commutator [x_α(u), x_β(v)] = x_{α+β}(N(α,β)uv).
-/

open Finset

/-- Factorial successor in R: ((k+1)! : R) = (k+1) * (k! : R). -/
theorem factorial_succ_cast {R : Type*} [Semiring R] (k : ℕ) :
    ((Nat.factorial (k + 1) : ℕ) : R) = ((k + 1 : ℕ) : R) * ((Nat.factorial k : ℕ) : R) := by
  rw [Nat.factorial_succ]
  push_cast
  ring

variable {R : Type*} [Field R] [CharZero R]

/-- (k+1 : R) is nonzero. -/
theorem succ_cast_ne_zero (k : ℕ) : ((k + 1 : ℕ) : R) ≠ 0 := by
  exact Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)

/-- (k! : R) is nonzero. -/
theorem factorial_cast_ne_zero (k : ℕ) : ((Nat.factorial k : ℕ) : R) ≠ 0 := by
  exact Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)

/-- The key coefficient identity: (k+1)/(k+1)! = 1/k!. -/
theorem coeff_identity (k : ℕ) :
    ((k + 1 : ℕ) : R) / ((Nat.factorial (k + 1) : ℕ) : R) =
    1 / ((Nat.factorial k : ℕ) : R) := by
  rw [factorial_succ_cast k]
  rw [div_mul_eq_div_div]
  rw [div_self (succ_cast_ne_zero k)]

variable {n : Type*} [DecidableEq n] [Fintype n]

/-- Heisenberg reindexing: the sum over k with k/(k!) coefficient reindexes to
    a sum over j=k-1 with 1/(j!) coefficient. The k=0 term vanishes. -/
theorem heisenberg_reindex
    (N : ℕ) (u : R) (X C : Matrix n n R) :
    ∑ k ∈ Finset.range (N + 1),
      ((u ^ k * ((k : ℕ) : R) / ((Nat.factorial k : ℕ) : R)) • (C * X ^ (k - 1))) =
    ∑ j ∈ Finset.range N,
      ((u ^ (j + 1) / ((Nat.factorial j : ℕ) : R)) • (C * X ^ j)) := by
  -- Peel off the k=0 term using sum_range_succ'
  rw [Finset.sum_range_succ']
  -- The k=0 term is zero
  have h0 : ((u ^ 0 * ((0 : ℕ) : R) / ((Nat.factorial 0 : ℕ) : R)) • (C * X ^ (0 - 1))) = 0 := by
    simp
  rw [h0, add_zero]
  -- Now show the sums match termwise via the coefficient identity
  apply Finset.sum_congr rfl
  intro j hj
  -- For term j, we have k = j+1 in the LHS
  -- LHS term: (u^(j+1) * (j+1) / (j+1)!) • (C * X^j)
  -- RHS term: (u^(j+1) / j!) • (C * X^j)
  -- Need: (j+1)/(j+1)! = 1/j!
  have hcoeff : ((j + 1 : ℕ) : R) / ((Nat.factorial (j + 1) : ℕ) : R) =
      1 / ((Nat.factorial j : ℕ) : R) := coeff_identity j
  -- Simplify the LHS term
  have h1 : (j + 1 - 1) = j := Nat.add_sub_cancel j 1
  rw [h1]
  -- Rewrite using the coefficient identity: (j+1)/(j+1)! = 1/j!
  -- So u^(j+1) * (j+1)/(j+1)! = u^(j+1) / j!
  have heq : (u ^ (j + 1) * ((j + 1 : ℕ) : R) / ((Nat.factorial (j + 1) : ℕ) : R))
      = (u ^ (j + 1) / ((Nat.factorial j : ℕ) : R)) := by
    rw [mul_div_assoc]
    rw [hcoeff]
    rw [mul_one_div]
  rw [heq]
