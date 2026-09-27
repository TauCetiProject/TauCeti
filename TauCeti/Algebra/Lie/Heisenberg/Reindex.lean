/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.Algebra.Basic
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Heisenberg Reindexing Lemma (integral form)

Key coefficient identity for the Chevalley commutator via Heisenberg conjugation,
in denominator-cleared integral form over a general commutative ring.

The reindexing transforms a sum over k with a `k * (k-1)!` coefficient into a sum
over j=k-1 with a `(j+1)!` coefficient, using `(j+1) * j! = (j+1)!`
(`Nat.factorial_succ`). This is the integral shadow of the field identity with
`k / k!` coefficients, where `(k+1) / (k+1)! = 1 / k!`; clearing denominators turns
the division into the multiplicative factorial relation, so no field or
characteristic-zero hypotheses are needed.

This is the technical core for the Heisenberg conjugation formula:
  exp(uX) * (vY) * exp(-uX) = vY + uv[X,Y]
which yields the Chevalley commutator [x_α(u), x_β(v)] = x_{α+β}(N(α,β)uv).
-/

public section

namespace TauCeti

open Finset

variable {R : Type*} [CommRing R]

variable {n : Type*} [DecidableEq n] [Fintype n]

/-- Integral Heisenberg reindexing: the sum over k with `k * (k-1)!` coefficient
    reindexes to a sum over j=k-1 with `(j+1)!` coefficient. The k=0 term vanishes. -/
theorem heisenberg_reindex
    (N : ℕ) (u : R) (X C : Matrix n n R) :
    ∑ k ∈ Finset.range (N + 1),
      (u ^ k * ((k * Nat.factorial (k - 1) : ℕ) : R)) • (C * X ^ (k - 1)) =
    ∑ j ∈ Finset.range N,
      ((u ^ (j + 1) * ((Nat.factorial (j + 1) : ℕ) : R)) • (C * X ^ j)) := by
  -- Peel off the k=0 term using sum_range_succ'
  rw [Finset.sum_range_succ']
  -- The k=0 term is zero
  have h0 : ((u ^ 0 * ((0 * Nat.factorial (0 - 1) : ℕ) : R)) • (C * X ^ (0 - 1))) = 0 := by
    simp
  rw [h0, add_zero]
  -- Now show the sums match termwise via (j+1) * j! = (j+1)!
  apply Finset.sum_congr rfl
  intro j hj
  -- For term j, we have k = j+1 in the LHS
  -- LHS scalar: u^(j+1) * ((j+1) * (j+1-1)!) ; RHS scalar: u^(j+1) * (j+1)!
  -- Need: (j+1) * j! = (j+1)!
  have h1 : (j + 1 - 1) = j := Nat.add_sub_cancel j 1
  have hcoeff : ((j + 1) * Nat.factorial j : ℕ) = Nat.factorial (j + 1) :=
    (Nat.factorial_succ j).symm
  rw [h1, hcoeff]

end TauCeti
