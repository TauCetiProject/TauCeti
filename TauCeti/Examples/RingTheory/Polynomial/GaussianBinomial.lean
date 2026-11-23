/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Basic
public import TauCeti.LinearAlgebra.Submodule.CardFinrank
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.LinearCombination

/-!
# Examples of Gaussian binomial coefficients

Small values computed from the successor recursion: `[2 1] = 1 + t`, `[4 2]_2 = 35`, and
`[3 1]_2 = 7`, which differs from the binomial coefficient `3`, while `[5 2]_1 = 10` recovers
`Nat.choose 5 2`. Over `ℕ`, `[2 1]_2 = 3` counts the lines of `𝔽₂²`, as the subspace count
`TauCeti.card_submodule_finrank_eq_gaussianBinomial` confirms by evaluating at the integer `2`.

The symmetry `[n n-k]_t = [n k]_t` needs `k ≤ n`: for `k > n` the coefficient `[n k]_t` vanishes,
while the truncated index `n - k = 0` gives `[n 0]_t = 1`. Cauchy's `q`-binomial theorem for
`n = 2` is `(1 + z)(1 + t z) = 1 + (1 + t) z + t z²`.
-/

public section

open Module Polynomial TauCeti

example : gaussianPoly 2 1 = 1 + X := by
  simp [gaussianPoly_succ_succ]

example : gaussianBinomial (2 : ℕ) 4 2 = 35 := by
  simp [gaussianBinomial_succ_succ]

example : gaussianBinomial (2 : ℕ) 3 1 = 7 := by
  simp [gaussianBinomial_succ_succ]

example : gaussianBinomial (1 : ℚ) 5 2 = 10 := by
  simp [Nat.choose]

example : gaussianBinomial (2 : ℕ) 2 1 = 3 := by
  simp [gaussianBinomial_succ_succ]

/-- The range hypothesis of `TauCeti.gaussianBinomial_symm` cannot be dropped. -/
example (t : ℤ) : gaussianBinomial t 2 3 = 0 ∧ gaussianBinomial t 2 (2 - 3) = 1 := by
  simp

example (t z : ℤ) : (1 + z) * (1 + t * z) = 1 + (1 + t) * z + t * z ^ 2 := by
  have h := prod_one_add_pow_mul_eq_sum_gaussianBinomial t z 2
  simp [Finset.prod_range_succ, Finset.sum_range_succ, gaussianBinomial_succ_succ] at h
  linear_combination h

example : Nat.card {W : Submodule (ZMod 2) (Fin 2 → ZMod 2) // finrank (ZMod 2) W = 1} = 3 := by
  rw [card_submodule_finrank_eq_gaussianBinomial]
  simp [gaussianBinomial_succ_succ]
