/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Polynomial.RogersRamanujan

/-!
# Examples of Schur's polynomial identities

At `n = 2` the two identities read `1 + t` and `1 + t²`, and at `n = 4` the first reads
`1 + t + t² + t³ + t⁴`. The integer lower index of `TauCeti.gaussianBinomialInt` must not be
truncated: `[0 -1]_t = 0`, while the truncated index `(-1).toNat = 0` would give `[0 0]_t = 1`.
-/

public section

open TauCeti

example (t : ℤ) : schurAlternatingSum t 2 = 1 + t := by
  rw [← rogersRamanujanSum_eq_schurAlternatingSum, rogersRamanujanSum_add_two]
  simp

example (t : ℤ) : schurAlternatingSumTwo t 2 = 1 + t ^ 2 := by
  rw [← rogersRamanujanSumTwo_eq_schurAlternatingSumTwo, rogersRamanujanSumTwo_add_two]
  simp

example (t : ℤ) : rogersRamanujanSum t 4 = 1 + t + t ^ 2 + t ^ 3 + t ^ 4 := by
  rw [rogersRamanujanSum_add_two, rogersRamanujanSum_add_two (n := 1),
    rogersRamanujanSum_add_two (n := 0)]
  simp
  ring

example (t : ℤ) :
    gaussianBinomialInt t 0 (-1) = 0 ∧ gaussianBinomialInt t 0 0 = 1 ∧
      gaussianBinomialInt t 0 1 = 0 := by
  refine ⟨gaussianBinomialInt_of_neg t 0 (by norm_num), by simp,
    gaussianBinomialInt_eq_zero_of_lt t (by norm_num)⟩

/-- Truncating the lower index `-1` to `0` would give `1`. -/
example (t : ℤ) : gaussianBinomial t 0 (-1 : ℤ).toNat = 1 := by
  simp
