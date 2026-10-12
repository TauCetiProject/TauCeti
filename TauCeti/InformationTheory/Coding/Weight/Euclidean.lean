/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.ValMinAbs
public import Mathlib.InformationTheory.Hamming

/-!
# Euclidean weights of words over `ℤ/n`

The Euclidean weight of a residue `a` modulo `n` is the square of the distance from `a` to `0`
on the cycle `ℤ/n`, namely `min (a, n - a)²` for the representative `0 ≤ a < n`; in Mathlib's
terms it is the square of the absolute value of `ZMod.valMinAbs a`. The Euclidean weight of a
word is the sum of the Euclidean weights of its coordinates, that is, the squared Euclidean norm
of the word's least absolute integer lift.

Euclidean weights are the weights used for codes over `ℤ/2k` whose Construction A lattices are
even: the Type II condition over `ℤ/2^r` asks that all Euclidean weights be divisible by
`2^(r+1)`. Over `ℤ/2` the Euclidean weight is the Hamming weight.

## References

* S. T. Dougherty, T. A. Gulliver, and M. Harada, *Type II self-dual codes over finite rings
  and even unimodular lattices*, J. Algebraic Combin. **9** (1999), 233–250, §1.
-/

public section

namespace TauCeti

variable {ι : Type*} [Fintype ι] {n : ℕ}

/-- The Euclidean weight of a word over `ℤ/n`: the sum over the coordinates of the squares of
their least absolute integer representatives. -/
def euclideanWeight (x : ι → ZMod n) : ℕ :=
  ∑ i, (x i).valMinAbs.natAbs ^ 2

theorem euclideanWeight_def (x : ι → ZMod n) :
    euclideanWeight x = ∑ i, (x i).valMinAbs.natAbs ^ 2 := (rfl)

/-- The Euclidean weight of a word is the sum of the squares of the least absolute integer
representatives of its coordinates. -/
theorem natCast_euclideanWeight (x : ι → ZMod n) :
    (euclideanWeight x : ℤ) = ∑ i, (x i).valMinAbs ^ 2 := by
  simp [euclideanWeight_def]

/-- For a nonzero modulus, the Euclidean weight of a word is the sum over the coordinates of
`min (a, n - a)²`, where `0 ≤ a < n` is the canonical representative of the coordinate. -/
theorem euclideanWeight_eq_sum_min [NeZero n] (x : ι → ZMod n) :
    euclideanWeight x = ∑ i, min (x i).val (n - (x i).val) ^ 2 := by
  simp only [euclideanWeight_def, ZMod.valMinAbs_natAbs_eq_min]

/-- The zero word has Euclidean weight zero. -/
@[simp]
theorem euclideanWeight_zero : euclideanWeight (0 : ι → ZMod n) = 0 := by
  simp [euclideanWeight_def]

/-- Only the zero word has Euclidean weight zero. -/
@[simp]
theorem euclideanWeight_eq_zero {x : ι → ZMod n} : euclideanWeight x = 0 ↔ x = 0 := by
  simp [euclideanWeight_def, Finset.sum_eq_zero_iff, funext_iff]

/-- Negating a word does not change its Euclidean weight. -/
@[simp]
theorem euclideanWeight_neg (x : ι → ZMod n) : euclideanWeight (-x) = euclideanWeight x := by
  simp [euclideanWeight_def, ZMod.natAbs_valMinAbs_neg]

/-- Over `ℤ/2` the Euclidean weight of a word is its Hamming weight. -/
@[simp]
theorem euclideanWeight_eq_hammingNorm (x : ι → ZMod 2) : euclideanWeight x = hammingNorm x := by
  have h (a : ZMod 2) : a.valMinAbs.natAbs ^ 2 = if a ≠ 0 then 1 else 0 := by
    fin_cases a <;> decide
  simp only [euclideanWeight_def, h, Finset.sum_boole, hammingNorm, Nat.cast_id]

end TauCeti
