/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arend Mellendijk, The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.SelbergSieve
public import TauCeti.NumberTheory.SelbergSieve.LambdaSquared
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

import TauCeti.Algebra.Order.Floor.Ring

/-!
# Selberg's optimal weights and upper bound

For a bounding sieve and a real cutoff `z`, the diagonal mass `G(z)` sums `selbergTerms` over the
divisors of the sieving product strictly below `z`, and the optimal weights `λ_z` are the
normalized upper-divisor sums over the same range. Since a natural number lies strictly below `z`
exactly when it is at most `⌈z⌉₊ - 1`, both agree with the inclusive-cutoff normalizer and weights
at that parameter, and inherit their laws.

## Main results

* `BoundingSieve.optimalSelbergWeights_one`: for `1 < z`, `λ_z(1) = 1`.
* `BoundingSieve.abs_optimalSelbergWeights_le_one`: `|λ_z(d)| ≤ 1`.
* `BoundingSieve.mainSum_lambdaSquared_optimalSelbergWeights`: the quadratic main term of `λ_z`
  is `1 / G(z)`, and `BoundingSieve.inv_diagonalMass_le_mainSum_lambdaSquared` bounds the main
  term of every weight normalized at one and supported strictly below `z` from below by `1 / G(z)`.
  For `1 < z` the optimal weights are such a weight, so `1 / G(z)` is the minimum.
* `BoundingSieve.siftedSum_le_totalMass_div_diagonalMass_add_sum_three_pow`: Selberg's upper
  bound `S ≤ X / G(z) + ∑_{d ∣ P, d < z²} 3^ω(d) |r_d|` for `1 < z`.

## References

* D. R. Heath-Brown, *Lectures on sieves*, §2, Lemma 2.1 and the fundamental theorem for
  Selberg's sieve.
* Adapted from Arend Mellendijk's PNT+ Selberg sieve, `selberg_bound_weights` and
  `selberg_bound_simple`:
  Repository: https://github.com/TauCetiProject/PrimeNumberTheoremAnd
  Revision: 0a81f5b37491b82a9a1a6b75369f428d9aa1a85f
  File: PrimeNumberTheoremAnd/Mathlib/NumberTheory/Sieve/Selberg.lean
-/

public noncomputable section

open Finset Nat ArithmeticFunction TauCeti
open scoped ArithmeticFunction.Moebius ArithmeticFunction.omega

namespace BoundingSieve

/-- The Selberg diagonal mass: the sum of `selbergTerms` over divisors of the sieving product
strictly below the cutoff. -/
def diagonalMass (s : BoundingSieve) (z : ℝ) : ℝ :=
  ∑ d ∈ s.prodPrimes.divisors.filter (fun d : ℕ ↦ (d : ℝ) < z), s.selbergTerms d

/-- The defining strict-cutoff sum for the Selberg diagonal mass. -/
theorem diagonalMass_def (s : BoundingSieve) (z : ℝ) :
    s.diagonalMass z =
      ∑ d ∈ s.prodPrimes.divisors.filter (fun d : ℕ ↦ (d : ℝ) < z), s.selbergTerms d := by
  rfl

/-- The strict diagonal mass is the inclusive truncated normalizer at `⌈z⌉₊ - 1`. -/
theorem diagonalMass_eq_truncatedSelbergSum (s : BoundingSieve) (z : ℝ) :
    s.diagonalMass z = s.truncatedSelbergSum (⌈z⌉₊ - 1) := by
  simp_rw [diagonalMass, truncatedSelbergSum_def, sum_filter, Nat.cast_lt_iff_le_ceil_sub_one]

/-- The diagonal mass is positive once the cutoff exceeds one. -/
theorem diagonalMass_pos (s : BoundingSieve) {z : ℝ} (hz : 1 < z) : 0 < s.diagonalMass z := by
  rw [diagonalMass_eq_truncatedSelbergSum]
  exact s.truncatedSelbergSum_pos <| by
    simpa using (Nat.cast_lt_iff_le_ceil_sub_one 1).mp (by simpa using hz)

/-- Selberg's optimal weights `λ_z`, the normalized upper-divisor sums of `selbergTerms` over
divisors of the sieving product strictly below the cutoff. -/
def optimalSelbergWeights (s : BoundingSieve) (z : ℝ) (d : ℕ) : ℝ :=
  if d ∣ s.prodPrimes then
    (s.nu d)⁻¹ * (μ d : ℝ) * (s.diagonalMass z)⁻¹ *
      ∑ l ∈ s.prodPrimes.divisors.filter (fun l : ℕ ↦ d ∣ l ∧ (l : ℝ) < z), s.selbergTerms l
  else 0

/-- The defining upper-divisor formula for Selberg's optimal weights. -/
theorem optimalSelbergWeights_def (s : BoundingSieve) (z : ℝ) (d : ℕ) :
    s.optimalSelbergWeights z d =
      if d ∣ s.prodPrimes then
        (s.nu d)⁻¹ * (μ d : ℝ) * (s.diagonalMass z)⁻¹ *
          ∑ l ∈ s.prodPrimes.divisors.filter (fun l : ℕ ↦ d ∣ l ∧ (l : ℝ) < z),
            s.selbergTerms l
      else 0 := by
  rfl

/-- The strict-cutoff weights are the inclusive-cutoff weights at `⌈z⌉₊ - 1`. -/
theorem optimalSelbergWeights_eq_selbergWeights (s : BoundingSieve) (z : ℝ) :
    s.optimalSelbergWeights z = s.selbergWeights (⌈z⌉₊ - 1) := by
  funext d
  simp_rw [optimalSelbergWeights, selbergWeights_def, diagonalMass_eq_truncatedSelbergSum,
    sum_filter, Nat.cast_lt_iff_le_ceil_sub_one]

/-- The optimal weights are normalized at one once the cutoff exceeds one. -/
@[simp] theorem optimalSelbergWeights_one (s : BoundingSieve) {z : ℝ} (hz : 1 < z) :
    s.optimalSelbergWeights z 1 = 1 := by
  rw [optimalSelbergWeights_eq_selbergWeights]
  exact s.selbergWeights_one <| by
    simpa using (Nat.cast_lt_iff_le_ceil_sub_one 1).mp (by simpa using hz)

/-- An optimal weight vanishes off the divisors of the sieving product. -/
@[simp] theorem optimalSelbergWeights_eq_zero_of_not_dvd (s : BoundingSieve) (z : ℝ) {d : ℕ}
    (hd : ¬d ∣ s.prodPrimes) : s.optimalSelbergWeights z d = 0 := by
  simp [optimalSelbergWeights, hd]

/-- An optimal weight vanishes at indices at or above the cutoff. -/
@[simp] theorem optimalSelbergWeights_eq_zero_of_le (s : BoundingSieve) {z : ℝ} {d : ℕ}
    (hd : z ≤ (d : ℝ)) : s.optimalSelbergWeights z d = 0 := by
  rw [optimalSelbergWeights_eq_selbergWeights]
  exact s.selbergWeights_eq_zero_of_lt _ d
    (lt_of_not_ge ((Nat.cast_lt_iff_le_ceil_sub_one d).not.mp (not_lt_of_ge hd)))

/-- Every optimal weight has absolute value at most one, at every real cutoff. -/
theorem abs_optimalSelbergWeights_le_one (s : BoundingSieve) (z : ℝ) (d : ℕ) :
    |s.optimalSelbergWeights z d| ≤ 1 := by
  rw [optimalSelbergWeights_eq_selbergWeights]
  exact s.abs_selbergWeights_le_one _ d

/-- The quadratic main term of the optimal weights is the reciprocal diagonal mass. -/
theorem mainSum_lambdaSquared_optimalSelbergWeights (s : BoundingSieve) (z : ℝ) :
    s.mainSum (lambdaSquared (s.optimalSelbergWeights z)) = (s.diagonalMass z)⁻¹ := by
  rw [optimalSelbergWeights_eq_selbergWeights, mainSum_lambdaSquared_selbergWeights,
    diagonalMass_eq_truncatedSelbergSum]

/-- Selberg's optimality: every weight normalized at one and vanishing on divisors of the
sieving product at or above `z` has quadratic main term at least the reciprocal diagonal mass. -/
theorem inv_diagonalMass_le_mainSum_lambdaSquared (s : BoundingSieve) {z : ℝ} (w : ℕ → ℝ)
    (hw : w 1 = 1) (hsupp : ∀ d ∈ s.prodPrimes.divisors, z ≤ (d : ℝ) → w d = 0) :
    (s.diagonalMass z)⁻¹ ≤ s.mainSum (lambdaSquared w) := by
  rw [diagonalMass_eq_truncatedSelbergSum]
  exact s.inv_truncatedSelbergSum_le_mainSum_lambdaSquared w hw fun d hd hdz ↦
    hsupp d hd (le_of_not_gt fun h ↦ not_le_of_gt hdz ((Nat.cast_lt_iff_le_ceil_sub_one d).mp h))

/-- Selberg's upper bound with its exact squared-weight remainder, for `1 < z`. -/
theorem siftedSum_le_totalMass_div_diagonalMass_add_errSum (s : BoundingSieve) {z : ℝ}
    (hz : 1 < z) :
    s.siftedSum ≤ s.totalMass / s.diagonalMass z +
      s.errSum (lambdaSquared (s.optimalSelbergWeights z)) := by
  simpa only [s.mainSum_lambdaSquared_optimalSelbergWeights, div_eq_mul_inv] using
    s.siftedSum_le_mainSum_errSum_of_upperMoebius _
      (upperMoebius_lambdaSquared _ (s.optimalSelbergWeights_one hz))

/-- **Selberg's upper-bound sieve**: for `1 < z`,
`S ≤ X / G(z) + ∑_{d ∣ P, d < z²} 3^ω(d) |r_d|`. -/
theorem siftedSum_le_totalMass_div_diagonalMass_add_sum_three_pow (s : BoundingSieve) {z : ℝ}
    (hz : 1 < z) :
    s.siftedSum ≤ s.totalMass / s.diagonalMass z +
      ∑ d ∈ s.prodPrimes.divisors.filter (fun d : ℕ ↦ (d : ℝ) < z ^ 2),
        (3 : ℝ) ^ ω d * |s.rem d| := by
  refine (s.siftedSum_le_totalMass_div_diagonalMass_add_errSum hz).trans ?_
  rw [sum_filter]
  gcongr
  exact s.errSum_lambdaSquared_le_sum_three_pow_cardDistinctFactors_lt _ z
    (fun d _ ↦ s.abs_optimalSelbergWeights_le_one z d)
    fun d _ hd ↦ s.optimalSelbergWeights_eq_zero_of_le hd

end BoundingSieve
