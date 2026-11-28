/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Riesz.Basic
public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.Remainder
import TauCeti.NumberTheory.DirichletCharacter.Quadratic.LegendreTwist

/-!
# Character expansion of the signed prime remainder

Character orthogonality writes the signed prime remainder in terms of first Riesz sums of
Dirichlet characters and their Legendre twists. The identity keeps the logarithmic correction
and the constants at `1` explicit; in particular it does not require the twists to be
nonprincipal. For a zero-exclusion argument, this separates the contribution of the untwisted
L-functions from the contribution with the opposite sign before taking a transform.

The normalization follows `New.lambdaKResidueClass`, `New.logDerivMean` and
`New.integral_primeRemainder` in `grh/src/New/Reduction/Zeros/PrimeError.lean` of
[lsernau/grh-lean](https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207/grh).
-/

public section

open ArithmeticFunction Complex Finset

namespace TauCeti.OneSidedBound

/-- The signed progression weight times the totient is the sum of the differences between
the untwisted and Legendre-twisted von Mangoldt coefficients. -/
theorem totient_mul_primeWeight_eq_sum (d q : ℕ) [Fact d.Prime] [NeZero q] (n : ℕ) :
    (q.totient : ℂ) * (primeWeight d q n : ℂ) =
      ∑ ψ : DirichletCharacter ℂ q, (ψ n - quadraticTwist d ψ n) * (Λ n : ℂ) := by
  have : NeZero (q * d) := ⟨Nat.mul_ne_zero (NeZero.ne q) (Fact.out : d.Prime).ne_zero⟩
  have ht (ψ : DirichletCharacter ℂ q) : quadraticTwist d ψ n = ψ n * legendreSym d n := by
    have he : quadraticTwist d ψ = ψ.legendreTwist d := by
      apply MulChar.ext
      intro a
      rw [quadraticTwist_apply]
      symm
      simpa [legendreSym] using ψ.legendreTwist_apply_natCast d (a : ZMod (q * d)).val
    rw [he, ψ.legendreTwist_apply_natCast]
  simp only [ht, ← mul_one_sub, mul_assoc, ← sum_mul, DirichletCharacter.sum_characters_eq]
  by_cases hn : (n : ZMod q) = 1 <;> simp [primeWeight_def, hn, NeZero.ne q]
  ring

/-- The signed prime remainder multiplied by the cutoff and the totient is the real part of
an untwisted-minus-twisted Riesz sum with its logarithmic and linear corrections. The linear
correction uses the pole-removed `L`-functions at `1`, including for principal twists. -/
theorem mul_primeRemainder_eq_re_signed_riesz_sum (d q : ℕ) [Fact d.Prime] [NeZero q]
    (y : ℝ) :
    letI : NeZero (q * d) := ⟨Nat.mul_ne_zero (NeZero.ne q) (Fact.out : d.Prime).ne_zero⟩
    (q.totient : ℝ) * (y * primeRemainder d q y) =
      ((∑ ψ : DirichletCharacter ℂ q,
        (rieszSum (fun n ↦ ψ n * (Λ n : ℂ)) y -
          rieszSum (fun n ↦ quadraticTwist d ψ n * (Λ n : ℂ)) y +
          (y : ℂ) * (logDeriv ψ.entireLFunction 1 -
            logDeriv (quadraticTwist d ψ).entireLFunction 1))) -
        (y : ℂ) * ((Real.log y : ℂ) - 1)).re := by
  classical
  have hprime : (q.totient : ℂ) * rieszSum (fun n ↦ (primeWeight d q n : ℂ)) y =
      ∑ ψ : DirichletCharacter ℂ q,
        (rieszSum (fun n ↦ ψ n * (Λ n : ℂ)) y -
          rieszSum (fun n ↦ quadraticTwist d ψ n * (Λ n : ℂ)) y) := by
    simp only [rieszSum_def, mul_sum, sum_sub_distrib]
    rw [← sum_comm (s := Finset.Icc 1 ⌊y⌋₊), ← sum_comm (s := Finset.Icc 1 ⌊y⌋₊),
      ← sum_sub_distrib]
    refine sum_congr rfl fun n _ ↦ ?_
    rw [← mul_assoc, totient_mul_primeWeight_eq_sum, sum_mul, ← sum_sub_distrib]
    exact sum_congr rfl fun ψ _ ↦ by ring
  have hscale : (rieszSum (fun n ↦ (primeWeight d q n : ℂ)) y).re =
      y * ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, primeWeight d q n * (1 / (n : ℝ) - 1 / y) := by
    by_cases hy : y = 0
    · simp [hy, rieszSum_eq_zero_of_le_one]
    rw [rieszSum_def, re_sum, mul_sum]
    refine sum_congr rfl fun n _ ↦ ?_
    rw [← ofReal_natCast, ← ofReal_div, ← ofReal_one, ← ofReal_sub, ← ofReal_mul, ofReal_re]
    field_simp
  have hR := congrArg Complex.re hprime
  simp only [← ofReal_natCast, re_ofReal_mul, hscale] at hR
  have hφ : (q.totient : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  rw [sum_add_distrib, ← mul_sum, primeRemainder_def, logDerivMean_def]
  simp only [← ofReal_natCast, Complex.div_ofReal_re, sub_re, add_re, re_ofReal_mul, one_re,
    ofReal_re]
  rw [← hR]
  simp only [sum_sub_distrib, sub_re]
  field_simp
  ring

end TauCeti.OneSidedBound
