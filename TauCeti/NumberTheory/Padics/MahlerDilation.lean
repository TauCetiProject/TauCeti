/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.MahlerBasis
public import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Order

/-!
# Mahler functions of a dilation

For `m : ℕ`, the function `x ↦ (m x choose n)` on `ℤ_p` is an integral combination of the Mahler
basis functions `x ↦ (x choose k)`, `k ≤ n`. The coefficients are those of the power series
`((1 + T) ^ m - 1) ^ k` at `T ^ n`: this is the coefficientwise form of
`(1 + T) ^ (m x) = ((1 + T) ^ m) ^ x = ∑_k (x choose k) ((1 + T) ^ m - 1) ^ k`.

## Main results

* `PadicInt.mahler_natCast_mul`: the Mahler function `(m x choose n)` is the integral combination
  of the `(x choose k)`, `k ≤ n`, with coefficients those of `((1 + T) ^ m - 1) ^ k` at `T ^ n`.
-/

public section

open PowerSeries

variable {p : ℕ} [Fact p.Prime]

namespace PadicInt

/-- **Mahler functions of a dilation.** For `m : ℕ`, the function `x ↦ (m x choose n)` is the
integral combination `∑_{k ≤ n} c_{n,k} (x choose k)`, where `c_{n,k}` is the coefficient of `T ^ n`
in `((1 + T) ^ m - 1) ^ k`. This is the coefficientwise form of
`(1 + T) ^ (m x) = ((1 + T) ^ m) ^ x = ∑_k (x choose k) ((1 + T) ^ m - 1) ^ k`. -/
theorem mahler_natCast_mul (m n : ℕ) (x : ℤ_[p]) :
    mahler n ((m : ℤ_[p]) * x) = ∑ k ∈ Finset.range (n + 1),
      ((coeff n (((1 + X) ^ m - 1) ^ k : ℤ⟦X⟧) : ℤ) : ℤ_[p]) * mahler k x := by
  set G : ℤ⟦X⟧ := (1 + X) ^ m - 1
  have hG : constantCoeff G = 0 := by simp [G]
  -- Both sides are continuous in `x`, so it suffices to compare them on `ℕ`.
  have hcont : Continuous fun x : ℤ_[p] ↦ mahler n ((m : ℤ_[p]) * x) :=
    (mahler n).continuous.comp (continuous_const.mul continuous_id)
  refine congrFun (denseRange_natCast.equalizer hcont
    (continuous_finsetSum _ fun k _ ↦ continuous_const.mul (mahler k).continuous)
    (funext fun l ↦ ?_)) x
  simp only [Function.comp_apply, ← Nat.cast_mul, Pi.mul_apply, mahler_natCast_eq]
  -- For natural `l`, expand `(1 + T) ^ (m l) = (G + 1) ^ l` by the binomial theorem.
  have hnat :
      ((m * l).choose n : ℤ) = ∑ k ∈ Finset.range (l + 1), coeff n (G ^ k) * l.choose k := by
    have hpow : ((1 + X : ℤ⟦X⟧) ^ (m * l)) = (G + 1) ^ l := by
      rw [pow_mul, sub_add_cancel]
    have hcoeff := congrArg (coeff n) hpow
    rw [← binomialSeries_nat (R := ℤ), binomialSeries_coeff, Ring.choose_natCast, add_pow,
      map_sum] at hcoeff
    simpa using hcoeff
  -- Both finite sums agree with the sum over `k ≤ n + l`.
  have hsub₁ : ∑ k ∈ Finset.range (l + 1), coeff n (G ^ k) * (l.choose k : ℤ) =
      ∑ k ∈ Finset.range (n + l + 1), coeff n (G ^ k) * (l.choose k : ℤ) :=
    Finset.sum_subset (Finset.range_subset_range.mpr (by lia)) fun k _ hk ↦ by
      rw [Nat.choose_eq_zero_of_lt (by simpa using hk), Nat.cast_zero, mul_zero]
  have hsub₂ : ∑ k ∈ Finset.range (n + 1), coeff n (G ^ k) * (l.choose k : ℤ) =
      ∑ k ∈ Finset.range (n + l + 1), coeff n (G ^ k) * (l.choose k : ℤ) :=
    Finset.sum_subset (Finset.range_subset_range.mpr (by lia)) fun k _ hk ↦ by
      rw [coeff_of_lt_order _ ((Nat.cast_lt.mpr (by simpa using hk)).trans_le
        (le_order_pow_of_constantCoeff_eq_zero k hG)), zero_mul]
  have hint : ((m * l).choose n : ℤ) =
      ∑ k ∈ Finset.range (n + 1), coeff n (G ^ k) * (l.choose k : ℤ) := by
    rw [hnat, hsub₁, hsub₂]
  exact_mod_cast congrArg (Int.cast : ℤ → ℤ_[p]) hint

end PadicInt
