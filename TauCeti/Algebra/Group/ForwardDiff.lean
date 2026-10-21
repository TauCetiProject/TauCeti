/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.ForwardDiff

/-!
# Alternating forward differences

For functions from an additive commutative monoid to an additive commutative group, multiplying
the `n`-th forward difference by the integer `(-1) ^ n` gives the alternating difference. These
identities describe its successor step and its alternating binomial expansion, using Mathlib's
forward-difference operator and integer scalar multiplication. For ring-valued functions, the same
identities are stated using multiplication by the coefficients in the ring.

## Main declarations

* `TauCeti.neg_one_pow_smul_fwdDiff_iter_succ`: a negative forward difference advances the
  alternating iterate by one step.
* `TauCeti.neg_one_pow_smul_fwdDiff_iter_eq_alternating_sum`: the alternating iterate as a
  binomial sum of translates.
* `TauCeti.neg_one_pow_mul_fwdDiff_iter_succ` and
  `TauCeti.neg_one_pow_mul_fwdDiff_iter_eq_alternating_sum`: the ring-valued forms.
* `TauCeti.sum_neg_one_pow_mul_choose_succ`: the successor step for alternating binomial sums.
-/

public section

open scoped fwdDiff

namespace TauCeti

variable {M G : Type*} [AddCommMonoid M] [AddCommGroup G]

/-- Differencing once advances the alternating iterated forward difference by one step. -/
theorem neg_one_pow_smul_fwdDiff_iter_succ (n : ℕ) (F : M → G) (s : M) :
    (-1 : ℤ) ^ n • Δ_[s]^[n] (-Δ_[s] F)
      = (-1 : ℤ) ^ (n + 1) • Δ_[s]^[n + 1] F := by
  rw [Function.iterate_succ_apply, ← neg_one_zsmul (Δ_[s] F),
    fwdDiff_iter_const_smul, smul_smul, pow_succ]

/-- The alternating iterated forward difference as an explicit alternating binomial sum. -/
theorem neg_one_pow_smul_fwdDiff_iter_eq_alternating_sum (n : ℕ) (F : M → G) (s x : M) :
    (-1 : ℤ) ^ n • Δ_[s]^[n] F x
      = ∑ k ∈ Finset.range (n + 1), ((-1 : ℤ) ^ k * n.choose k) • F (x + k • s) := by
  rw [fwdDiff_iter_eq_sum_shift, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hexp : n + (n - k) = 2 * (n - k) + k := by omega
  have hsign : (-1 : ℤ) ^ n * (-1 : ℤ) ^ (n - k) = (-1 : ℤ) ^ k := by
    rw [← pow_add, hexp, pow_add, pow_mul]
    simp
  rw [smul_smul, ← mul_assoc, hsign]

variable {R : Type*} [Ring R]

/-- Differencing once advances the alternating iterated forward difference of a ring-valued
function by one step. -/
theorem neg_one_pow_mul_fwdDiff_iter_succ (n : ℕ) (F : M → R) (s : M) :
    (fun x : M => (-1 : R) ^ n * Δ_[s]^[n] (-Δ_[s] F) x)
      = fun x : M => (-1 : R) ^ (n + 1) * Δ_[s]^[n + 1] F x := by
  funext x
  have h := congrFun (neg_one_pow_smul_fwdDiff_iter_succ n F s) x
  simp only [Pi.smul_apply, zsmul_eq_mul] at h
  push_cast at h
  exact h

/-- The alternating iterated forward difference of a ring-valued function as an explicit
alternating binomial sum. -/
theorem neg_one_pow_mul_fwdDiff_iter_eq_alternating_sum (n : ℕ) (F : M → R) (s x : M) :
    (-1 : R) ^ n * Δ_[s]^[n] F x
      = ∑ k ∈ Finset.range (n + 1), (-1 : R) ^ k * n.choose k * F (x + k • s) := by
  have h := neg_one_pow_smul_fwdDiff_iter_eq_alternating_sum n F s x
  simp only [zsmul_eq_mul] at h
  push_cast at h
  exact h

/-- An alternating binomial sum of successor order is the alternating binomial sum of the
negative forward differences of consecutive values. -/
theorem sum_neg_one_pow_mul_choose_succ (n : ℕ) (f : ℕ → R) :
    (∑ k ∈ Finset.range (n + 2), (-1 : R) ^ k * (n + 1).choose k * f k) =
      ∑ k ∈ Finset.range (n + 1), (-1 : R) ^ k * n.choose k * (f k - f (k + 1)) := by
  have h := congrFun (neg_one_pow_mul_fwdDiff_iter_succ n f 1) 0
  simpa only [neg_one_pow_mul_fwdDiff_iter_eq_alternating_sum,
    smul_eq_mul, mul_one, zero_add, Pi.neg_apply, fwdDiff, neg_sub] using h.symm

end TauCeti
