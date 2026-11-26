/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Chebyshev.FinitePrimeSums
public import TauCeti.NumberTheory.Padics.PadicNorm

/-!
# Rational normalisation by local divisibility gains

A rational scalar can remove the guaranteed prime powers from an integral lift.
At each prime, round the net gain down before taking the reciprocal power. The
scalar then has precisely the required local norm. At the real place, rounding
costs at most one `log p` per prime; at small primes the total cost is bounded by
Chebyshev's theta function.

The normalisation and the rounding budget follow the statements `New.Data.norm_invGainFactor`,
`New.Data.sum_log_smallNonsplitPrimes_union_le` and `New.Data.log_invGainFactor_le` in
`grh/src/New/Reduction/ShortAndEnough.lean` of lsernau/grh-lean (`72fead1`).
-/

public section

namespace TauCeti

/-- The positive rational normalising factor for real divisibility gains and losses at a finite
set of primes. The exponent at `p` is the negative of the floor of `gain p - loss p`. -/
noncomputable def inverseGainFactor (S : Finset Nat.Primes) (gain loss : Nat.Primes → ℝ) : ℚ :=
  ∏ p ∈ S, (p.val : ℚ) ^ (-⌊gain p - loss p⌋)

/-- The inverse gain factor is a product of reciprocal prime powers. -/
theorem inverseGainFactor_def (S : Finset Nat.Primes) (gain loss : Nat.Primes → ℝ) :
    inverseGainFactor S gain loss = ∏ p ∈ S, (p.val : ℚ) ^ (-⌊gain p - loss p⌋) := (rfl)

/-- Removing no gains gives the factor `1`. -/
@[simp] theorem inverseGainFactor_empty (gain loss : Nat.Primes → ℝ) :
    inverseGainFactor ∅ gain loss = 1 := by simp [inverseGainFactor_def]

/-- The prime powers in an inverse gain factor are all positive. -/
theorem inverseGainFactor_pos (S : Finset Nat.Primes) (gain loss : Nat.Primes → ℝ) :
    0 < inverseGainFactor S gain loss := by
  rw [inverseGainFactor_def]
  exact Finset.prod_pos fun p _ ↦ zpow_pos (by exact_mod_cast p.property.pos) _

/-- At a prime in the support of the normalising product the norm is the rounded net gain,
expressed as a prime power. At every other prime the scalar has norm `1`. -/
@[simp] theorem padicNorm_inverseGainFactor (p : Nat.Primes) (S : Finset Nat.Primes)
    (gain loss : Nat.Primes → ℝ) :
    padicNorm (p : ℕ) (inverseGainFactor S gain loss) =
      if p ∈ S then (p.val : ℚ) ^ ⌊gain p - loss p⌋ else 1 := by
  rw [inverseGainFactor_def, padicNorm.prod_prime_zpow]
  simp only [neg_neg]

/-- The logarithm of the normalising factor is minus the sum of the rounded net gains,
each weighted by the logarithm of its prime. -/
theorem log_inverseGainFactor (S : Finset Nat.Primes) (gain loss : Nat.Primes → ℝ) :
    Real.log (inverseGainFactor S gain loss : ℝ) =
      ∑ p ∈ S, -(⌊gain p - loss p⌋ : ℝ) * Real.log p.val := by
  rw [inverseGainFactor_def, Rat.cast_prod, Real.log_prod]
  · simp only [Rat.cast_zpow, Rat.cast_natCast, Real.log_zpow, Int.cast_neg]
  · intro p _
    rw [Rat.cast_zpow, Rat.cast_natCast]
    exact zpow_ne_zero _ (by exact_mod_cast p.property.ne_zero)

/-- Relative to the unrounded logarithmic factor, flooring increases the logarithm by at most
one `log p` for each prime. -/
theorem log_inverseGainFactor_sub_mem_Icc (S : Finset Nat.Primes) (gain loss : Nat.Primes → ℝ) :
    Real.log (inverseGainFactor S gain loss : ℝ) -
        (∑ p ∈ S, (loss p - gain p) * Real.log p.val) ∈
      Set.Icc 0 (∑ p ∈ S, Real.log p.val) := by
  rw [log_inverseGainFactor, ← Finset.sum_sub_distrib]
  have hterm (p : Nat.Primes) :
      -(⌊gain p - loss p⌋ : ℝ) * Real.log p.val - (loss p - gain p) * Real.log p.val =
        (gain p - loss p - ⌊gain p - loss p⌋) * Real.log p.val := by ring
  simp only [hterm]
  have hlog (p : Nat.Primes) : 0 ≤ Real.log p.val :=
    Real.log_nonneg (by exact_mod_cast p.property.one_le)
  refine ⟨Finset.sum_nonneg fun p _ ↦ ?_, Finset.sum_le_sum fun p _ ↦ ?_⟩
  · exact mul_nonneg (sub_nonneg.mpr (Int.floor_le _)) (hlog p)
  · calc
      _ ≤ 1 * Real.log p.val := mul_le_mul_of_nonneg_right
        (by linarith [Int.lt_floor_add_one (gain p - loss p)]) (hlog p)
      _ = _ := one_mul _

/-- If all primes in `S` are at most `X` and the exceptional level prime `N` has nonnegative gain,
the logarithm of the factor is bounded above by the negative total gain over `S`, the loss
budget, and a rounding budget of `θ(X) + log N`. This includes the case `N ∈ S`. -/
theorem log_inverseGainFactor_insert_le (S : Finset Nat.Primes) (N : Nat.Primes)
    (gain loss : Nat.Primes → ℝ) {X B : ℝ} (hS : ∀ p ∈ S, (p.val : ℝ) ≤ X)
    (hN : 0 ≤ gain N) (hB : ∑ p ∈ insert N S, loss p * Real.log p.val ≤ B) :
    Real.log (inverseGainFactor (insert N S) gain loss : ℝ) ≤
      -(∑ p ∈ S, gain p * Real.log p.val) + B + Chebyshev.theta X + Real.log N.val := by
  have hcost := S.sum_insert_prime_log_le_theta_add_log N hS
  have hgain : (∑ p ∈ S, gain p * Real.log p.val) ≤
      ∑ p ∈ insert N S, gain p * Real.log p.val := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_insert N S) ?_
    intro p hp hpS
    have hpN := (Finset.mem_insert.mp hp).resolve_right hpS
    subst p
    exact mul_nonneg hN (Real.log_natCast_nonneg N.val)
  have hround := (log_inverseGainFactor_sub_mem_Icc (insert N S) gain loss).2
  simp only [sub_mul, Finset.sum_sub_distrib] at hround
  linarith

end TauCeti
