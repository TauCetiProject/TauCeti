/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Height.FamilyOverPairs.Basic
public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.GainFactor

/-!
# Integrality after prime-gain normalization

A rational inverse gain factor has the same local norm at every embedding above a given prime.
Multiplication by it makes a complex coefficient integral precisely when the coefficient's
local norm is at most the reciprocal of that norm. In particular, an estimate with the
unrounded net gain suffices, so the same factor can be used on all coefficients of a lift.

The normalization is that of `New.Data.norm_invGainFactor` and its application in
`New.Data.normalizedPoincare_mem_integralVectors`, in `grh/src/New/Reduction/ShortAndEnough.lean`
of lsernau/grh-lean (`72fead1`).
-/

public section

namespace PadicAlgCl

/-- The norm of an inverse gain factor at a prime in `S` is the prime raised to the rounded
net gain. At a prime outside `S` the norm is one. -/
@[simp]
theorem norm_ratCast_inverseGainFactor (p : ℕ) [hp : Fact p.Prime] (S : Finset Nat.Primes)
    (gain loss : Nat.Primes → ℝ) :
    let q : Nat.Primes := ⟨p, hp.out⟩
    ‖(S.inverseGainFactor gain loss : PadicAlgCl p)‖ =
      if q ∈ S then (p : ℝ) ^ ⌊gain q - loss q⌋ else 1 := by
  dsimp only
  set q : Nat.Primes := ⟨p, hp.out⟩
  rw [← map_ratCast (algebraMap ℚ_[p] (PadicAlgCl p)), norm_extends, Padic.eq_padicNorm]
  have h := congrArg (fun x : ℚ ↦ (x : ℝ)) (q.padicNorm_inverseGainFactor S gain loss)
  split_ifs at h ⊢ <;> push_cast at h <;> exact h

end PadicAlgCl

namespace TauCeti.PrimePadicIso

/-- A scaled coefficient is locally integral exactly when its norm lies within the budget
prescribed by the rounded gain at the given prime. At a prime outside the product, the
normalization does not change integrality. -/
theorem inverseGainFactor_mul_mem_integers_iff (ι : PrimePadicIso) (S : Finset Nat.Primes)
    (gain loss : Nat.Primes → ℝ) {z : ℂ} :
    let p : Nat.Primes := ⟨ι.prime, ι.fact_prime.out⟩
    ((S.inverseGainFactor gain loss : ℚ) : ℂ) * z ∈ ι.integers ↔
      ‖ι.iso z‖ ≤ if p ∈ S then (ι.prime : ℝ) ^ (-⌊gain p - loss p⌋) else 1 := by
  rw [mem_integers, map_mul, norm_mul, map_ratCast, PadicAlgCl.norm_ratCast_inverseGainFactor]
  dsimp only
  set p : Nat.Primes := ⟨ι.prime, ι.fact_prime.out⟩
  split_ifs
  · have hp : (0 : ℝ) < ι.prime := by exact_mod_cast ι.fact_prime.out.pos
    simp only [zpow_neg, ← one_div, le_div_iff₀ (zpow_pos hp _), mul_comm]
  · simp

/-- A bound by the unrounded net gain makes the normalized coefficient integral. Outside the
product it is enough that the net gain is nonnegative; in applications both gain and loss
vanish there. -/
theorem inverseGainFactor_mul_mem_integers_of_norm_le (ι : PrimePadicIso)
    (S : Finset Nat.Primes) (gain loss : Nat.Primes → ℝ) {z : ℂ}
    (hS : let p : Nat.Primes := ⟨ι.prime, ι.fact_prime.out⟩; p ∉ S → loss p ≤ gain p)
    (hz : let p : Nat.Primes := ⟨ι.prime, ι.fact_prime.out⟩;
      ‖ι.iso z‖ ≤ (ι.prime : ℝ) ^ (loss p - gain p)) :
    ((S.inverseGainFactor gain loss : ℚ) : ℂ) * z ∈ ι.integers := by
  have hp : (1 : ℝ) ≤ ι.prime := by exact_mod_cast ι.fact_prime.out.one_lt.le
  apply (ι.inverseGainFactor_mul_mem_integers_iff S gain loss).mpr
  dsimp only at hS hz ⊢
  set p : Nat.Primes := ⟨ι.prime, ι.fact_prime.out⟩
  split_ifs with h
  · rw [← Real.rpow_intCast, Int.cast_neg]
    have hfloor : loss p - gain p ≤ -(⌊gain p - loss p⌋ : ℝ) := by
      linarith only [Int.floor_le (gain p - loss p)]
    exact hz.trans (Real.rpow_le_rpow_of_exponent_le hp hfloor)
  · exact hz.trans (Real.rpow_le_one_of_one_le_of_nonpos hp (sub_nonpos.mpr (hS h)))

end TauCeti.PrimePadicIso
