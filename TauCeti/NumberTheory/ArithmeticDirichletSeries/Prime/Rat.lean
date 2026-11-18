/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.PrimeCounting
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Counting
import TauCeti.NumberTheory.NumberField.Ideal.IntegersRat

/-!
# The prime count of `ℚ`

Over `ℚ`, the number-field prime count `TauCeti.primeCount ℚ Set.univ` is the classical prime
counting function. The height-one primes of `𝓞 ℚ` correspond to the rational primes
(`Rat.HeightOneSpectrum.primesEquiv`), and the absolute norm of such a prime is the rational prime
it corresponds to, its residue ring being `ℤ / p` (`Rat.HeightOneSpectrum.absNorm_asIdeal`). The
absolute norm therefore restricts to a bijection from the primes of norm at most `x` onto the
rational primes `p ≤ ⌊x⌋₊`. Both cutoffs are inclusive: at `x = 2` both counts are `1`.

## Main results

* `TauCeti.primeCount_rat_univ`: `primeCount ℚ Set.univ x = Nat.primeCounting ⌊x⌋₊` for every real
  `x`.
-/

public section

open IsDedekindDomain
open scoped NumberField

namespace TauCeti

/-- The number of primes of `𝓞 ℚ` of absolute norm at most `x` is the number `π(⌊x⌋₊)` of rational
primes `p ≤ x`. -/
theorem primeCount_rat_univ (x : ℝ) :
    primeCount ℚ Set.univ x = Nat.primeCounting ⌊x⌋₊ := by
  classical
  rw [primeCount_eq_card, Finset.filter_true_of_mem fun _ _ ↦ Set.mem_univ _,
    ← Nat.primesLE_card_eq_primeCounting]
  congr 1
  refine Finset.card_nbij (fun v ↦ Ideal.absNorm v.asIdeal) (fun v hv ↦ ?_) (fun v _ w _ h ↦ ?_)
    fun p hp ↦ ?_
  · rw [Finset.mem_coe, mem_normLE] at hv
    rw [Finset.mem_coe, Nat.mem_primesLE]
    refine ⟨Nat.le_floor hv, ?_⟩
    simpa only [Rat.HeightOneSpectrum.absNorm_asIdeal] using
      Rat.HeightOneSpectrum.prime_natGenerator v
  · simp only [Rat.HeightOneSpectrum.absNorm_asIdeal] at h
    exact Rat.HeightOneSpectrum.primesEquiv.injective (Subtype.ext h)
  · rw [Finset.mem_coe, Nat.mem_primesLE] at hp
    obtain ⟨v, hv⟩ := Rat.HeightOneSpectrum.exists_absNorm_eq hp.2
    refine ⟨v, ?_, hv⟩
    rw [Finset.mem_coe, mem_normLE, hv]
    exact (Nat.le_floor_iff' hp.2.ne_zero).mp hp.1

end TauCeti
