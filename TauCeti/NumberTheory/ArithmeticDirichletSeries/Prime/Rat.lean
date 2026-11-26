/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.PrimeCounting
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Counting
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Prime.Psi
import TauCeti.NumberTheory.NumberField.Ideal.IntegersRat

/-!
# Prime summatory functions and the prime count over `ℚ`

The nonzero primes of `𝓞 ℚ` correspond to the rational primes through their absolute norms
(Mathlib's `Rat.HeightOneSpectrum.primesEquiv`, with `Rat.HeightOneSpectrum.absNorm_asIdeal`
identifying the norm of `v` with its generator). This file transports a prime summatory function or
finite product over `ℚ` whose weight depends only on the norm to the corresponding sum or product
over Mathlib's `Nat.primesLE`, so that results stated for the primes of a number field specialize to
the classical sums and products over rational primes. The number-field prime count
`TauCeti.primeCount ℚ Set.univ` is the classical prime counting function, and
`TauCeti.primePsi ℚ Set.univ` is Mathlib's Chebyshev function `ψ`. These use inclusive cutoffs:
at `x = 2` the prime counts are `1`.

## Main results

* `TauCeti.image_absNorm_primesLE_rat`: the image of `primesLE ℚ x` under absolute norm is
  `Nat.primesLE ⌊x⌋₊`.
* `TauCeti.prod_primesLE_rat_eq_prod_primesLE`: products over `primesLE ℚ x` depending only on
  the absolute norm agree with those over `Nat.primesLE ⌊x⌋₊`.
* `TauCeti.primeSummatory_rat_eq_sum_primesLE`: for a weight `f : ℕ → M`,
  `∑_{N𝔭 ≤ x} f (N𝔭)` over the primes of `𝓞 ℚ` is `∑_{p ∈ Nat.primesLE ⌊x⌋₊} f p`.
* `TauCeti.primeCount_rat_univ`: `primeCount ℚ Set.univ x = Nat.primeCounting ⌊x⌋₊` for every real
  `x`.
-/

public section

namespace TauCeti

open NumberField

/-- The image of `primesLE ℚ x` under absolute norm is `Nat.primesLE ⌊x⌋₊`. -/
theorem image_absNorm_primesLE_rat (x : ℝ) :
    (primesLE ℚ x).image (fun v ↦ Ideal.absNorm v.asIdeal) = Nat.primesLE ⌊x⌋₊ := by
  ext p
  simp only [Finset.mem_image, mem_normLE, Nat.mem_primesLE]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨Nat.le_floor hv, Rat.HeightOneSpectrum.prime_absNorm_asIdeal v⟩
  · rintro ⟨hple, hp⟩
    obtain ⟨v, hv⟩ := Rat.HeightOneSpectrum.exists_absNorm_eq hp
    have hx0 : 0 ≤ x := by
      by_contra hlt
      have hfl : ⌊x⌋₊ = 0 := Nat.floor_of_nonpos (le_of_not_ge hlt)
      have hp2 := hp.two_le
      omega
    exact ⟨v, hv.symm ▸ (Nat.cast_le.mpr hple).trans (Nat.floor_le hx0), hv⟩

/-- A product over `primesLE ℚ x` depending only on the absolute norm equals the corresponding
product over `Nat.primesLE ⌊x⌋₊`. -/
@[to_additive /-- A sum over `primesLE ℚ x` depending only on the
absolute norm equals the corresponding sum over `Nat.primesLE ⌊x⌋₊`. -/]
theorem prod_primesLE_rat_eq_prod_primesLE {M : Type*} [CommMonoid M] (f : ℕ → M) (x : ℝ) :
    (∏ v ∈ primesLE ℚ x, f (Ideal.absNorm v.asIdeal)) = ∏ p ∈ Nat.primesLE ⌊x⌋₊, f p := by
  rw [← image_absNorm_primesLE_rat,
    Finset.prod_image fun _ _ _ _ h ↦ Rat.HeightOneSpectrum.absNorm_asIdeal_injective h]

/-- Over `ℚ`, the sum of a weight depending only on the norm over the primes of norm at most `x` is
the corresponding sum over the rational primes in `Nat.primesLE ⌊x⌋₊`. -/
theorem primeSummatory_rat_eq_sum_primesLE {M : Type*} [AddCommMonoid M] (f : ℕ → M) (x : ℝ) :
    primeSummatory ℚ (fun v ↦ f (Ideal.absNorm v.asIdeal)) x = ∑ p ∈ Nat.primesLE ⌊x⌋₊, f p := by
  rw [primeSummatory_apply, sum_primesLE_rat_eq_sum_primesLE]

/-- The number of primes of `𝓞 ℚ` of absolute norm at most `x` is the number `π(⌊x⌋₊)` of rational
primes `p ≤ x`. -/
theorem primeCount_rat_univ (x : ℝ) :
    primeCount ℚ Set.univ x = Nat.primeCounting ⌊x⌋₊ := by
  classical
  rw [primeCount_eq_card, Finset.filter_true_of_mem fun _ _ ↦ Set.mem_univ _,
    ← Nat.primesLE_card_eq_primeCounting, ← image_absNorm_primesLE_rat,
    Finset.card_image_of_injective _ Rat.HeightOneSpectrum.absNorm_asIdeal_injective]

/-- The sum of the von Mangoldt weights of all prime ideal powers over `ℚ` is Mathlib's
Chebyshev function `ψ`. -/
@[simp] theorem primePsi_rat_univ (x : ℝ) : primePsi ℚ Set.univ x = Chebyshev.psi x := by
  rw [primePsi_eq_sum_Icc, Chebyshev.psi, ← Finset.Icc_add_one_left_eq_Ioc, zero_add]
  exact Finset.sum_congr rfl fun n _ ↦ primeVonMangoldtCoeff_rat_univ n

end TauCeti
