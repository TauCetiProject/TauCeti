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
# Rational prime-ideal counting transport

Over `ℚ`, absolute norm identifies the height-one primes of `𝓞 ℚ` bijectively with the rational
primes (`Rat.HeightOneSpectrum.absNorm_asIdeal`, `Rat.HeightOneSpectrum.exists_absNorm_eq`,
`Rat.HeightOneSpectrum.absNorm_asIdeal_injective`). Consequently, the finite cutoff carrier
`TauCeti.primesLE ℚ x` maps bijectively onto Mathlib's `Nat.primesLE ⌊x⌋₊`, and any prime
summatory function `TauCeti.primeSummatory ℚ` depending only on the absolute norm equals the
corresponding finite sum over `Nat.primesLE ⌊x⌋₊`.

## Main results

* `TauCeti.image_absNorm_primesLE_rat`: the image of `primesLE ℚ x` under absolute norm is
  `Nat.primesLE ⌊x⌋₊`.
* `TauCeti.primeSummatory_rat_eq_sum_primesLE`: a summatory function over the height-one primes of
  `𝓞 ℚ` depending only on the absolute norm equals the corresponding finite sum over
  `Nat.primesLE ⌊x⌋₊`.
-/

public section

open Finset

namespace TauCeti

/-- The image of `primesLE ℚ x` under absolute norm is `Nat.primesLE ⌊x⌋₊`. -/
theorem image_absNorm_primesLE_rat (x : ℝ) :
    (primesLE ℚ x).image (fun v ↦ Ideal.absNorm v.asIdeal) = Nat.primesLE ⌊x⌋₊ := by
  ext p
  simp only [mem_image, mem_normLE, Nat.mem_primesLE]
  constructor
  · rintro ⟨v, hv, rfl⟩
    have hx0 : 0 ≤ x := (Nat.cast_nonneg _).trans hv
    rw [Rat.HeightOneSpectrum.absNorm_asIdeal] at hv ⊢
    exact ⟨Nat.le_floor hv, Rat.HeightOneSpectrum.prime_natGenerator v⟩
  · rintro ⟨hple, hp⟩
    obtain ⟨v, hv⟩ := Rat.HeightOneSpectrum.exists_absNorm_eq hp
    have hx0 : 0 ≤ x := by
      by_contra hlt
      have hfl : ⌊x⌋₊ = 0 := Nat.floor_of_nonpos (le_of_not_ge hlt)
      have hp2 := hp.two_le
      omega
    exact ⟨v, hv.symm ▸ (Nat.cast_le.mpr hple).trans (Nat.floor_le hx0), hv⟩

/-- A summatory function over the height-one primes of `𝓞 ℚ` depending only on the absolute norm
equals the corresponding finite sum over `Nat.primesLE ⌊x⌋₊`. -/
theorem primeSummatory_rat_eq_sum_primesLE {M : Type*} [AddCommMonoid M] (f : ℕ → M) (x : ℝ) :
    primeSummatory ℚ (fun v ↦ f (Ideal.absNorm v.asIdeal)) x = ∑ p ∈ Nat.primesLE ⌊x⌋₊, f p := by
  rw [primeSummatory_apply, ← image_absNorm_primesLE_rat,
    sum_image fun _ _ _ _ h ↦ Rat.HeightOneSpectrum.absNorm_asIdeal_injective h]

end TauCeti
