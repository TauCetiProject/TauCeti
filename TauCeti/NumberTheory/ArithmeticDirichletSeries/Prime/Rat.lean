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
# Prime summatory functions over `ℚ`

The nonzero primes of `𝓞 ℚ` correspond to the rational primes through their absolute norms
(Mathlib's `Rat.HeightOneSpectrum.primesEquiv`, with `Rat.HeightOneSpectrum.absNorm_asIdeal`
identifying the norm of `v` with its generator). This file transports a prime summatory function
over `ℚ` whose weight depends only on the norm to the corresponding sum over Mathlib's
`Nat.primesLE`, so that results stated for the primes of a number field specialize to the
classical sums over rational primes.

## Main results

* `TauCeti.image_absNorm_primesLE_rat`: the image of `primesLE ℚ x` under absolute norm is
  `Nat.primesLE ⌊x⌋₊`.
* `TauCeti.primeSummatory_rat_eq_sum_primesLE`: for a weight `f : ℕ → M`,
  `∑_{N𝔭 ≤ x} f (N𝔭)` over the primes of `𝓞 ℚ` is `∑_{p ∈ Nat.primesLE ⌊x⌋₊} f p`.
-/

public section

namespace TauCeti

open NumberField

/-- Over `ℚ`, the sum of a weight depending only on the norm over the primes of norm at most `x` is
the corresponding sum over the rational primes in `Nat.primesLE ⌊x⌋₊`. -/
theorem primeSummatory_rat_eq_sum_primesLE {M : Type*} [AddCommMonoid M] (f : ℕ → M) (x : ℝ) :
    primeSummatory ℚ (fun v ↦ f (Ideal.absNorm v.asIdeal)) x = ∑ p ∈ Nat.primesLE ⌊x⌋₊, f p := by
  have hprime (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) : (Ideal.absNorm v.asIdeal).Prime := by
    rw [Rat.HeightOneSpectrum.absNorm_asIdeal]
    exact Rat.HeightOneSpectrum.prime_natGenerator v
  have hmem (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) :
      v ∈ primesLE ℚ x ↔ Ideal.absNorm v.asIdeal ∈ Nat.primesLE ⌊x⌋₊ := by
    rw [mem_normLE, Nat.mem_primesLE, Nat.le_floor_iff' (hprime v).ne_zero]
    exact (and_iff_left (hprime v)).symm
  rw [primeSummatory_apply]
  refine Finset.sum_bij (fun v _ ↦ Ideal.absNorm v.asIdeal) (fun v hv ↦ (hmem v).mp hv)
    (fun v _ w _ h ↦ Rat.HeightOneSpectrum.absNorm_asIdeal_injective h) (fun p hp ↦ ?_)
    fun _ _ ↦ rfl
  obtain ⟨v, hv⟩ := Rat.HeightOneSpectrum.exists_absNorm_eq (Nat.prime_of_mem_primesLE hp)
  exact ⟨v, (hmem v).mpr (hv ▸ hp), hv⟩

/-- The image of `primesLE ℚ x` under absolute norm is `Nat.primesLE ⌊x⌋₊`. -/
theorem image_absNorm_primesLE_rat (x : ℝ) :
    (primesLE ℚ x).image (fun v ↦ Ideal.absNorm v.asIdeal) = Nat.primesLE ⌊x⌋₊ := by
  ext p
  simp only [Finset.mem_image, mem_normLE, Nat.mem_primesLE]
  constructor
  · rintro ⟨v, hv, rfl⟩
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

end TauCeti
