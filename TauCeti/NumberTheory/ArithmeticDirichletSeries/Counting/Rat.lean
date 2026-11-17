/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.NumberTheory.PrimeCounting
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Counting
import TauCeti.NumberTheory.NumberField.Ideal.IntegersRat

/-!
# Rational prime-ideal counting transport

Over `ℚ`, the height-one prime ideals of `𝓞 ℚ` are identified with the rational primes via their
absolute norms (`Rat.HeightOneSpectrum.absNorm_asIdeal`, `Rat.HeightOneSpectrum.exists_absNorm_eq`,
and `TauCeti.absNorm_asIdeal_rat_injective`). This file transports the number-field cutoff set
`TauCeti.primesLE ℚ x`, finite products and sums over `primesLE ℚ x`, the prime summatory function
`TauCeti.primeSummatory ℚ`, and norm-truncated `finprod`s over `HeightOneSpectrum (𝓞 ℚ)` to the
corresponding objects over `Nat.primesLE ⌊x⌋₊`.

## Main results

* `TauCeti.image_absNorm_primesLE_rat`: the image of `primesLE ℚ x` under `Ideal.absNorm` is
  `Nat.primesLE ⌊x⌋₊`.
* `TauCeti.prod_primesLE_rat_eq_prod_primesLE` and `TauCeti.sum_primesLE_rat_eq_sum_primesLE`:
  products and sums over `primesLE ℚ x` depending only on the absolute norm agree with those over
  `Nat.primesLE ⌊x⌋₊`.
* `TauCeti.primeSummatory_rat_eq_sum_primesLE`: `primeSummatory ℚ` of a function of the absolute
  norm equals the sum over `Nat.primesLE ⌊x⌋₊`.
* `TauCeti.finprod_heightOneSpectrum_rat_ite_absNorm_le_eq_prod_primesLE`: a norm-truncated
  `finprod` over `HeightOneSpectrum (𝓞 ℚ)` depending only on the absolute norm equals the finite
  product over `Nat.primesLE ⌊x⌋₊`.
-/

public section

open IsDedekindDomain
open scoped NumberField

namespace TauCeti

-- Not `@[simp]`: `Rat.HeightOneSpectrum.absNorm_asIdeal` is `@[simp]` and rewrites
-- `Ideal.absNorm v.asIdeal` to `Rat.HeightOneSpectrum.natGenerator v` on the left-hand sides of
-- the `Ideal.absNorm` transport lemmas below (`simpNF`).
/-- The norms of the height-one primes of `𝓞 ℚ` bounded by `x` are the rational primes `p ≤ ⌊x⌋₊`.
For `x < 2` both sides are empty. -/
theorem image_absNorm_primesLE_rat (x : ℝ) :
    (primesLE ℚ x).image (fun v ↦ Ideal.absNorm v.asIdeal) = Nat.primesLE ⌊x⌋₊ := by
  ext p
  simp only [Finset.mem_image, mem_normLE, Nat.mem_primesLE]
  constructor
  · rintro ⟨v, hvx, rfl⟩
    exact ⟨Nat.le_floor hvx,
      (Rat.HeightOneSpectrum.absNorm_asIdeal v).symm ▸ Rat.HeightOneSpectrum.prime_natGenerator v⟩
  · rintro ⟨hpx, hp⟩
    obtain ⟨v, rfl⟩ := Rat.HeightOneSpectrum.exists_absNorm_eq hp
    exact ⟨v, (Nat.le_floor_iff' hp.ne_zero).mp hpx, rfl⟩

/-- A product over `primesLE ℚ x` depending only on the absolute norm equals the corresponding
product over `Nat.primesLE ⌊x⌋₊`. -/
@[to_additive /-- A sum over `primesLE ℚ x` depending only on the absolute norm equals the
corresponding sum over `Nat.primesLE ⌊x⌋₊`. -/]
theorem prod_primesLE_rat_eq_prod_primesLE {M : Type*} [CommMonoid M] (f : ℕ → M) (x : ℝ) :
    (∏ v ∈ primesLE ℚ x, f (Ideal.absNorm v.asIdeal)) = ∏ p ∈ Nat.primesLE ⌊x⌋₊, f p := by
  rw [← image_absNorm_primesLE_rat,
    Finset.prod_image fun _ _ _ _ h ↦ absNorm_asIdeal_rat_injective h]

/-- The prime summatory function over `ℚ` of a function of the ideal norm is the finite sum over
rational primes `p ≤ ⌊x⌋₊`. -/
theorem primeSummatory_rat_eq_sum_primesLE {M : Type*} [AddCommMonoid M] (f : ℕ → M) (x : ℝ) :
    primeSummatory ℚ (fun v ↦ f (Ideal.absNorm v.asIdeal)) x = ∑ p ∈ Nat.primesLE ⌊x⌋₊, f p := by
  rw [primeSummatory_apply, sum_primesLE_rat_eq_sum_primesLE]

/-- A `finprod` over `HeightOneSpectrum (𝓞 ℚ)` truncated at norm `x` equals the finite product over
`Nat.primesLE ⌊x⌋₊`. -/
theorem finprod_heightOneSpectrum_rat_ite_absNorm_le_eq_prod_primesLE {M : Type*} [CommMonoid M]
    (f : ℕ → M) (x : ℝ) :
    (∏ᶠ v : HeightOneSpectrum (𝓞 ℚ),
        if (Ideal.absNorm v.asIdeal : ℝ) ≤ x then f (Ideal.absNorm v.asIdeal) else 1) =
      ∏ p ∈ Nat.primesLE ⌊x⌋₊, f p := by
  rw [finprod_eq_prod_of_mulSupport_subset (s := primesLE ℚ x),
    ← prod_primesLE_rat_eq_prod_primesLE]
  · exact Finset.prod_congr rfl fun v hv ↦
      ite_eq_left ((mem_normLE fun w : HeightOneSpectrum (𝓞 ℚ) ↦ Ideal.absNorm w.asIdeal).mp hv)
  · intro v hv
    rw [Finset.mem_coe, mem_normLE]
    by_contra hvx
    exact hv (ite_eq_right hvx)

end TauCeti
