/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.Away.Basic
import TauCeti.Algebra.BigOperators.Associated

/-!
# Units in localizations away from prime elements

In a domain `R`, inverting an element `x` creates new units only from divisors of powers of `x`.
When `x` is prime, an element not divisible by `x` is a unit if it becomes one after inverting `x`,
and every unit of the localization away from `x` has the form `c * x ^ n` (`c` a unit of `R`,
`n : ℤ`), written with `selfZPow`. More generally, when `x` is associated to a finite product
`∏ i ∈ t, p i` of primes, every unit of the localization is a unit of `R` times an integer-exponent
product of the images of the `p i`.

## Main definitions and results

* `isUnit_selfZPow`: every integer power `selfZPow x S n` in an away localization is a unit.
* `Prime.isUnit_of_isUnit_away_of_not_dvd`: an element not divisible by a prime `p` that becomes a
  unit after inverting `p` is already a unit.
* `IsLocalization.Away.isUnit_iff_of_prime`: in a localization of a domain away from a prime `x`,
  the units are the elements `algebraMap R S r * selfZPow x S n` with `r` a unit of `R` and `n : ℤ`.
* `IsLocalization.Away.exists_unit_mul_prod_zpow_eq_of_associated_prod_prime`: in a localization of
  a domain away from an element associated to a product `∏ i ∈ t, p i` of primes, every unit is a
  unit of `R` times `∏ i ∈ t, v i ^ m i` (`m : ι → ℤ`).
-/

public section

/-- Every integer power `selfZPow x S n` of `x` in a localization away from `x` is a unit. -/
@[simp]
theorem isUnit_selfZPow {R : Type*} [CommSemiring R] (x : R) (S : Type*) [CommSemiring S]
    [Algebra R S] [IsLocalization.Away x S] (n : ℤ) : IsUnit (selfZPow x S n) :=
  .of_mul_eq_one (selfZPow x S (-n)) (selfZPow_mul_neg x S n)

namespace Prime

variable {R S : Type*} [CommSemiring R] [IsDomain R] [CommSemiring S] [Algebra R S]
  {p x : R} [IsLocalization.Away p S]

/-- Inverting a prime element can only make its multiples into new units. -/
theorem isUnit_of_isUnit_away_of_not_dvd (hp : Prime p)
    (hx : IsUnit (algebraMap R S x)) (hpx : ¬p ∣ x) : IsUnit x := by
  obtain ⟨n, hn⟩ := (IsLocalization.Away.algebraMap_isUnit_iff (S := S) p).mp hx
  obtain ⟨i, _, hi⟩ := (dvd_prime_pow hp n).mp hn
  by_cases hi0 : i = 0
  · exact associated_one_iff_isUnit.mp (by simpa [hi0] using hi)
  · exact (hpx ((dvd_pow_self p hi0).trans hi.dvd')).elim

end Prime

namespace IsLocalization.Away

variable {R S : Type*} [CommSemiring R] [IsDomain R] [CommSemiring S] [Algebra R S]

/-- **Units of a localization away from a prime.** Over a domain `R`, an element of a localization
`S` away from a prime `x` is a unit if and only if it has the form
`algebraMap R S r * selfZPow x S n` for a unit `r` of `R` and an integer `n : ℤ`. -/
theorem isUnit_iff_of_prime {x : R} [IsLocalization.Away x S] (hx : Prime x) {s : S} :
    IsUnit s ↔ ∃ r : R, IsUnit r ∧ ∃ n : ℤ, algebraMap R S r * selfZPow x S n = s := by
  refine ⟨fun hs ↦ ?_, fun ⟨r, hr, n, h⟩ ↦ h ▸ (hr.map _).mul (isUnit_selfZPow x S n)⟩
  obtain ⟨k, a, hka⟩ := surj x s
  have ha_unit : IsUnit (algebraMap R S a) := by
    rw [← hka]
    exact hs.mul (algebraMap_pow_isUnit (S := S) x k)
  obtain ⟨N, hN⟩ := (algebraMap_isUnit_iff (S := S) x).mp ha_unit
  obtain ⟨i, _, u, hau⟩ := (dvd_prime_pow hx N).mp hN
  have ha_eq : a = (u⁻¹ : Rˣ) * x ^ i := by
    rw [← hau, mul_comm a, Units.inv_mul_cancel_left]
  refine ⟨(u⁻¹ : Rˣ), (u⁻¹ : Rˣ).isUnit, (i : ℤ) - (k : ℤ), ?_⟩
  rw [selfZPow_sub_natCast]
  apply (algebraMap_pow_isUnit (S := S) x k).mul_left_inj.mp
  have hmk : IsLocalization.mk' S (x ^ i) (Submonoid.pow x k) * algebraMap R S (x ^ k) =
      algebraMap R S (x ^ i) :=
    IsLocalization.mk'_spec S (x ^ i) (Submonoid.pow x k)
  rw [mul_assoc, ← map_pow, hmk, ← map_mul, ← ha_eq, ← hka, map_pow]

/-- **Units of a localization away from a product of primes.** Over a domain `R`, if `x` is
associated to a finite product `∏ i ∈ t, p i` of primes and `v i : Sˣ` represents the image of
`p i` in a localization `S` away from `x`, then every unit of `S` has the form
`Units.map (algebraMap R S) c * ∏ i ∈ t, v i ^ m i` for `c : Rˣ` and `m : ι → ℤ`. -/
theorem exists_unit_mul_prod_zpow_eq_of_associated_prod_prime {ι : Type*} {t : Finset ι}
    {p : ι → R} {x : R} [IsLocalization.Away x S] (hp : ∀ i ∈ t, Prime (p i))
    (hx : Associated x (∏ i ∈ t, p i)) {v : ι → Sˣ}
    (hv : ∀ i ∈ t, (v i : S) = algebraMap R S (p i)) (u : Sˣ) :
    ∃ (c : Rˣ) (m : ι → ℤ),
      Units.map (algebraMap R S : R →* S) c * ∏ i ∈ t, v i ^ m i = u := by
  obtain ⟨n, a, hna⟩ := surj x (u : S)
  have ha_unit : IsUnit (algebraMap R S a) := by
    rw [← hna]
    exact u.isUnit.mul (algebraMap_pow_isUnit (S := S) x n)
  obtain ⟨N, hN⟩ := (algebraMap_isUnit_iff (S := S) x).mp ha_unit
  have hdvd : a ∣ ∏ i ∈ t, p i ^ N := by
    rw [Finset.prod_pow]
    exact hN.trans (pow_dvd_pow_of_dvd hx.dvd N)
  obtain ⟨k, -, ua, hua⟩ := (Finset.dvd_prod_pow_iff_of_prime hp).mp hdvd
  obtain ⟨ux, hux⟩ := hx.symm
  -- Lift the numerator-denominator identity `(u : S) * x ^ n = a` into the unit group `Sˣ`.
  let φ : Rˣ →* Sˣ := Units.map (algebraMap R S : R →* S)
  have hrel :
      u * (φ (ux ^ n) * ∏ i ∈ t, v i ^ n) = φ ua⁻¹ * ∏ i ∈ t, v i ^ k i := by
    ext
    have hv_pow (e : ι → ℕ) :
        ((∏ i ∈ t, v i ^ e i : Sˣ) : S) = algebraMap R S (∏ i ∈ t, p i ^ e i) := by
      rw [← Units.coeHom_apply, map_prod, map_prod]
      exact Finset.prod_congr rfl fun i hi ↦ by
        rw [Units.coeHom_apply, Units.val_pow_eq_pow_val, hv i hi, map_pow]
    have ha_eq : (ua⁻¹ : Rˣ) * ∏ i ∈ t, p i ^ k i = a := by
      rw [← hua, mul_comm a, Units.inv_mul_cancel_left]
    have hx_eq : (ux ^ n : Rˣ) * ∏ i ∈ t, p i ^ n = x ^ n := by
      rw [Units.val_pow_eq_pow_val, Finset.prod_pow, mul_comm, ← mul_pow, hux]
    rw [Units.val_mul, Units.val_mul, Units.val_mul, hv_pow, hv_pow]
    simp only [φ, Units.coe_map, MonoidHom.coe_ofClass, ← map_mul, ha_eq, hx_eq]
    rw [map_pow, hna]
  refine ⟨ua⁻¹ * (ux ^ n)⁻¹, fun i ↦ (k i : ℤ) - (n : ℤ),
    mul_right_cancel (b := φ (ux ^ n) * ∏ i ∈ t, v i ^ n) ?_⟩
  rw [hrel, mul_mul_mul_comm, ← map_mul, mul_assoc ua⁻¹, inv_mul_cancel, mul_one,
    ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [← zpow_natCast (v i) n, ← zpow_add, sub_add_cancel, zpow_natCast]

end IsLocalization.Away
