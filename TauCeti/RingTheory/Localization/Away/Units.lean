/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GroupWithZero.Associated
public import Mathlib.RingTheory.Localization.Away.Basic
import TauCeti.Algebra.BigOperators.Associated

/-!
# Units of localizations away from primes and products of primes

In a cancellative commutative semiring, the units of the localization away from a prime element `p`
are precisely the products `u * p ^ k` with `u ∈ Rˣ` and `k ∈ ℤ`. More generally, when `f` is
associated to a finite product `∏ i ∈ s, p i` of primes (not necessarily distinct), an element
`x` of `Localization.Away f` is a unit if and only if clearing a power `f ^ n` yields
`u * ∏ i ∈ s, p i ^ k i` for some unit `u ∈ Rˣ` and exponents `k : ι → ℕ`.

In particular, an element not divisible by a prime `p` is already a unit if it becomes a unit after
inverting `p`, allowing invertibility off a prime divisor to descend to the original ring.

## Main results

* `Prime.isUnit_of_isUnit_away_of_not_dvd`: inverting a prime only turns its multiples into new
  units.
* `IsLocalization.Away.isUnit_iff_exists_mul_pow_eq_finsetProd`: unit criterion in a localization
  away from an element associated to a finite product of primes.
* `IsLocalization.Away.exists_unit_mul_zpow_of_prime` and
  `IsLocalization.Away.isUnit_iff_exists_unit_mul_zpow_of_prime`: the units of a localization away
  from a prime `p` are the `u * p ^ k` with `u ∈ Rˣ` and `k ∈ ℤ`.
-/

public section

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

variable {ι R S : Type*} [CommSemiring R] [IsCancelMulZero R] [CommSemiring S] [Algebra R S]

/-- In a localization away from an element `f` associated to a finite product `∏ i ∈ s, p i` of
primes, an element `x` is a unit if and only if multiplying by some power `f ^ n` produces
`u * ∏ i ∈ s, p i ^ k i` for a unit `u ∈ Rˣ` and exponents `k : ι → ℕ`. -/
theorem isUnit_iff_exists_mul_pow_eq_finsetProd (f : R) [IsLocalization.Away f S]
    {s : Finset ι} {p : ι → R} (hp : ∀ i ∈ s, Prime (p i))
    (hf : Associated f (∏ i ∈ s, p i)) {x : S} :
    IsUnit x ↔ ∃ (u : Rˣ) (k : ι → ℕ) (n : ℕ),
      x * algebraMap R S (f ^ n) = algebraMap R S (u * ∏ i ∈ s, p i ^ k i) := by
  constructor
  · intro hx
    obtain ⟨⟨a, _, n, rfl⟩, hxn⟩ := IsLocalization.surj (Submonoid.powers f) x
    have ha : IsUnit (algebraMap R S a) := by
      rw [← hxn, map_pow]
      exact hx.mul (algebraMap_pow_isUnit f n)
    obtain ⟨m, hm⟩ := (algebraMap_isUnit_iff (S := S) f).mp ha
    have hm' : a ∣ ∏ i ∈ s, p i ^ m := by
      rw [Finset.prod_pow]
      exact hm.trans hf.pow_pow.dvd
    obtain ⟨k, -, u, hu⟩ := (TauCeti.dvd_finsetProd_pow_iff_of_prime hp (fun _ ↦ m)).mp hm'
    refine ⟨u⁻¹, k, n, ?_⟩
    have hau : a = (u⁻¹ : Rˣ) * ∏ i ∈ s, p i ^ k i := by
      rw [← hu, mul_comm a u, ← mul_assoc, Units.inv_mul, one_mul]
    rw [← hau]
    exact hxn
  · rintro ⟨u, k, n, h⟩
    have hrhs : IsUnit (algebraMap R S (u * ∏ i ∈ s, p i ^ k i)) := by
      rw [map_mul, map_prod]
      refine (u.isUnit.map (algebraMap R S)).mul
        (Finset.prod_induction _ IsUnit (fun _ _ ↦ IsUnit.mul) isUnit_one fun i hi ↦ ?_)
      rw [map_pow]
      exact (isUnit_of_dvd f ((Finset.dvd_prod_of_mem p hi).trans hf.symm.dvd)).pow (k i)
    exact isUnit_of_mul_isUnit_left (h.symm ▸ hrhs)

/-- Every unit of a localization away from a prime element `p` is the image of a unit of `R`
multiplied by an integer power of `p`. -/
theorem exists_unit_mul_zpow_of_prime (p : R) [IsLocalization.Away p S] (hp : Prime p) (x : Sˣ) :
    ∃ (u : Rˣ) (k : ℤ),
      x = Units.map (algebraMap R S).toMonoidHom u *
        (algebraMap_isUnit (S := S) p).unit ^ k := by
  obtain ⟨u, k, n, h⟩ := (isUnit_iff_exists_mul_pow_eq_finsetProd p (s := {()})
    (p := fun _ ↦ p) (fun _ _ ↦ hp) (by simp)).mp x.isUnit
  refine ⟨u, (k () : ℤ) - n, ?_⟩
  have hunit : x * (algebraMap_isUnit (S := S) p).unit ^ (n : ℤ) =
      Units.map (algebraMap R S).toMonoidHom u *
        (algebraMap_isUnit (S := S) p).unit ^ (k () : ℤ) :=
    Units.ext (by simpa [map_mul, map_pow] using h)
  rw [eq_mul_inv_iff_mul_eq.mpr hunit, mul_assoc, ← zpow_sub]

/-- An element of a localization away from a prime `p` is a unit if and only if it is the image of
a unit of `R` multiplied by an integer power of `p`. -/
theorem isUnit_iff_exists_unit_mul_zpow_of_prime (p : R) [IsLocalization.Away p S] (hp : Prime p)
    {x : S} :
    IsUnit x ↔ ∃ (u : Rˣ) (k : ℤ),
      x = algebraMap R S u * ((algebraMap_isUnit (S := S) p).unit ^ k : Sˣ) := by
  refine ⟨fun hx ↦ ?_, ?_⟩
  · obtain ⟨u, k, hk⟩ := exists_unit_mul_zpow_of_prime p hp hx.unit
    exact ⟨u, k, by simpa using congrArg Units.val hk⟩
  · rintro ⟨u, k, rfl⟩
    exact (u.isUnit.map (algebraMap R S)).mul (Units.isUnit _)

end IsLocalization.Away
