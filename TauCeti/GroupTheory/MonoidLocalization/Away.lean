/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Associated
public import Mathlib.GroupTheory.MonoidLocalization.Away
import Mathlib.GroupTheory.MonoidLocalization.Divisibility
import TauCeti.Algebra.BigOperators.Associated
import TauCeti.Algebra.Divisibility.Basic

/-!
# Units of monoid localizations away from primes and products of primes

In a commutative monoid with zero, the units of a localization away from a regular prime element
`p` are precisely the products `u * p ^ k` with `u ∈ Mˣ` and `k ∈ ℤ`. More generally, when `f` is
regular and associated to a finite product `∏ i ∈ s, p i` of primes (not necessarily distinct), an
element `x` of a monoid localization `F : Submonoid.LocalizationMap.AwayMap f N` is a unit if and
only if clearing a power `f ^ n` yields `u * ∏ i ∈ s, p i ^ k i` for some unit `u ∈ Mˣ` and
exponents `k : ι → ℕ`.

In particular, for a regular prime `p`, an element not divisible by `p` is already a unit if it
becomes a unit after localizing away from `p`.

## Main results

* `Prime.isUnit_of_isUnit_awayMap_of_not_dvd`: inverting a regular prime only turns its multiples
  into new units.
* `Submonoid.LocalizationMap.AwayMap.isUnit_iff_exists_mul_pow_eq_finsetProd`: unit criterion in a
  monoid localization away from a regular element associated to a finite product of primes.
* `Submonoid.LocalizationMap.AwayMap.exists_unit_mul_zpow_of_prime` and
  `Submonoid.LocalizationMap.AwayMap.isUnit_iff_exists_unit_mul_zpow_of_prime`: the units of a
  monoid localization away from a regular prime `p` are the `u * p ^ k` with `u ∈ Mˣ` and `k ∈ ℤ`.
-/

public section

namespace Prime

variable {M N : Type*} [CommMonoidWithZero M] [CommMonoid N] {p x : M}

/-- Inverting a regular prime element in a commutative monoid with zero can only make its
multiples into new units. -/
theorem isUnit_of_isUnit_awayMap_of_not_dvd (hp : Prime p) (hreg : IsLeftRegular p)
    (F : Submonoid.LocalizationMap.AwayMap p N) (hx : IsUnit (F x)) (hpx : ¬p ∣ x) :
    IsUnit x := by
  obtain ⟨_, ⟨n, rfl⟩, hn⟩ := F.map_isUnit_iff.mp hx
  obtain ⟨i, -, b, hb, hi⟩ :=
    (TauCeti.dvd_prime_pow_mul_iff hp hreg n (a := 1)).mp (by simpa using hn)
  by_cases hi0 : i = 0
  · have hxb : x ∣ b := by simpa [hi0] using hi.dvd
    exact isUnit_of_dvd_one (hxb.trans hb)
  · exact (hpx ((dvd_pow_self p hi0).trans ((dvd_mul_right (p ^ i) b).trans hi.dvd'))).elim

end Prime

namespace Submonoid.LocalizationMap.AwayMap

variable {ι M N : Type*} [CommMonoidWithZero M] [CommMonoid N]

/-- In a monoid localization away from a regular element `f` associated to a finite product
`∏ i ∈ s, p i` of primes, an element `x` is a unit if and only if multiplying by some power
`f ^ n` produces `u * ∏ i ∈ s, p i ^ k i` for a unit `u ∈ Mˣ` and exponents `k : ι → ℕ`. -/
theorem isUnit_iff_exists_mul_pow_eq_finsetProd {f : M} (F : AwayMap f N)
    {s : Finset ι} {p : ι → M} (hp : ∀ i ∈ s, Prime (p i))
    (hf : Associated f (∏ i ∈ s, p i)) (hreg : IsLeftRegular f) {x : N} :
    IsUnit x ↔ ∃ (u : Mˣ) (k : ι → ℕ) (n : ℕ),
      x * F (f ^ n) = F (u * ∏ i ∈ s, p i ^ k i) := by
  constructor
  · intro hx
    obtain ⟨⟨a, _, n, rfl⟩, hxn⟩ := F.surj x
    have ha : IsUnit (F a) := by
      rw [← hxn]
      exact hx.mul (F.map_units ⟨f ^ n, n, rfl⟩)
    obtain ⟨_, ⟨m, rfl⟩, hm⟩ := F.map_isUnit_iff.mp ha
    have hm' : a ∣ ∏ i ∈ s, p i ^ m := by
      rw [Finset.prod_pow]
      exact hm.trans hf.pow_pow.dvd
    have hregp : ∀ i ∈ s, IsLeftRegular (p i) := fun i hi ↦
      hreg.of_dvd ((Finset.dvd_prod_of_mem p hi).trans hf.symm.dvd)
    obtain ⟨k, -, u, hu⟩ := (TauCeti.dvd_finsetProd_pow_iff_of_prime hp hregp (fun _ ↦ m)).mp hm'
    refine ⟨u⁻¹, k, n, ?_⟩
    have hau : a = (u⁻¹ : Mˣ) * ∏ i ∈ s, p i ^ k i := by
      rw [← hu, mul_comm a u, ← mul_assoc, Units.inv_mul, one_mul]
    rw [← hau]
    exact hxn
  · rintro ⟨u, k, n, h⟩
    have hrhs : IsUnit (F (u * ∏ i ∈ s, p i ^ k i)) := by
      rw [map_mul, map_prod]
      refine (u.isUnit.map F.toMonoidHom).mul
        (Finset.prod_induction _ IsUnit (fun _ _ ↦ IsUnit.mul) isUnit_one fun i hi ↦ ?_)
      rw [map_pow]
      have hpi : IsUnit (F (p i)) :=
        isUnit_of_dvd_unit (map_dvd F ((Finset.dvd_prod_of_mem p hi).trans hf.symm.dvd))
          (F.map_units ⟨f, 1, pow_one f⟩)
      exact hpi.pow (k i)
    exact isUnit_of_mul_isUnit_left (h.symm ▸ hrhs)

/-- Every unit of a monoid localization away from a regular prime element `p` is the image of a
unit of `M` multiplied by an integer power of `p`. -/
theorem exists_unit_mul_zpow_of_prime {p : M} (F : AwayMap p N) (hp : Prime p)
    (hreg : IsLeftRegular p) (x : Nˣ) :
    ∃ (u : Mˣ) (k : ℤ),
      x = Units.map F.toMonoidHom u * (F.map_units ⟨p, Submonoid.mem_powers p⟩).unit ^ k := by
  obtain ⟨u, k, n, h⟩ := (F.isUnit_iff_exists_mul_pow_eq_finsetProd (s := {()})
    (p := fun _ ↦ p) (fun _ _ ↦ hp) (by simp) hreg).mp x.isUnit
  refine ⟨u, (k () : ℤ) - n, ?_⟩
  have hunit : x * (F.map_units ⟨p, Submonoid.mem_powers p⟩).unit ^ (n : ℤ) =
      Units.map F.toMonoidHom u * (F.map_units ⟨p, Submonoid.mem_powers p⟩).unit ^ (k () : ℤ) :=
    Units.ext (by simpa [map_mul, map_pow] using h)
  rw [eq_mul_inv_iff_mul_eq.mpr hunit, mul_assoc, ← zpow_sub]

/-- An element of a monoid localization away from a regular prime `p` is a unit if and only if it
is the image of a unit of `M` multiplied by an integer power of `p`. -/
theorem isUnit_iff_exists_unit_mul_zpow_of_prime {p : M} (F : AwayMap p N) (hp : Prime p)
    (hreg : IsLeftRegular p) {x : N} :
    IsUnit x ↔ ∃ (u : Mˣ) (k : ℤ),
      x = F u * ((F.map_units ⟨p, Submonoid.mem_powers p⟩).unit ^ k : Nˣ) := by
  refine ⟨fun hx ↦ ?_, ?_⟩
  · obtain ⟨u, k, hk⟩ := F.exists_unit_mul_zpow_of_prime hp hreg hx.unit
    exact ⟨u, k, by simpa using congrArg Units.val hk⟩
  · rintro ⟨u, k, rfl⟩
    exact (u.isUnit.map F.toMonoidHom).mul (Units.isUnit _)

end Submonoid.LocalizationMap.AwayMap
