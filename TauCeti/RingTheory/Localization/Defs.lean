/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.Defs

/-!
# Basic facts about localizations of commutative semirings

For a localization `S` of a commutative semiring `R` at a submonoid `M`:

* `IsLocalization.subsingleton_addUnits`: a localization of a commutative semiring in which sums
  vanish only when every summand does inherits this property.
* `IsLocalization.lift_injective_of_injective`: if an injective ring homomorphism `g : R →+* P`
  maps `M` into the units of `P`, then its lift `IsLocalization.lift hg : S →+* P` is injective
  (complementing Mathlib's `IsLocalization.lift_injective_iff` and `IsLocalization.eq_of_eq`).
* `IsLocalization.map_injective_of_injective_of_le_nonZeroDivisors`: an injective ring homomorphism
  of commutative rings carrying `M` into a submonoid of non-zero-divisors induces an injective map
  of localizations, with no domain hypothesis (for instance, on total rings of fractions).
* `TauCeti.IsLocalization.le_nonZeroDivisors_of_nontrivial`: a submonoid along which a semiring
  without zero divisors localizes to a nontrivial semiring consists of non-zero-divisors.
* `TauCeti.IsLocalization.isUnit_mk'_iff` and `TauCeti.Localization.isUnit_mk_iff`: a fraction
  `a / m` (`m ∈ M`) is a unit in `S` (or `Localization M`) if and only if `algebraMap R S a` is a
  unit, since `m` already maps to a unit.
-/

public section

namespace IsLocalization

/-- A localization of a commutative semiring in which sums vanish only when every summand does
has the same property. -/
theorem subsingleton_addUnits {R : Type*} [CommSemiring R] (M : Submonoid R) (S : Type*)
    [CommSemiring S] [Algebra R S] [IsLocalization M S] [Subsingleton (AddUnits R)] :
    Subsingleton (AddUnits S) :=
  Subsingleton.addUnits_of_isAddUnit fun a ha ↦ by
    obtain ⟨b, h⟩ := ha.exists_neg
    obtain ⟨⟨r, s⟩, rfl⟩ := mk'_surjective M a
    obtain ⟨⟨u, v⟩, rfl⟩ := mk'_surjective M b
    rw [← mk'_add, mk'_eq_zero_iff] at h
    obtain ⟨m, hm⟩ := h
    rw [mul_add, add_eq_zero] at hm
    exact (mk'_eq_zero_iff (S := S) r s).mpr
      ⟨m * v, by simpa [mul_assoc, mul_comm (v : R)] using hm.1⟩

section Lift

variable {R : Type*} [CommSemiring R] {M : Submonoid R} {S : Type*} [CommSemiring S]
  [Algebra R S] [IsLocalization M S] {P : Type*} [CommSemiring P] {g : R →+* P}

/-- If an injective ring homomorphism `g : R →+* P` sends every element of `M` to a unit, then its
lift `S →+* P` out of a localization `S` of `R` at `M` is injective. -/
theorem lift_injective_of_injective (hg : ∀ y : M, IsUnit (g y)) (hinj : Function.Injective g) :
    Function.Injective (lift (M := M) (S := S) hg) :=
  (lift_injective_iff hg).mpr fun _ _ ↦
    ⟨eq_of_eq (S := S) hg, fun h ↦ congrArg (algebraMap R S) (hinj h)⟩

end Lift

open scoped nonZeroDivisors

/-- Let `f : R →+* S` be injective, carrying a submonoid `M` into a submonoid `T` of
non-zero-divisors of `S`. Then the induced map from the localization of `R` at `M` to that of `S`
at `T` is injective. Unlike `IsLocalization.map_injective_of_injective'`, `S` need not be a domain;
the main case is the induced map of total quotient rings, `M = R⁰` and `T = S⁰`. -/
theorem map_injective_of_injective_of_le_nonZeroDivisors {R S : Type*} [CommRing R] [CommRing S]
    {M : Submonoid R} {T : Submonoid S} (Rₘ Sₘ : Type*) [CommRing Rₘ] [CommRing Sₘ]
    [Algebra R Rₘ] [Algebra S Sₘ] [IsLocalization M Rₘ] [IsLocalization T Sₘ] {f : R →+* S}
    (hf : Function.Injective f) (hMT : M ≤ T.comap f) (hT : T ≤ S⁰) :
    Function.Injective (map Sₘ f hMT : Rₘ →+* Sₘ) :=
  injective_of_map_algebraMap_zero (M := M) Rₘ _ fun x hx ↦ by
    rw [map_eq, to_map_eq_zero_iff Sₘ hT, _root_.map_eq_zero_iff f hf] at hx
    rw [hx, map_zero]

end IsLocalization

namespace TauCeti.IsLocalization

open _root_.IsLocalization

/-- A submonoid of a commutative semiring without zero divisors along which the semiring localizes
to a nontrivial semiring consists of non-zero-divisors. -/
theorem le_nonZeroDivisors_of_nontrivial {R : Type*} [CommSemiring R] [NoZeroDivisors R]
    (M : Submonoid R) (S : Type*) [CommSemiring S] [Nontrivial S] [Algebra R S]
    [IsLocalization M S] : M ≤ nonZeroDivisors R :=
  le_nonZeroDivisors_of_noZeroDivisors fun h ↦
    not_subsingleton S (_root_.IsLocalization.subsingleton h)

variable {R : Type*} [CommSemiring R] {M : Submonoid R} {S : Type*} [CommSemiring S]
  [Algebra R S] [IsLocalization M S]

/-- A fraction `IsLocalization.mk' S x y` is a unit in `S` if and only if its numerator `x` maps to
a unit in `S`. -/
@[simp]
theorem isUnit_mk'_iff {x : R} {y : M} :
    IsUnit (mk' S x y) ↔ IsUnit (algebraMap R S x) :=
  ⟨fun h ↦ mk'_spec S x y ▸ h.mul (map_units S y),
    fun h ↦ isUnit_of_dvd_unit ⟨algebraMap R S y, (mk'_spec S x y).symm⟩ h⟩

end TauCeti.IsLocalization

namespace TauCeti.Localization

open _root_.Localization

variable {R : Type*} [CommSemiring R] {M : Submonoid R}

/-- A fraction `Localization.mk x y` is a unit in `Localization M` if and only if `x` maps to a unit
in `Localization M`. -/
@[simp]
theorem isUnit_mk_iff {x : R} {y : M} :
    IsUnit (mk x y) ↔ IsUnit (algebraMap R (_root_.Localization M) x) := by
  rw [mk_eq_mk'_apply, TauCeti.IsLocalization.isUnit_mk'_iff]

end TauCeti.Localization
