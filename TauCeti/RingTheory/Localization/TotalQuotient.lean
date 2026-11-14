/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.Basic
public import Mathlib.Algebra.Field.IsField
public import TauCeti.Algebra.Regular.Submonoid

/-!
# Total quotients of commutative semirings

The total quotient semiring inverts the elements whose multiplication is injective. For
commutative rings these are the non-zero-divisors; for a general semiring the two conditions need
not coincide. Regular localization preserves zero-sum-freeness, and the total quotient of a
semiring domain is a semifield.
-/

public section

noncomputable section

namespace TauCeti

/-- The localization of a commutative semiring at all its regular elements. -/
abbrev TotalQuotient (R : Type*) [CommSemiring R] := Localization (regularElements R)

namespace IsLocalization

variable {R : Type*} [CommSemiring R] {M : Submonoid R}

/-- The canonical map into a regular localization is injective. -/
theorem algebraMap_injective_of_isRegular (L : Type*) {M : Submonoid R} [CommSemiring L]
    [Algebra R L] [IsLocalization M L] (hM : ∀ m ∈ M, IsRegular m) :
    Function.Injective (algebraMap R L) := IsLocalization.injectiveₛ L hM

variable {L : Type*} [CommSemiring L] [Algebra R L] [IsLocalization M L]

/-- A fraction in a regular localization vanishes exactly when its numerator vanishes. -/
@[simp]
theorem mk'_eq_zero_iff_eq_zero (hM : ∀ m ∈ M, IsRegular m) (r : R) (s : M) :
    IsLocalization.mk' L r s = 0 ↔ r = 0 := by
  constructor
  · intro h
    apply algebraMap_injective_of_isRegular L hM
    rw [← IsLocalization.mk'_spec L r s, h, zero_mul, map_zero]
  · rintro rfl
    exact IsLocalization.mk'_zero _

/-- A map to a division semiring evaluates a fraction by dividing the images of its components. -/
theorem map_mk'_eq_div {S : Type*} [DivisionSemiring S] (f : L →+* S) (r : R) (s : M) :
    f (IsLocalization.mk' L r s) = f (algebraMap R L r) / f (algebraMap R L s) := by
  have hs : IsUnit (f (algebraMap R L s)) := (IsLocalization.map_units L s).map f
  exact (eq_div_iff hs.ne_zero).mpr (by
    simpa only [map_mul] using congrArg f (IsLocalization.mk'_spec L r s))

/-- Localization at regular denominators preserves zero-sum-freeness. -/
theorem subsingleton_addUnits (hM : ∀ m ∈ M, IsRegular m) [Subsingleton (AddUnits R)] :
    Subsingleton (AddUnits L) :=
  Subsingleton.addUnits_of_isAddUnit fun a ha => by
    obtain ⟨b, h⟩ := ha.exists_neg
    obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective M a
    obtain ⟨⟨u, v⟩, rfl⟩ := IsLocalization.mk'_surjective M b
    rw [← IsLocalization.mk'_add, mk'_eq_zero_iff_eq_zero hM] at h
    exact (mk'_eq_zero_iff_eq_zero hM r s).mpr
      ((hM (v : R) v.2).right (by simpa using (add_eq_zero.mp h).1))

/-- A regular localization of a semiring domain is a semifield. -/
theorem isField (L : Type*) [CommSemiring L] [Algebra R L]
    [IsLocalization (regularElements R) L] [IsDomain R] : IsField L where
  exists_pair_ne := ⟨algebraMap R _ 0, algebraMap R _ 1,
    fun h => zero_ne_one
      (algebraMap_injective_of_isRegular L (fun _ hr => mem_regularElements.mp hr) h)⟩
  mul_comm := mul_comm
  mul_inv_cancel {a} ha := by
    obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective (regularElements R) a
    have hr : IsRegular r := IsRegular.of_ne_zero (IsLocalization.ne_zero_of_mk'_ne_zero ha)
    have hr' : r ∈ regularElements R := mem_regularElements.mpr hr
    exact ⟨IsLocalization.mk' _ (s : R) ⟨r, hr'⟩, IsLocalization.mk'_mul_mk'_eq_one' r s hr'⟩

end IsLocalization

namespace TotalQuotient

variable {R : Type*} [CommSemiring R]

/-- The canonical map into the total quotient is injective. -/
theorem algebraMap_injective (R : Type*) [CommSemiring R] :
    Function.Injective (algebraMap R (TotalQuotient R)) :=
  IsLocalization.algebraMap_injective_of_isRegular _ fun _ hr => mem_regularElements.mp hr

/-- Total quotient localization is faithful over its base semiring. -/
instance : FaithfulSMul R (TotalQuotient R) :=
  (faithfulSMul_iff_algebraMap_injective R _).mpr (algebraMap_injective R)

/-- A total quotient is nontrivial whenever its base is nontrivial. -/
instance [Nontrivial R] : Nontrivial (TotalQuotient R) := (algebraMap_injective R).nontrivial

/-- A fraction in the total quotient vanishes precisely when its numerator vanishes. -/
theorem mk'_eq_zero_iff (r : R) (s : regularElements R) :
    IsLocalization.mk' (TotalQuotient R) r s = 0 ↔ r = 0 :=
  IsLocalization.mk'_eq_zero_iff_eq_zero (fun _ hr => mem_regularElements.mp hr) r s

/-- A map to a division semiring evaluates a total-quotient fraction by dividing the images of
its numerator and denominator. -/
theorem map_mk'_eq_div {S : Type*} [DivisionSemiring S] (f : TotalQuotient R →+* S)
    (r : R) (s : regularElements R) :
    f (IsLocalization.mk' (TotalQuotient R) r s) =
      f (algebraMap R (TotalQuotient R) r) / f (algebraMap R (TotalQuotient R) s) :=
  IsLocalization.map_mk'_eq_div f r s

/-- The total quotient of a semiring domain is a semifield. -/
instance [IsDomain R] : Semifield (TotalQuotient R) :=
  (IsLocalization.isField (R := R) (TotalQuotient R)).toSemifield

/-- Regular localization preserves zero-sum-freeness. -/
instance [Subsingleton (AddUnits R)] : Subsingleton (AddUnits (TotalQuotient R)) :=
  IsLocalization.subsingleton_addUnits (R := R) fun _ hr => mem_regularElements.mp hr

end TotalQuotient

end TauCeti
