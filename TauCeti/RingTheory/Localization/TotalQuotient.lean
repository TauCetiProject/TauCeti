/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.Basic
public import Mathlib.Algebra.Field.IsField
public import TauCeti.Algebra.Group.Units.ZeroSumFree

/-!
# Total quotients of commutative semirings

The total quotient semiring inverts the elements whose multiplication is injective.
For commutative rings these are the non-zero-divisors; for a general semiring
the two conditions need not coincide.
-/

public section

noncomputable section

namespace TauCeti

variable (R : Type*) [CommSemiring R]

/-- The multiplicatively cancellable elements of a commutative semiring. -/
def regularElements : Submonoid R where
  carrier := {r | IsRegular r}
  one_mem' := isRegular_one
  mul_mem' ha hb := ha.mul hb

@[simp]
theorem mem_regularElements {r : R} : r ∈ regularElements R ↔ IsRegular r := (Iff.rfl)

/-- In a semiring domain the denominators are exactly the nonzero elements. -/
theorem mem_regularElements_iff_ne_zero [IsDomain R] {r : R} :
    r ∈ regularElements R ↔ r ≠ 0 :=
  isRegular_iff_ne_zero

/-- The localization of a commutative semiring at all its regular elements. -/
abbrev TotalQuotient := Localization (regularElements R)

namespace TotalQuotient

/-- The canonical map into the total quotient is injective. -/
theorem algebraMap_injective : Function.Injective (algebraMap R (TotalQuotient R)) :=
  IsLocalization.injectiveₛ (M := regularElements R) _ (fun _ hr => hr)

variable {R}

@[simp]
theorem mk'_eq_zero_iff (r : R) (s : regularElements R) :
    IsLocalization.mk' (TotalQuotient R) r s = 0 ↔ r = 0 := by
  constructor
  · intro h
    apply algebraMap_injective R
    rw [← IsLocalization.mk'_spec (TotalQuotient R) r s, h, zero_mul, map_zero]
  · rintro rfl
    exact IsLocalization.mk'_zero _

/-- A map to a semifield evaluates a fraction by dividing the images of its components. -/
theorem map_mk'_eq_div {S : Type*} [Semifield S] (f : TotalQuotient R →+* S)
    (r : R) (s : regularElements R) :
    f (IsLocalization.mk' (TotalQuotient R) r s) =
      f (algebraMap R (TotalQuotient R) r) / f (algebraMap R (TotalQuotient R) s) := by
  have hs : IsUnit (f (algebraMap R (TotalQuotient R) s)) :=
    (IsLocalization.map_units (TotalQuotient R) s).map f
  exact (eq_div_iff hs.ne_zero).mpr (by
    simpa only [map_mul] using congrArg f (IsLocalization.mk'_spec (TotalQuotient R) r s))

/-- Every nonzero fraction in the total quotient of a semiring domain is invertible. -/
theorem isField [IsDomain R] : IsField (TotalQuotient R) where
  exists_pair_ne := ⟨algebraMap R _ 0, algebraMap R _ 1,
    fun h => zero_ne_one (algebraMap_injective R h)⟩
  mul_comm := mul_comm
  mul_inv_cancel {a} ha := by
    obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective (regularElements R) a
    have hr : IsRegular r := IsRegular.of_ne_zero (IsLocalization.ne_zero_of_mk'_ne_zero ha)
    exact ⟨IsLocalization.mk' _ (s : R) ⟨r, hr⟩, IsLocalization.mk'_mul_mk'_eq_one' r s hr⟩

/-- The total quotient of a semiring domain is a semifield. -/
instance [IsDomain R] : Semifield (TotalQuotient R) := isField.toSemifield

/-- Regular localization preserves zero-sum-freeness. -/
instance [Subsingleton (AddUnits R)] : Subsingleton (AddUnits (TotalQuotient R)) :=
  Subsingleton.addUnits_of_isAddUnit fun a ha => by
    obtain ⟨b, h⟩ := ha.exists_neg
    obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective (regularElements R) a
    obtain ⟨⟨u, v⟩, rfl⟩ := IsLocalization.mk'_surjective (regularElements R) b
    rw [← IsLocalization.mk'_add, mk'_eq_zero_iff] at h
    exact (mk'_eq_zero_iff r s).mpr (v.property.right (by simpa using (add_eq_zero.mp h).1))

end TotalQuotient

end TauCeti
