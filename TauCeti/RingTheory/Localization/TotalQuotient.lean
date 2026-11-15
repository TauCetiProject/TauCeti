/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Field.IsField
public import Mathlib.RingTheory.Localization.Defs
public import TauCeti.Algebra.Regular.Submonoid

/-!
# Total quotients of commutative semirings

The total quotient `TauCeti.TotalQuotient R` of a commutative semiring `R` is its localization at
the submonoid `TauCeti.regulars R` of regular elements. The canonical map from `R` is injective,
and Mathlib's `IsLocalization` API supplies the universal property: a semiring map out of `R`
extends to the total quotient, necessarily uniquely, exactly when it sends regular elements to
units (`IsLocalization.lift`, `IsLocalization.ringHom_ext` and `IsLocalization.isUnit_comp`).

For a commutative ring the regular elements are the non-zero-divisors
(`TauCeti.regulars_eq_nonZeroDivisors`), so the total quotient is Mathlib's `FractionRing`. For
semirings the two submonoids can differ, and this localization is the one that keeps `R` inside.

Any localization of a commutative semiring in which sums vanish only when every summand does
inherits this property (`IsLocalization.subsingleton_addUnits`). The total quotient of a
semiring domain is a semifield, in which a fraction is the quotient of its numerator by its
denominator.
-/

public section

noncomputable section

open scoped nonZeroDivisors

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

end IsLocalization

namespace TauCeti

/-- The total quotient of a commutative semiring: its localization at all regular elements. -/
abbrev TotalQuotient (R : Type*) [CommSemiring R] := Localization (regulars R)

namespace TotalQuotient

variable {R : Type*} [CommSemiring R]

/-- A commutative semiring embeds in its total quotient. -/
instance : FaithfulSMul R (TotalQuotient R) :=
  (faithfulSMul_iff_algebraMap_injective R _).mpr <|
    IsLocalization.injectiveₛ _ fun _ ↦ mem_regulars.mp

/-- The total quotient inherits zero-sum-freeness. -/
instance [Subsingleton (AddUnits R)] : Subsingleton (AddUnits (TotalQuotient R)) :=
  IsLocalization.subsingleton_addUnits (regulars R) _

/-- The total quotient of a semiring domain is a field. -/
theorem isField [IsDomain R] : IsField (TotalQuotient R) where
  exists_pair_ne := ⟨0, 1, fun h ↦ zero_ne_one <|
    FaithfulSMul.algebraMap_injective R (TotalQuotient R) (by simpa using h)⟩
  mul_comm := mul_comm
  mul_inv_cancel {a} ha := by
    obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective (regulars R) a
    have hr : r ∈ regulars R :=
      mem_regulars_iff_ne_zero.mpr (IsLocalization.ne_zero_of_mk'_ne_zero ha)
    exact ⟨IsLocalization.mk' _ (s : R) ⟨r, hr⟩, IsLocalization.mk'_mul_mk'_eq_one' r s hr⟩

/-- The total quotient of a semiring domain is a semifield. -/
instance [IsDomain R] : Semifield (TotalQuotient R) :=
  isField.toSemifield

/-- In the total quotient of a semiring domain, a fraction is the quotient of the images of its
numerator and denominator. -/
theorem mk'_eq_div [IsDomain R] (r : R) (s : regulars R) :
    IsLocalization.mk' (TotalQuotient R) r s =
      algebraMap R (TotalQuotient R) r / algebraMap R (TotalQuotient R) s := by
  rw [eq_div_iff (IsLocalization.map_units _ s).ne_zero, IsLocalization.mk'_spec]

end TotalQuotient

end TauCeti
