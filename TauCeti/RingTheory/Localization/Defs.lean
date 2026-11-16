/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.Defs

/-!
# Basic facts about localizations of commutative semirings

For a localization `S` of a commutative semiring `R` at a submonoid `M`, a ring homomorphism
`g : R →+* P` that maps `M` into the units of `P` extends to `IsLocalization.lift hg : S →+* P`.
Complementing Mathlib's `IsLocalization.lift_injective_iff` and `IsLocalization.eq_of_eq`, this file
records that `IsLocalization.lift hg` is injective whenever `g` is injective
(`IsLocalization.lift_injective_of_injective`).

It also records that a localization of a commutative semiring in which sums vanish only when
every summand does inherits this property (`IsLocalization.subsingleton_addUnits`).
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

variable {R : Type*} [CommSemiring R] {M : Submonoid R} {S : Type*} [CommSemiring S]
  [Algebra R S] [IsLocalization M S] {P : Type*} [CommSemiring P] {g : R →+* P}

/-- If an injective ring homomorphism `g : R →+* P` sends every element of `M` to a unit, then its
lift `S →+* P` out of a localization `S` of `R` at `M` is injective. -/
theorem lift_injective_of_injective (hg : ∀ y : M, IsUnit (g y)) (hinj : Function.Injective g) :
    Function.Injective (lift (M := M) (S := S) hg) :=
  (lift_injective_iff hg).mpr fun _ _ ↦
    ⟨eq_of_eq (S := S) hg, fun h ↦ congrArg (algebraMap R S) (hinj h)⟩

end IsLocalization
