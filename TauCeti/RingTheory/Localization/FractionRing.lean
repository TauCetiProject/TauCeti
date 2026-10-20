/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.LocalizationLocalization

/-!
# A fraction ring of a localization is a fraction ring of the base

Let `S` be the localization of a ring `R` at a submonoid `M` of non-zero-divisors. A total ring
of fractions `T` of `S` is then a total ring of fractions of `R`
(`TauCeti.IsFractionRing.of_isLocalization_of_isFractionRing`). Mathlib proves the converse
direction, from a fraction ring of `R` to one of `S`, as
`IsFractionRing.isFractionRing_of_isLocalization`.
This lets a statement about the fraction field of a localization of a domain be reduced to the
fraction field of the domain itself.
-/

public section

namespace TauCeti.IsFractionRing

variable {R : Type*} [CommRing R] (M : Submonoid R) (S T : Type*) [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

/-- If `S` is the localization of `R` at a submonoid `M` of non-zero-divisors, then a total ring of
fractions of `S` is a total ring of fractions of `R`. -/
theorem of_isLocalization_of_isFractionRing [IsLocalization M S] [IsFractionRing S T]
    (hM : M ≤ nonZeroDivisors R) : IsFractionRing R T := by
  -- `T` is the localization of `R` at the preimage of the non-zero-divisors of `S`, which are
  -- exactly the non-zero-divisors of `R`, since `R ⟶ S` is injective and localization maps
  -- non-zero-divisors to non-zero-divisors
  have := IsLocalization.localization_localization_isLocalization_of_has_all_units M
    (nonZeroDivisors S) T fun _ hx ↦ hx.mem_nonZeroDivisors
  rwa [le_antisymm (comap_nonZeroDivisors_le_of_injective (IsLocalization.injective S hM))
    (IsLocalization.nonZeroDivisors_le_comap M S)] at this

end TauCeti.IsFractionRing
