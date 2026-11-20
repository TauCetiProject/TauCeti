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
fraction field of the domain itself. The non-zero-divisor hypothesis holds whenever a domain is
localized to a nontrivial ring (`TauCeti.IsLocalization.le_nonZeroDivisors_of_nontrivial`, in
`TauCeti.RingTheory.Localization.Defs`).

An injective ring homomorphism that carries non-zero-divisors to non-zero-divisors induces an
injective map of total rings of fractions
(`IsLocalization.map_injective_of_injective_of_le_nonZeroDivisors`), with no domain hypothesis.
-/

public section

namespace IsLocalization

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
