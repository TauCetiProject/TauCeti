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
localized to a nontrivial ring (`TauCeti.IsLocalization.le_nonZeroDivisors_of_nontrivial`).

When every positive integer is a non-zero-divisor of `R`, every quotient of a total ring of
fractions of `R` by a proper ideal has characteristic zero (`IsFractionRing.charZero_quotient`).
-/

public section

namespace TauCeti.IsLocalization

/-- A submonoid of a ring without zero divisors along which the ring localizes to a nontrivial
ring consists of non-zero-divisors. -/
theorem le_nonZeroDivisors_of_nontrivial {R : Type*} [CommRing R] [NoZeroDivisors R]
    (M : Submonoid R) (S : Type*) [CommRing S] [Nontrivial S] [Algebra R S] [IsLocalization M S] :
    M ≤ nonZeroDivisors R :=
  le_nonZeroDivisors_of_noZeroDivisors fun h ↦
    not_subsingleton S (_root_.IsLocalization.subsingleton h)

end TauCeti.IsLocalization

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

namespace IsFractionRing

open scoped nonZeroDivisors

variable (A K : Type*) [CommRing A] [CommRing K] [Algebra A K] [IsFractionRing A K]

/-- If every positive integer is a non-zero-divisor of `A`, then every quotient of the total
quotient ring of `A` by a proper ideal has characteristic zero. -/
theorem charZero_quotient (h : ∀ n : ℕ, n ≠ 0 → (n : A) ∈ A⁰) {I : Ideal K} (hI : I ≠ ⊤) :
    CharZero (K ⧸ I) := by
  refine charZero_of_inj_zero fun n hn ↦ ?_
  by_contra h0
  have hu : IsUnit (n : K) := by
    simpa using IsLocalization.map_units K ⟨(n : A), h n h0⟩
  have := Ideal.Quotient.nontrivial_iff.mpr hI
  exact (hu.map (Ideal.Quotient.mk I)).ne_zero (by simpa using hn)

end IsFractionRing
