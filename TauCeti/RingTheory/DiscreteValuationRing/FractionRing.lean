/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# Fraction fields of discrete valuation rings

This file relates the two natural descriptions of the fraction field of a discrete valuation
ring. Besides being the localization at all non-zero elements, it is the localization away from
any uniformizer. This is what makes the induced map of spectra a principal open immersion.
-/

public section

/-- The fraction field of a discrete valuation ring is the localization away from any
uniformizer. Here uniformizers are expressed using Mathlib's equivalent `Irreducible` predicate.
-/
lemma Irreducible.isLocalizationAway_fractionRing {R K : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [CommSemiring K] [Algebra R K] [IsFractionRing R K]
    {ϖ : R} (hϖ : Irreducible ϖ) : IsLocalization.Away ϖ K :=
  (IsLocalization.iff_of_le_of_exists_dvd _ _
    (powers_le_nonZeroDivisors_of_noZeroDivisors hϖ.ne_zero) fun _ hx ↦
      have ⟨n, hn⟩ :=
        IsDiscreteValuationRing.associated_pow_irreducible (nonZeroDivisors.ne_zero hx) hϖ
      ⟨ϖ ^ n, pow_mem (Submonoid.mem_powers ϖ) n, hn.dvd⟩).mpr inferInstance
