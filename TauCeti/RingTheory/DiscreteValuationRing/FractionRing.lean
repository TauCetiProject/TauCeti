/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.FractionRing
import TauCeti.RingTheory.Localization.TensorProduct

/-!
# Fraction fields of discrete valuation rings

This file relates the two natural descriptions of the fraction field of a discrete valuation
ring. Besides being the localization at all non-zero elements, it is the localization away from
any uniformizer (`Irreducible.isLocalizationAway_fractionRing`). Consequently, any pushout of an
algebra `A` along `R → K` is the localization of `A` away from the image of any uniformizer
(`Irreducible.isLocalizationAway_of_isPushout`).
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

/-- Any pushout `B` of an algebra `A` over a discrete valuation ring `R` along its fraction field
`K` is the localization of `A` away from the image of any uniformizer `ϖ` of `R`. -/
lemma Irreducible.isLocalizationAway_of_isPushout {R K A B : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [CommSemiring K] [Algebra R K] [IsFractionRing R K]
    [CommSemiring A] [CommSemiring B] [Algebra R A] [Algebra R B] [Algebra A B] [Algebra K B]
    [IsScalarTower R A B] [IsScalarTower R K B] [Algebra.IsPushout R A K B]
    {ϖ : R} (hϖ : Irreducible ϖ) :
    IsLocalization.Away (algebraMap R A ϖ) B := by
  have : IsLocalization.Away ϖ K := hϖ.isLocalizationAway_fractionRing
  exact (Algebra.isLocalization_away_iff_isPushout (A := K) ϖ).mpr inferInstance
