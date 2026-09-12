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
any uniformizer. This identifies the induced map of spectra with a principal open immersion.
-/

public section

namespace TauCeti

open IsDiscreteValuationRing

/-- The fraction field of a discrete valuation ring is the localization away from any
uniformizer. Here uniformizers are expressed using Mathlib's equivalent `Irreducible` predicate.
-/
lemma Irreducible.isLocalizationAway_fractionRing {R K : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    {ϖ : R} (hϖ : Irreducible ϖ) : IsLocalization.Away ϖ K := by
  refine (IsLocalization.iff_of_le_of_exists_dvd (S := K) (M := Submonoid.powers ϖ)
    (nonZeroDivisors R) (by
      rintro x ⟨n, rfl⟩
      exact pow_mem (mem_nonZeroDivisors_iff_ne_zero.mpr hϖ.ne_zero) n) (by
      rintro x hx
      rw [mem_nonZeroDivisors_iff_ne_zero] at hx
      let hR : HasUnitMulPowIrreducibleFactorization R :=
        .of_ufd_of_unique_irreducible (exists_irreducible R)
          (fun _ _ ha hb ↦ associated_of_irreducible R ha hb)
      obtain ⟨π, hπ, H⟩ := hR
      obtain ⟨n, hn⟩ := H hx
      have hπϖ : Associated π ϖ := associated_of_irreducible R hπ hϖ
      exact ⟨ϖ ^ n, ⟨n, rfl⟩, hn.symm.dvd.trans hπϖ.pow_pow.dvd⟩)).mpr inferInstance

end TauCeti
