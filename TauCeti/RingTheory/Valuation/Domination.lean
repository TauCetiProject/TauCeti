/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.Valuation.LocalSubring

/-!
# Valuation subrings dominating a prime

Let `φ : R →+* L` be a ring map to a field and `𝔭` a prime ideal of `R` containing the kernel of
`φ`. The image of `R` localised at the image of `𝔭` is a local subring of `L`, and a valuation
subring `V` dominating it (`LocalSubring.exists_le_valuationSubring`) contains `φ(R)` and has
exactly `𝔭` as the preimage of its nonunits
(`RingHom.exists_valuationSubring_mem_and_mem_nonunits_iff`).

This is the classical construction of a valuation with prescribed centre. Pulled back to `R`, the
valuation of `V` is bounded by `1`, vanishes exactly on the kernel of `φ` and is below `1` exactly
on `𝔭`. With `φ` the map to a residue field of a valuation ring, it gives the composite
valuations realising specializations in valuation spectra.

## Main results

* `RingHom.exists_valuationSubring_mem_and_mem_nonunits_iff`: some valuation subring of `L`
  contains `φ(R)`, and `φ r` is a nonunit of it exactly when `r ∈ 𝔭`.

## References

* [The Stacks Project](https://stacks.math.columbia.edu/tag/00IA), Tag 00IA: every local subring
  of a field is dominated by a valuation subring.
-/

public section

namespace RingHom

/-- **A valuation subring dominating a prime.** Let `φ : R →+* L` be a ring map to a field and
`𝔭` a prime ideal of `R` containing the kernel of `φ`. Some valuation subring `V` of `L` contains
`φ(R)`, and `φ r` is a nonunit of `V` exactly when `r ∈ 𝔭`. -/
theorem exists_valuationSubring_mem_and_mem_nonunits_iff {R L : Type*} [CommRing R] [Field L]
    (φ : R →+* L) (𝔭 : Ideal R) [𝔭.IsPrime] (hker : RingHom.ker φ ≤ 𝔭) :
    ∃ V : ValuationSubring L, (∀ r, φ r ∈ V) ∧ ∀ r, φ r ∈ V.nonunits ↔ r ∈ 𝔭 := by
  -- the image `P` of `𝔭` in the range of `φ` is prime, and pulls back to `𝔭`
  have hφ : Function.Surjective φ.rangeRestrict := φ.rangeRestrict_surjective
  have hker' : RingHom.ker φ.rangeRestrict ≤ 𝔭 := by rwa [RingHom.ker_rangeRestrict]
  let P : Ideal φ.range := 𝔭.map φ.rangeRestrict
  have : P.IsPrime := Ideal.map_isPrime_of_surjective hφ hker'
  have hP (r : R) : φ.rangeRestrict r ∈ P ↔ r ∈ 𝔭 := by
    rw [← Ideal.mem_comap, Ideal.comap_map_of_surjective' _ hφ, sup_eq_left.mpr hker']
  -- a valuation subring `V` dominating the localisation of the range of `φ` at `P`
  obtain ⟨V, hle, hloc⟩ := (LocalSubring.ofPrime φ.range P).exists_le_valuationSubring
  have hmem (r : R) : φ r ∈ V := hle (LocalSubring.le_ofPrime _ _ (φ.rangeRestrict r).property)
  -- domination: `φ r` is a unit of `V` exactly when `r ∉ 𝔭`
  have hunit (r : R) : IsUnit (⟨φ r, hmem r⟩ : V) ↔ r ∉ 𝔭 := by
    rw [← hP, ← Ideal.mem_primeCompl_iff, ← IsLocalization.AtPrime.isUnit_to_map_iff
      (LocalSubring.ofPrime φ.range P).toSubring P, ← isUnit_map_iff (Subring.inclusion hle)]
    -- both elements of `V` have underlying element `φ r` of `L`
    rfl
  refine ⟨V, hmem, fun r ↦ ?_⟩
  rw [ValuationSubring.coe_mem_nonunits_iff (a := ⟨φ r, hmem r⟩), IsLocalRing.mem_maximalIdeal,
    mem_nonunits_iff, hunit, not_not]

end RingHom
