/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.LocalizationLocalization

/-!
# Localizing a prime that survives in a localization

Let `S` be a localization of `R` at a submonoid `M`, and let `q` be a prime of `R` disjoint from
`M`. Then `q S` is a prime of `S` lying over `q`, and the localization of `R` at `q` is the
localization of `S` at `q S`. Mathlib records the converse direction, starting from a prime of
`S`, as `IsLocalization.isLocalization_isLocalization_atPrime_isLocalization` and
`IsLocalization.localizationLocalizationAtPrimeIsoLocalization`.

## Main results

* `IsLocalization.exists_ringEquiv_localization_atPrime`: for a prime `q` of `R` disjoint from
  `M`, there is a prime `P` of `S` lying over `q` with `R_q ≃+* S_P`.
-/

public section

namespace IsLocalization

variable {R : Type*} [CommSemiring R] (M : Submonoid R) (S : Type*) [CommSemiring S]
  [Algebra R S] [IsLocalization M S]

/-- If `S` is a localization of `R` at `M` and `q` is a prime of `R` disjoint from `M`, then
there is a prime `P` of `S` lying over `q` (namely `q S`) such that `R_q` is isomorphic to
`S_P`. -/
theorem exists_ringEquiv_localization_atPrime (q : Ideal R) [q.IsPrime]
    (hq : Disjoint (M : Set R) q) :
    ∃ (P : Ideal S) (_ : P.IsPrime), P.under R = q ∧
      Nonempty (Localization.AtPrime q ≃+* Localization.AtPrime P) := by
  let P := q.map (algebraMap R S)
  have : P.IsPrime := isPrime_of_isPrime_disjoint M S q ‹_› hq
  have hP : P.under R = q := under_map_of_isPrime_disjoint M S ‹_› hq
  -- `convert` is needed because the prime `P.under R` carries its own `IsPrime` instance.
  have : IsLocalization.AtPrime (Localization.AtPrime P) q := by
    convert isLocalization_isLocalization_atPrime_isLocalization M (Localization.AtPrime P) P
    exact hP.symm
  exact ⟨P, inferInstance, hP, ⟨(algEquiv q.primeCompl _ _).toRingEquiv⟩⟩

end IsLocalization
