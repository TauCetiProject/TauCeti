/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.LocalizationLocalization

/-!
# The localization of a domain away from a nonzero element, inside a fraction field

Let `R` be a domain with fraction field `K` and let `f` be a nonzero element of `R`. The
localization `Localization.Away f` embeds in `K`, and `K` is again its fraction field. This is the
analogue for `Localization.Away` of `TauCeti/RingTheory/Localization/AtPrime.lean`, built the same
way from `IsLocalization.localizationAlgebraOfSubmonoidLe`, here for the inequality
`powers_le_nonZeroDivisors_of_noZeroDivisors`.

Unlike the prime case, the construction needs the hypothesis `f ≠ 0` (for `f = 0` the
localization is the zero ring, which has no map to a field), so the declarations below are a
`def` and theorems about it rather than global instances. A consumer installs them locally.

## Main declarations

* `Localization.Away.algebraOfIsFractionRing : Algebra (Localization.Away f) K`, the lift of
  `algebraMap R K` along the localization;
* `Localization.Away.isScalarTower_of_isFractionRing : IsScalarTower R (Localization.Away f) K`,
  saying that lift extends `algebraMap R K`;
* `Localization.Away.isFractionRing : IsFractionRing (Localization.Away f) K`.
-/

public section

namespace Localization.Away

variable {R : Type*} [CommRing R] [IsDomain R] (K : Type*) [Field K] [Algebra R K]
  [IsFractionRing R K] {f : R}

/-- For a nonzero `f` in a domain `R`, the localization `R_f` maps to any fraction field `K` of
`R`: the `Algebra` structure lifting `algebraMap R K`, which inverts the powers of `f` because they
are nonzero. -/
noncomputable abbrev algebraOfIsFractionRing (hf : f ≠ 0) : Algebra (Localization.Away f) K :=
  IsLocalization.localizationAlgebraOfSubmonoidLe _ _ _ _
    (powers_le_nonZeroDivisors_of_noZeroDivisors hf)

/-- The map `algebraOfIsFractionRing` from `R_f` to a fraction field `K` of `R` extends
`algebraMap R K`. -/
theorem isScalarTower_of_isFractionRing (hf : f ≠ 0) :
    letI := algebraOfIsFractionRing K hf
    IsScalarTower R (Localization.Away f) K :=
  IsLocalization.localization_isScalarTower_of_submonoid_le _ _ _ _ _

/-- Along `algebraOfIsFractionRing`, a fraction field `K` of a domain `R` is a fraction field of
the localization `R_f` away from a nonzero `f`. -/
theorem isFractionRing (hf : f ≠ 0) :
    letI := algebraOfIsFractionRing K hf
    IsFractionRing (Localization.Away f) K :=
  letI := algebraOfIsFractionRing K hf
  haveI := isScalarTower_of_isFractionRing K hf
  IsFractionRing.isFractionRing_of_isLocalization (.powers f) _ _
    (powers_le_nonZeroDivisors_of_noZeroDivisors hf)

end Localization.Away

end
