/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing

/-!
# The valuation of a discrete valuation ring on its own elements

Let `R` be a discrete valuation ring with fraction field `K`, and let `v` be the valuation on `K`
attached to the maximal ideal of `R` (`IsDiscreteValuationRing.maximalIdeal`). Mathlib's
`IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem` reads `v r < 1`, for `r : R`, as
membership in the ideal underlying that height-one prime. This file restates it with the local
ring's maximal ideal, and with divisibility by a uniformiser.

## Main results

* `TauCeti.IsDiscreteValuationRing.valuation_algebraMap_lt_one_iff_mem`: `v r < 1` exactly when
  `r` lies in the maximal ideal.
* `Irreducible.valuation_algebraMap_lt_one_iff_dvd` and
  `Irreducible.valuation_algebraMap_eq_one_iff_not_dvd`: for a uniformiser `ϖ`, `v r < 1` exactly
  when `ϖ ∣ r`, and `v r = 1` exactly when `ϖ ∤ r`.
-/

public section

open IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

namespace TauCeti.IsDiscreteValuationRing

/-- An element of a discrete valuation ring has valuation less than one in the fraction field
exactly when it lies in the maximal ideal. -/
theorem valuation_algebraMap_lt_one_iff_mem (r : R) :
    valuation K (_root_.IsDiscreteValuationRing.maximalIdeal R) (algebraMap R K r) < 1 ↔
      r ∈ IsLocalRing.maximalIdeal R :=
  -- `(maximalIdeal R).asIdeal` is by definition `IsLocalRing.maximalIdeal R`
  valuation_lt_one_iff_mem _ r

end TauCeti.IsDiscreteValuationRing

namespace Irreducible

variable {K} {ϖ : R}

/-- An element of a discrete valuation ring has valuation less than one in the fraction field
exactly when the uniformiser divides it. -/
theorem valuation_algebraMap_lt_one_iff_dvd (hϖ : Irreducible ϖ) (r : R) :
    valuation K (IsDiscreteValuationRing.maximalIdeal R) (algebraMap R K r) < 1 ↔ ϖ ∣ r := by
  rw [TauCeti.IsDiscreteValuationRing.valuation_algebraMap_lt_one_iff_mem, hϖ.maximalIdeal_eq,
    Ideal.mem_span_singleton]

/-- An element of a discrete valuation ring has valuation one in the fraction field exactly when
the uniformiser does not divide it. -/
theorem valuation_algebraMap_eq_one_iff_not_dvd (hϖ : Irreducible ϖ) (r : R) :
    valuation K (IsDiscreteValuationRing.maximalIdeal R) (algebraMap R K r) = 1 ↔ ¬ ϖ ∣ r := by
  rw [← hϖ.valuation_algebraMap_lt_one_iff_dvd (K := K),
    (valuation_le_one (K := K) _ r).lt_iff_ne, not_not]

end Irreducible
