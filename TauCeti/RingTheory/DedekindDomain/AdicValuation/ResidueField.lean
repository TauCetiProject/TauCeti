/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation

/-!
# Natural numbers in the residue field of an adic valuation ring

Let `R` be a Dedekind domain with fraction field `K`, and let `v` be a height one prime of `R`.
The valuation ring of `K` at `v` is a local ring whose residue field has the same characteristic
as `R ⧸ v`: a natural number vanishes in it exactly when its image in `R` lies in `v`.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.natCast_residueField_valuationSubring_eq_zero_iff`: a
  natural number is zero in the residue field of the valuation ring of `K` at `v` exactly when
  it lies in `v`.
-/

public section

namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- A natural number is zero in the residue field of the valuation ring of `K` at `v` exactly
when its image in `R` lies in `v`. -/
theorem natCast_residueField_valuationSubring_eq_zero_iff (v : HeightOneSpectrum R) (n : ℕ) :
    (n : IsLocalRing.ResidueField (v.valuation K).valuationSubring) = 0 ↔
      (n : R) ∈ v.asIdeal := by
  rw [← map_natCast (IsLocalRing.residue _), IsLocalRing.residue_eq_zero_iff,
    Valuation.mem_maximalIdeal_iff]
  push_cast
  rw [← map_natCast (algebraMap R K), v.valuation_lt_one_iff_mem]

end IsDedekindDomain.HeightOneSpectrum
