/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients.Basic

/-!
# Residue fields at height-one primes and adic valuation rings

In a commutative ring `R` with finite quotients, every height-one prime `v` has a finite residue
ring `R ⧸ v.asIdeal`. When `R` is a Dedekind domain with fraction field `K`, the valuation ring of
`K` at `v` is a local ring whose residue field has the same characteristic as `R ⧸ v`: a natural
number vanishes in it exactly when its image in `R` lies in `v`.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.finite_quotient_asIdeal`: when `R` has finite quotients,
  every height-one prime `v` of `R` has finite quotient `R ⧸ v.asIdeal`.
* `IsDedekindDomain.HeightOneSpectrum.natCast_residueField_valuationSubring_eq_zero_iff`: a
  natural number is zero in the residue field of the valuation ring of `K` at `v` exactly when
  it lies in `v`.
-/

public section

namespace IsDedekindDomain.HeightOneSpectrum

/-- In a commutative ring with finite quotients, the quotient by every height-one prime is
finite. -/
instance finite_quotient_asIdeal {R : Type*} [CommRing R] [Ring.HasFiniteQuotients R]
    (v : HeightOneSpectrum R) :
    Finite (R ⧸ v.asIdeal) :=
  Ring.HasFiniteQuotients.finiteQuotient v.ne_bot

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
