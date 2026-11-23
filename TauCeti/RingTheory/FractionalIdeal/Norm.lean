/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.FractionalIdeal.Norm
public import TauCeti.RingTheory.DedekindDomain.Factorization

/-!
# Fractional ideal norms: positivity and prime factorization

Mathlib defines the rational-valued absolute norm `FractionalIdeal.absNorm` on fractional ideals of
a Dedekind domain `R` that is finite free over `ℤ`, and proves `FractionalIdeal.absNorm_nonneg` and
`FractionalIdeal.absNorm_eq_zero_iff`. This file records the corresponding strict positivity
characterization for nonzero fractional ideals.

Combining `FractionalIdeal.finprod_unitOfPrime_zpow_count` with `FractionalIdeal.absNorm` also
expresses `FractionalIdeal.absNorm I` in `ℚ` for any nonzero fractional ideal `I` (and in
particular `|Algebra.norm ℚ a|` for any nonzero `a : K`) as the product over all height-one primes
`v` of `R` of the residue cardinality `Nat.card (R ⧸ v.asIdeal)` raised to the multiplicity at `v`
(see `Ideal.finprod_pow_count_eq_absNorm` for the integral ideal version over an arbitrary Dedekind
domain).

## Main results

* `FractionalIdeal.absNorm_pos_iff`: `0 < FractionalIdeal.absNorm I ↔ I ≠ 0`.
* `FractionalIdeal.absNorm_pos`: `0 < FractionalIdeal.absNorm I` for `I ≠ 0`.
* `FractionalIdeal.finprod_zpow_count_units_eq_absNorm` and
  `FractionalIdeal.finprod_zpow_count_eq_absNorm`: the rational norm of an invertible (or nonzero)
  fractional ideal equals `∏ᶠ v, (#(R ⧸ v)) ^ count K v I`.
* `IsDedekindDomain.HeightOneSpectrum.finprod_zpow_neg_log_valuation_eq_abs_norm`: when `K` is a
  finite `ℚ`-algebra, for any nonzero `a : K`,
  `∏ᶠ v, (#(R ⧸ v)) ^ (-WithZero.log (v.valuation K a)) = |Algebra.norm ℚ a|`.
-/

public section

open IsDedekindDomain
open scoped nonZeroDivisors

namespace FractionalIdeal

section Positivity

variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Module.Free ℤ R] [Module.Finite ℤ R]
  {K : Type*} [CommRing K] [IsDomain K] [Algebra R K] [IsFractionRing R K]

/-- The absolute norm of a fractional ideal is positive if and only if the ideal is nonzero. -/
@[simp]
theorem absNorm_pos_iff {I : FractionalIdeal R⁰ K} : 0 < absNorm I ↔ I ≠ 0 :=
  (absNorm_nonneg I).lt_iff_ne'.trans absNorm_eq_zero_iff.not

/-- The absolute norm of a nonzero fractional ideal is positive. -/
theorem absNorm_pos {I : FractionalIdeal R⁰ K} (hI : I ≠ 0) : 0 < absNorm I :=
  absNorm_pos_iff.mpr hI

end Positivity

section Factorization

variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Module.Free ℤ R] [Module.Finite ℤ R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- **Prime-factorization formula for the norm of an invertible fractional ideal.** -/
theorem finprod_zpow_count_units_eq_absNorm (I : (FractionalIdeal R⁰ K)ˣ) :
    (∏ᶠ v : HeightOneSpectrum R,
        (Nat.card (R ⧸ v.asIdeal) : ℚ) ^ count K v (I : FractionalIdeal R⁰ K)) =
      absNorm (I : FractionalIdeal R⁰ K) := by
  let f : (FractionalIdeal R⁰ K)ˣ →* ℚ :=
    (absNorm (R := R) (K := K)).toMonoidHom.comp (Units.coeHom _)
  have hfact := congrArg f (finprod_unitOfPrime_zpow_count I)
  rw [MonoidHom.map_finprod f (hasFiniteMulSupport_zpow_count _ _)] at hfact
  have hfI : f I = absNorm (I : FractionalIdeal R⁰ K) := rfl
  rw [hfI] at hfact
  rw [hfact]
  refine (finprod_congr fun v ↦ ?_).symm
  have hf_unit : f (v.unitOfPrime K) = (Nat.card (R ⧸ v.asIdeal) : ℚ) := by
    simp [f, HeightOneSpectrum.coe_unitOfPrime, coeIdeal_absNorm,
      Ideal.absNorm_of_ne_bot v.ne_bot, Submodule.cardQuot_apply]
  rw [map_zpow, hf_unit]

/-- **Prime-factorization formula for the norm of a nonzero fractional ideal.** -/
theorem finprod_zpow_count_eq_absNorm {I : FractionalIdeal R⁰ K} (hI : I ≠ 0) :
    (∏ᶠ v : HeightOneSpectrum R, (Nat.card (R ⧸ v.asIdeal) : ℚ) ^ count K v I) =
      absNorm I := by
  simpa using finprod_zpow_count_units_eq_absNorm (Units.mk0 I hI)

end Factorization

end FractionalIdeal

namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Module.Free ℤ R] [Module.Finite ℤ R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] [Algebra ℚ K] [Module.Finite ℚ K]

/-- **Prime-factorization formula for the rational field norm.** For a nonzero element `a : K`, the
product over all height-one primes of `(#(R ⧸ v)) ^ (-log (v.valuation K a))` equals
`|Algebra.norm ℚ a|`. -/
theorem finprod_zpow_neg_log_valuation_eq_abs_norm {a : K} (ha : a ≠ 0) :
    (∏ᶠ v : HeightOneSpectrum R,
        (Nat.card (R ⧸ v.asIdeal) : ℚ) ^ (-WithZero.log (v.valuation K a))) =
      |Algebra.norm ℚ a| := by
  simpa [FractionalIdeal.count_spanSingleton_eq_neg_log_valuation] using
    FractionalIdeal.finprod_zpow_count_eq_absNorm
      (FractionalIdeal.spanSingleton_ne_zero_iff (S := R⁰).mpr ha)

end IsDedekindDomain.HeightOneSpectrum

end
