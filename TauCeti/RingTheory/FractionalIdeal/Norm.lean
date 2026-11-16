/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.FractionalIdeal.Norm
public import TauCeti.RingTheory.DedekindDomain.Factorization

/-!
# Prime-factorization formulas for fractional ideal and field norms

Let `R` be a Dedekind domain. For any nonzero ideal `J` of `R`, applying `Ideal.absNorm` to
`Ideal.finprod_heightOneSpectrum_factorization` expresses `Ideal.absNorm J` in `ℕ` as the product
over all height-one primes `v` of `R` of the residue cardinality `Nat.card (R ⧸ v.asIdeal)` raised
to the multiplicity at `v`. When `R` is also finite and free as a `ℤ`-module, with fraction field
`K`, combining `FractionalIdeal.finprod_unitOfPrime_zpow_count` with `FractionalIdeal.absNorm`
gives the corresponding formula in `ℚ` for any nonzero fractional ideal (and in particular for any
nonzero principal fractional ideal).

## Main results

* `FractionalIdeal.finprod_zpow_count_units_eq_absNorm` and
  `FractionalIdeal.finprod_zpow_count_eq_absNorm`: the rational norm of an invertible (or nonzero)
  fractional ideal equals `∏ᶠ v, (#(R ⧸ v)) ^ count K v I`.
* `Ideal.finprod_pow_count_eq_absNorm`: for a nonzero ideal `J` of an arbitrary Dedekind domain `R`,
  the absolute norm equals `∏ᶠ v, (#(R ⧸ v)) ^ count v J`.
* `IsDedekindDomain.HeightOneSpectrum.finprod_zpow_neg_log_valuation_eq_abs_norm`: when `K` is a
  finite `ℚ`-algebra, for any nonzero `a : K`,
  `∏ᶠ v, (#(R ⧸ v)) ^ (-WithZero.log (v.valuation K a)) = |Algebra.norm ℚ a|`.
-/

public section

open IsDedekindDomain
open scoped nonZeroDivisors

namespace FractionalIdeal

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

end FractionalIdeal

namespace Ideal

open _root_.IsDedekindDomain

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

/-- **Prime-factorization formula for the absolute norm of a nonzero ideal.** -/
theorem finprod_pow_count_eq_absNorm {J : Ideal R} (hJ : J ≠ ⊥) :
    (∏ᶠ v : HeightOneSpectrum R,
        Nat.card (R ⧸ v.asIdeal) ^ (Associates.mk v.asIdeal).count (Associates.mk J).factors) =
      Ideal.absNorm J := by
  have hJ0 : J ≠ 0 := by rwa [Ideal.zero_eq_bot]
  have hfact := congrArg Ideal.absNorm.toMonoidHom
    (Ideal.finprod_heightOneSpectrum_factorization hJ0)
  rw [MonoidHom.map_finprod _ (Ideal.hasFiniteMulSupport hJ0)] at hfact
  refine Eq.trans ?_ hfact
  refine finprod_congr fun v ↦ ?_
  simp [IsDedekindDomain.HeightOneSpectrum.maxPowDividing, Ideal.absNorm_of_ne_bot v.ne_bot,
    Submodule.cardQuot_apply]

end Ideal

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
