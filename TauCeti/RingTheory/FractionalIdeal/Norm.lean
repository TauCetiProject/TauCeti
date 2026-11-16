/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.FractionalIdeal.Norm
public import TauCeti.RingTheory.DedekindDomain.Factorization

/-!
# Prime-factorisation formulas for fractional ideal norms

Let `R` be a Dedekind domain that is finitely generated and free as a `ℤ`-module, with fraction
field `K`. Applying the multiplicative morphism `FractionalIdeal.absNorm` to the prime-ideal
factorisation `I = ∏ᵥ 𝔭ᵥ ^ count K v I` of a nonzero fractional ideal expresses `absNorm I` as the
finite product over all height-one primes `v` of `(Ideal.absNorm v.asIdeal : ℚ) ^ count K v I`, or
equivalently `(Nat.card (R ⧸ v.asIdeal) : ℚ) ^ count K v I`.

When `K` is also a finite `ℚ`-algebra (in particular `R = ℤ`, `K = ℚ`, or the ring of integers of a
number field), specialising to the principal fractional ideal `(x)` of a nonzero element `x : K`
links the prime-power valuation product `∏ᵥ (#(R ⧸ v)) ^ (-log (v x))` to `|Algebra.norm ℚ x|`.

## Main results

* `FractionalIdeal.finprod_absNorm_zpow_count_eq_absNorm` and
  `FractionalIdeal.finprod_natCard_quotient_zpow_count_eq_absNorm`: the absolute norm of a nonzero
  fractional ideal is the product of prime-norm (or residue-cardinality) powers weighted by
  `FractionalIdeal.count`.
* `IsDedekindDomain.HeightOneSpectrum.finprod_absNorm_zpow_neg_log_valuation_eq_abs_norm` and
  `IsDedekindDomain.HeightOneSpectrum.finprod_natCard_quotient_zpow_neg_log_valuation_eq_abs_norm`:
  the product of prime-norm (or residue-cardinality) powers with exponents `-log (v.valuation K x)`
  equals `|Algebra.norm ℚ x|` for any nonzero `x : K`.

## References

* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992], Chapter I, §6 and Chapter III, §1.
-/

public section

open IsDedekindDomain
open scoped nonZeroDivisors

namespace FractionalIdeal

variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Module.Free ℤ R] [Module.Finite ℤ R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- **Prime-factorisation product for `FractionalIdeal.absNorm`.** The absolute norm of a nonzero
fractional ideal `I` equals the product over all height-one primes `v` of
`(Ideal.absNorm v.asIdeal : ℚ) ^ count K v I`. -/
theorem finprod_absNorm_zpow_count_eq_absNorm {I : FractionalIdeal R⁰ K} (hI : I ≠ 0) :
    (∏ᶠ v : HeightOneSpectrum R, (Ideal.absNorm v.asIdeal : ℚ) ^ count K v I) = absNorm I := by
  have hf := hasFiniteMulSupport_zpow_count I fun v ↦ (v.asIdeal : FractionalIdeal R⁰ K)
  have hmap := map_finprod (absNorm (R := R) (K := K)) hf
  rw [finprod_heightOneSpectrum_factorization' K hI] at hmap
  refine Eq.trans ?_ hmap.symm
  exact finprod_congr fun v ↦ by rw [map_zpow₀, coeIdeal_absNorm]

/-- **Residue-cardinality product for `FractionalIdeal.absNorm`.** The absolute norm of a nonzero
fractional ideal `I` equals the product over all height-one primes `v` of
`(Nat.card (R ⧸ v.asIdeal) : ℚ) ^ count K v I`. -/
theorem finprod_natCard_quotient_zpow_count_eq_absNorm {I : FractionalIdeal R⁰ K} (hI : I ≠ 0) :
    (∏ᶠ v : HeightOneSpectrum R, (Nat.card (R ⧸ v.asIdeal) : ℚ) ^ count K v I) = absNorm I := by
  rw [← finprod_absNorm_zpow_count_eq_absNorm hI]
  exact finprod_congr fun v ↦ by rw [Ideal.absNorm_of_ne_bot v.ne_bot, Submodule.cardQuot_apply]

end FractionalIdeal

namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Module.Free ℤ R] [Module.Finite ℤ R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] [Algebra ℚ K] [Module.Finite ℚ K]

variable (R) in
/-- **Prime-norm product formula for `-log (v.valuation K x)`.** For any nonzero `x : K`, the
product over all height-one primes `v` of `R` of
`(Ideal.absNorm v.asIdeal : ℚ) ^ (-WithZero.log (v.valuation K x))` equals `|Algebra.norm ℚ x|`. -/
theorem finprod_absNorm_zpow_neg_log_valuation_eq_abs_norm {x : K} (hx : x ≠ 0) :
    (∏ᶠ v : HeightOneSpectrum R,
      (Ideal.absNorm v.asIdeal : ℚ) ^ (-WithZero.log (v.valuation K x))) =
      |Algebra.norm ℚ x| := by
  simp_rw [← FractionalIdeal.count_spanSingleton_eq_neg_log_valuation K]
  rw [FractionalIdeal.finprod_absNorm_zpow_count_eq_absNorm
    (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hx), FractionalIdeal.absNorm_span_singleton]

variable (R) in
/-- **Residue-cardinality product formula for `-log (v.valuation K x)`.** For any nonzero `x : K`,
the product over all height-one primes `v` of `R` of
`(Nat.card (R ⧸ v.asIdeal) : ℚ) ^ (-WithZero.log (v.valuation K x))` equals
`|Algebra.norm ℚ x|`. -/
theorem finprod_natCard_quotient_zpow_neg_log_valuation_eq_abs_norm {x : K} (hx : x ≠ 0) :
    (∏ᶠ v : HeightOneSpectrum R,
      (Nat.card (R ⧸ v.asIdeal) : ℚ) ^ (-WithZero.log (v.valuation K x))) =
      |Algebra.norm ℚ x| := by
  rw [← finprod_absNorm_zpow_neg_log_valuation_eq_abs_norm R hx]
  exact finprod_congr fun v ↦ by rw [Ideal.absNorm_of_ne_bot v.ne_bot, Submodule.cardQuot_apply]

end IsDedekindDomain.HeightOneSpectrum

end
