/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.Completion
import TauCeti.RingTheory.DedekindDomain.AdicValuation.Multiplicity
import TauCeti.RingTheory.DiscreteValuationRing.Basic

/-!
# Quotient cardinalities of completed integer rings at height-one primes

Let `R` be a Dedekind domain with fraction field `K` and let `v` be a height-one prime of `R`.
In the completed integer ring `𝒪_v = v.adicCompletionIntegers K`, a nonzero global element `r ∈ R`
generates a power of the maximal ideal `𝔪_v`. This file identifies that exponent with the global
ideal multiplicity `multiplicity v.asIdeal (Ideal.span {r})`, equips `𝒪_v` with
`Ring.HasFiniteQuotients` whenever `R ⧸ v.asIdeal` is finite, and computes the cardinality of
`𝒪_v ⧸ (r)` in terms of `Nat.card (R ⧸ v.asIdeal)` and `Ideal.absNorm v.asIdeal` without assuming
that `v` does not divide `r`.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.span_algebraMap_adicCompletionIntegers_eq_maximalIdeal_pow`:
  for `r ≠ 0`, `Ideal.span {algebraMap R 𝒪_v r} = 𝔪_v ^ multiplicity v.asIdeal (Ideal.span {r})`.
* `IsDedekindDomain.HeightOneSpectrum.hasFiniteQuotients_adicCompletionIntegers`: if
  `R ⧸ v.asIdeal` is finite, `𝒪_v` has finite quotients by nonzero ideals.
* `HeightOneSpectrum.natCard_quotient_span_algebraMap_adicCompletionIntegers_eq_pow` and
  `..._eq_absNorm_pow` (in `IsDedekindDomain`): `#(𝒪_v ⧸ (r)) = #(R ⧸ v) ^ v(r) = N(v) ^ v(r)` for
  any nonzero `r ∈ R`, with no finiteness hypothesis on the residue field.
* `IsDedekindDomain.HeightOneSpectrum.natCard_quotient_span_natCast_adicCompletionIntegers_eq_pow`:
  specialization to a natural number `n` with `(n : R) ≠ 0`.

## References

* [J. Neukirch, *Algebraic Number Theory*][neukirch1999], Chapter II, §4 and §6.
-/

public section

open IsDedekindDomain

namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- In the completed integer ring `v.adicCompletionIntegers K`, a nonzero element `r ∈ R` generates
the power of the maximal ideal whose exponent is the multiplicity of `v.asIdeal` in `(r)`. -/
theorem span_algebraMap_adicCompletionIntegers_eq_maximalIdeal_pow
    (v : HeightOneSpectrum R) {r : R} (hr : r ≠ 0) :
    Ideal.span {algebraMap R (v.adicCompletionIntegers K) r} =
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^
        multiplicity v.asIdeal (Ideal.span {r}) := by
  obtain ⟨e, he⟩ := v.exists_span_algebraMap_adicCompletionIntegers_eq_maximalIdeal_pow (K := K) hr
  have hmap : Ideal.span {algebraMap R (v.adicCompletionIntegers K) r} =
      (Ideal.span {r}).map (algebraMap R (v.adicCompletionIntegers K)) := by
    rw [Ideal.map_span, Set.image_singleton]
  have hP : Prime (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) :=
    Ideal.prime_of_isPrime (IsDiscreteValuationRing.not_a_field _) inferInstance
  have hmul := congrArg (multiplicity (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K))) he
  rw [hmap, v.multiplicity_map_adicCompletionIntegers (Ideal.span {r})
    (mt Ideal.span_singleton_eq_bot.mp hr), multiplicity_pow_self_of_prime hP] at hmul
  rwa [hmul]

/-- The residue field of `v.adicCompletionIntegers K` has the same `Nat.card` as `R ⧸ v.asIdeal`. -/
@[simp]
theorem natCard_residueField_adicCompletionIntegers (v : HeightOneSpectrum R) :
    Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers K)) =
      Nat.card (R ⧸ v.asIdeal) :=
  Nat.card_congr (v.residueFieldEquivAdicCompletionIntegers (K := K)).symm.toEquiv

/-- If `R ⧸ v.asIdeal` is finite, the completed integer ring `v.adicCompletionIntegers K` has
finite quotients by all nonzero ideals. -/
instance hasFiniteQuotients_adicCompletionIntegers
    (v : HeightOneSpectrum R) [Finite (R ⧸ v.asIdeal)] :
    Ring.HasFiniteQuotients (v.adicCompletionIntegers K) :=
  have : Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers K)) :=
    Finite.of_equiv _ (v.residueFieldEquivAdicCompletionIntegers (K := K)).toEquiv
  TauCeti.IsDiscreteValuationRing.hasFiniteQuotients

/-- If `R ⧸ v.asIdeal` is finite and `r ∈ R` is nonzero, the quotient of
`v.adicCompletionIntegers K` by the image of `r` is finite. -/
theorem finite_quotient_span_algebraMap_adicCompletionIntegers
    (v : HeightOneSpectrum R) [Finite (R ⧸ v.asIdeal)] {r : R} (hr : r ≠ 0) :
    Finite (v.adicCompletionIntegers K ⧸
      Ideal.span {algebraMap R (v.adicCompletionIntegers K) r}) :=
  Ring.HasFiniteQuotients.finiteQuotient <| mt Ideal.span_singleton_eq_bot.mp <|
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective R (v.adicCompletionIntegers K))).mpr hr

/-- For any nonzero `r ∈ R`, the cardinality of `v.adicCompletionIntegers K ⧸ (r)` is
`Nat.card (R ⧸ v.asIdeal) ^ multiplicity v.asIdeal (Ideal.span {r})`. No finiteness assumption on
the residue field is required. -/
theorem natCard_quotient_span_algebraMap_adicCompletionIntegers_eq_pow
    (v : HeightOneSpectrum R) {r : R} (hr : r ≠ 0) :
    Nat.card (v.adicCompletionIntegers K ⧸
      Ideal.span {algebraMap R (v.adicCompletionIntegers K) r}) =
      Nat.card (R ⧸ v.asIdeal) ^ multiplicity v.asIdeal (Ideal.span {r}) := by
  rw [v.span_algebraMap_adicCompletionIntegers_eq_maximalIdeal_pow hr,
    TauCeti.IsDiscreteValuationRing.natCard_quotient_maximalIdeal_pow,
    v.natCard_residueField_adicCompletionIntegers]

/-- For any nonzero `r ∈ R`, the cardinality of `v.adicCompletionIntegers K ⧸ (r)` equals
`Ideal.absNorm v.asIdeal ^ multiplicity v.asIdeal (Ideal.span {r})`. -/
theorem natCard_quotient_span_algebraMap_adicCompletionIntegers_eq_absNorm_pow
    (v : HeightOneSpectrum R) {r : R} (hr : r ≠ 0) :
    Nat.card (v.adicCompletionIntegers K ⧸
      Ideal.span {algebraMap R (v.adicCompletionIntegers K) r}) =
      Ideal.absNorm v.asIdeal ^ multiplicity v.asIdeal (Ideal.span {r}) := by
  rw [v.natCard_quotient_span_algebraMap_adicCompletionIntegers_eq_pow hr,
    Ideal.absNorm_of_ne_bot v.ne_bot, Submodule.cardQuot_apply]

/-- For `n : ℕ` with `(n : R) ≠ 0`, the ideal `(n)` in `v.adicCompletionIntegers K` equals the
`multiplicity v.asIdeal (Ideal.span {(n : R)})`-th power of the maximal ideal. -/
theorem span_natCast_adicCompletionIntegers_eq_maximalIdeal_pow
    (v : HeightOneSpectrum R) {n : ℕ} (hn : (n : R) ≠ 0) :
    Ideal.span {(n : v.adicCompletionIntegers K)} =
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^
        multiplicity v.asIdeal (Ideal.span {(n : R)}) := by
  simpa only [map_natCast] using
    v.span_algebraMap_adicCompletionIntegers_eq_maximalIdeal_pow (K := K) hn

/-- If `R ⧸ v.asIdeal` is finite and `(n : R) ≠ 0`, the quotient
`v.adicCompletionIntegers K ⧸ (n)` is finite. -/
theorem finite_quotient_span_natCast_adicCompletionIntegers
    (v : HeightOneSpectrum R) [Finite (R ⧸ v.asIdeal)] {n : ℕ} (hn : (n : R) ≠ 0) :
    Finite (v.adicCompletionIntegers K ⧸ Ideal.span {(n : v.adicCompletionIntegers K)}) := by
  simpa only [map_natCast] using
    v.finite_quotient_span_algebraMap_adicCompletionIntegers (K := K) hn

/-- For `n : ℕ` with `(n : R) ≠ 0`, the cardinality of `v.adicCompletionIntegers K ⧸ (n)` equals
`Nat.card (R ⧸ v.asIdeal) ^ multiplicity v.asIdeal (Ideal.span {(n : R)})`. -/
theorem natCard_quotient_span_natCast_adicCompletionIntegers_eq_pow
    (v : HeightOneSpectrum R) {n : ℕ} (hn : (n : R) ≠ 0) :
    Nat.card (v.adicCompletionIntegers K ⧸ Ideal.span {(n : v.adicCompletionIntegers K)}) =
      Nat.card (R ⧸ v.asIdeal) ^ multiplicity v.asIdeal (Ideal.span {(n : R)}) := by
  simpa only [map_natCast] using
    v.natCard_quotient_span_algebraMap_adicCompletionIntegers_eq_pow (K := K) hn

end IsDedekindDomain.HeightOneSpectrum
