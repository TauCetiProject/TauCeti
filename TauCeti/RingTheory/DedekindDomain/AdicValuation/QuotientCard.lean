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
In the completed integer ring `𝒪_v = v.adicCompletionIntegers K`, the extension of a nonzero global
ideal `I` of `R` is a power of the maximal ideal `𝔪_v`. This file identifies that exponent with the
global ideal multiplicity `multiplicity v.asIdeal I`, equips `𝒪_v` with `Ring.HasFiniteQuotients`
whenever `R ⧸ v.asIdeal` is finite, computes the cardinality of `𝒪_v ⧸ I.map (algebraMap R 𝒪_v)` in
terms of `Nat.card (R ⧸ v.asIdeal)` and `Ideal.absNorm v.asIdeal`, and specializes these formulas to
principal ideals `(r)` and natural-number casts `(n)` without assuming coprimality to `v`.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.map_adicCompletionIntegers_eq_maximalIdeal_pow` and
  `IsDedekindDomain.HeightOneSpectrum.span_algebraMap_adicCompletionIntegers_eq_maximalIdeal_pow`:
  for `I ≠ ⊥`, `I.map (algebraMap R 𝒪_v) = 𝔪_v ^ multiplicity v.asIdeal I`, and its specialization
  to `I = Ideal.span {r}` (`r ≠ 0`).
* `IsDedekindDomain.HeightOneSpectrum.hasFiniteQuotients_adicCompletionIntegers`: if
  `R ⧸ v.asIdeal` is finite, `𝒪_v` has finite quotients by nonzero ideals.
* `HeightOneSpectrum.natCard_quotient_map_adicCompletionIntegers_eq_pow`,
  `HeightOneSpectrum.natCard_quotient_map_adicCompletionIntegers_eq_absNorm_pow`, and their
  `span_algebraMap` and `span_natCast` specializations (in `IsDedekindDomain`):
  `#(𝒪_v ⧸ I 𝒪_v) = #(R ⧸ v) ^ v(I) = N(v) ^ v(I)` for any nonzero ideal `I` of `R`, with no
  finiteness hypothesis on the residue field.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter II, §4 and §6.
-/

public section

open IsDedekindDomain

namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- In the completed integer ring `v.adicCompletionIntegers K`, extending a nonzero ideal `I` of
`R` produces the power of the maximal ideal whose exponent is `multiplicity v.asIdeal I`. -/
theorem map_adicCompletionIntegers_eq_maximalIdeal_pow
    (v : HeightOneSpectrum R) {I : Ideal R} (hI : I ≠ ⊥) :
    I.map (algebraMap R (v.adicCompletionIntegers K)) =
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ multiplicity v.asIdeal I := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers K)
  obtain ⟨e, he⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible
    (Ideal.map_ne_bot_of_ne_bot hI) hϖ
  rw [← Ideal.span_singleton_pow, ← hϖ.maximalIdeal_eq] at he
  have hP : Prime (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) :=
    Ideal.prime_of_isPrime (IsDiscreteValuationRing.not_a_field _) inferInstance
  have hmul := congrArg (multiplicity (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K))) he
  rw [v.multiplicity_map_adicCompletionIntegers I hI, multiplicity_pow_self_of_prime hP] at hmul
  rwa [hmul]

/-- In the completed integer ring `v.adicCompletionIntegers K`, a nonzero element `r ∈ R` generates
the power of the maximal ideal whose exponent is the multiplicity of `v.asIdeal` in `(r)`. -/
theorem span_algebraMap_adicCompletionIntegers_eq_maximalIdeal_pow
    (v : HeightOneSpectrum R) {r : R} (hr : r ≠ 0) :
    Ideal.span {algebraMap R (v.adicCompletionIntegers K) r} =
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^
        multiplicity v.asIdeal (Ideal.span {r}) := by
  rw [← Set.image_singleton, ← Ideal.map_span,
    v.map_adicCompletionIntegers_eq_maximalIdeal_pow (mt Ideal.span_singleton_eq_bot.mp hr)]

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
  TauCeti.IsDiscreteValuationRing.hasFiniteQuotients

/-- If `R ⧸ v.asIdeal` is finite and `I` is a nonzero ideal of `R`, the quotient of
`v.adicCompletionIntegers K` by the extended ideal `I.map (algebraMap R _)` is finite. -/
theorem finite_quotient_map_adicCompletionIntegers
    (v : HeightOneSpectrum R) [Finite (R ⧸ v.asIdeal)] {I : Ideal R} (hI : I ≠ ⊥) :
    Finite (v.adicCompletionIntegers K ⧸ I.map (algebraMap R (v.adicCompletionIntegers K))) :=
  Ring.HasFiniteQuotients.finiteQuotient (Ideal.map_ne_bot_of_ne_bot hI)

/-- If `R ⧸ v.asIdeal` is finite and `r ∈ R` is nonzero, the quotient of
`v.adicCompletionIntegers K` by the image of `r` is finite. -/
theorem finite_quotient_span_algebraMap_adicCompletionIntegers
    (v : HeightOneSpectrum R) [Finite (R ⧸ v.asIdeal)] {r : R} (hr : r ≠ 0) :
    Finite (v.adicCompletionIntegers K ⧸
      Ideal.span {algebraMap R (v.adicCompletionIntegers K) r}) := by
  rw [← Set.image_singleton, ← Ideal.map_span]
  exact v.finite_quotient_map_adicCompletionIntegers (mt Ideal.span_singleton_eq_bot.mp hr)

/-- For any nonzero ideal `I` of `R`, the cardinality of
`v.adicCompletionIntegers K ⧸ I.map (algebraMap R _)` is
`Nat.card (R ⧸ v.asIdeal) ^ multiplicity v.asIdeal I`. No finiteness assumption on the residue field
is required. -/
theorem natCard_quotient_map_adicCompletionIntegers_eq_pow
    (v : HeightOneSpectrum R) {I : Ideal R} (hI : I ≠ ⊥) :
    Nat.card (v.adicCompletionIntegers K ⧸ I.map (algebraMap R (v.adicCompletionIntegers K))) =
      Nat.card (R ⧸ v.asIdeal) ^ multiplicity v.asIdeal I := by
  rw [v.map_adicCompletionIntegers_eq_maximalIdeal_pow hI,
    TauCeti.IsDiscreteValuationRing.natCard_quotient_maximalIdeal_pow,
    v.natCard_residueField_adicCompletionIntegers]

/-- For any nonzero ideal `I` of `R`, the cardinality of
`v.adicCompletionIntegers K ⧸ I.map (algebraMap R _)` equals
`Ideal.absNorm v.asIdeal ^ multiplicity v.asIdeal I`. -/
theorem natCard_quotient_map_adicCompletionIntegers_eq_absNorm_pow
    (v : HeightOneSpectrum R) {I : Ideal R} (hI : I ≠ ⊥) :
    Nat.card (v.adicCompletionIntegers K ⧸ I.map (algebraMap R (v.adicCompletionIntegers K))) =
      Ideal.absNorm v.asIdeal ^ multiplicity v.asIdeal I := by
  rw [v.natCard_quotient_map_adicCompletionIntegers_eq_pow hI,
    Ideal.absNorm_of_ne_bot v.ne_bot, Submodule.cardQuot_apply]

/-- For any nonzero `r ∈ R`, the cardinality of `v.adicCompletionIntegers K ⧸ (r)` is
`Nat.card (R ⧸ v.asIdeal) ^ multiplicity v.asIdeal (Ideal.span {r})`. No finiteness assumption on
the residue field is required. -/
theorem natCard_quotient_span_algebraMap_adicCompletionIntegers_eq_pow
    (v : HeightOneSpectrum R) {r : R} (hr : r ≠ 0) :
    Nat.card (v.adicCompletionIntegers K ⧸
      Ideal.span {algebraMap R (v.adicCompletionIntegers K) r}) =
      Nat.card (R ⧸ v.asIdeal) ^ multiplicity v.asIdeal (Ideal.span {r}) := by
  rw [← Set.image_singleton, ← Ideal.map_span,
    v.natCard_quotient_map_adicCompletionIntegers_eq_pow (mt Ideal.span_singleton_eq_bot.mp hr)]

/-- For any nonzero `r ∈ R`, the cardinality of `v.adicCompletionIntegers K ⧸ (r)` equals
`Ideal.absNorm v.asIdeal ^ multiplicity v.asIdeal (Ideal.span {r})`. -/
theorem natCard_quotient_span_algebraMap_adicCompletionIntegers_eq_absNorm_pow
    (v : HeightOneSpectrum R) {r : R} (hr : r ≠ 0) :
    Nat.card (v.adicCompletionIntegers K ⧸
      Ideal.span {algebraMap R (v.adicCompletionIntegers K) r}) =
      Ideal.absNorm v.asIdeal ^ multiplicity v.asIdeal (Ideal.span {r}) := by
  rw [← Set.image_singleton, ← Ideal.map_span,
    v.natCard_quotient_map_adicCompletionIntegers_eq_absNorm_pow
      (mt Ideal.span_singleton_eq_bot.mp hr)]

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
