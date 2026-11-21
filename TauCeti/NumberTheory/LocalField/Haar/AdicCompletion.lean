/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RamificationInertia.Inertia
public import TauCeti.NumberTheory.LocalField.Haar.Basic
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel
import TauCeti.RingTheory.Ideal.LiesOver

/-!
# Normalized additive Haar measure and character on adic completions of Dedekind domains

Let `R` be a Dedekind domain with fraction field `K` and let `v` be a height-one prime of `R` with
finite residue field `R ⧸ v.asIdeal`. Then `v.adicCompletion K` is a nonarchimedean local field
whose residue field has cardinality `Ideal.absNorm v.asIdeal`. This module specializes
`TauCeti.NumberTheory.LocalField.Haar.Basic` to `v.adicCompletion K`, with no global number-field
hypotheses:

* the normalized additive Haar measure `TauCeti.localAddHaar (v.adicCompletion K)` assigns mass one
  to `v.adicCompletionIntegers K`;
* when `R` has finite quotients (`[Ring.HasFiniteQuotients R]`, as holds for the ring of integers
  of a number field), `MeasureTheory.distribHaarChar (v.adicCompletion K) a` coincides with the
  pinned norm `‖a‖₊` of `Mathlib.NumberTheory.NumberField.Completion.FinitePlace`;
* any uniformizer `ϖ` of `v.adicCompletion K` has distributive Haar character
  `(Ideal.absNorm v.asIdeal : ℝ≥0)⁻¹`;
* when `v.asIdeal` lies over a nonzero ideal `p` of a base Dedekind domain `A` (in particular
  `Ideal.span {(p : ℤ)}` over `ℤ`), a uniformizer has character
  `((Ideal.absNorm p : ℝ≥0) ^ v.asIdeal.inertiaDeg A)⁻¹` (respectively
  `((p : ℝ≥0) ^ v.asIdeal.inertiaDeg ℤ)⁻¹`).

## Main results

* `IsDedekindDomain.HeightOneSpectrum.localAddHaar_adicCompletionIntegers`: the normalized additive
  Haar measure gives `v.adicCompletionIntegers K` mass one.
* `IsDedekindDomain.HeightOneSpectrum.distribHaarChar_adicCompletion`: identification of
  `distribHaarChar (v.adicCompletion K) a` with `‖a‖₊`.
* `IsDedekindDomain.HeightOneSpectrum.distribHaarChar_adicCompletion_of_isUniformizer`: a
  uniformizer of `v.adicCompletion K` has character `(Ideal.absNorm v.asIdeal)⁻¹`.
* `IsDedekindDomain.HeightOneSpectrum.distribHaarChar_adicCompletion_of_isUniformizer_of_liesOver`
  and `distribHaarChar_adicCompletion_of_isUniformizer_of_liesOver_span`: inertia-degree forms of
  the uniformizer character.
-/

public section

open MeasureTheory TauCeti
open scoped NNReal ValuativeRel

namespace IsDedekindDomain.HeightOneSpectrum

variable {R K : Type*} [CommRing R] [IsDedekindDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R)

/-- The normalized additive Haar measure on `v.adicCompletion K` gives the local integer ring
`v.adicCompletionIntegers K` mass one. -/
@[simp, grind =]
theorem localAddHaar_adicCompletionIntegers [Finite (R ⧸ v.asIdeal)]
    [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)] :
    localAddHaar (v.adicCompletion K)
      (v.adicCompletionIntegers K : Set (v.adicCompletion K)) = 1 := by
  have h : (v.adicCompletionIntegers K : Set (v.adicCompletion K)) =
      (𝒪[v.adicCompletion K] : Set (v.adicCompletion K)) := by
    rw [v.integer_eq_adicCompletionIntegers (K := K)]
    rfl
  rw [h, localAddHaar_integer]

/-- **Adic completion Haar character equals pinned `nnnorm`.** When `R` has finite quotients and
`R ⧸ v.asIdeal` is finite, the distributive Haar character of `a ∈ (v.adicCompletion K)ˣ` coincides
with `‖a‖₊` for the pinned norm using `Ideal.absNorm v.asIdeal`. -/
@[simp, grind =]
theorem distribHaarChar_adicCompletion [Ring.HasFiniteQuotients R] [Finite (R ⧸ v.asIdeal)]
    (a : (v.adicCompletion K)ˣ) :
    distribHaarChar (v.adicCompletion K) a = ‖(a : v.adicCompletion K)‖₊ := by
  rw [a.distribHaarChar_eq_normalizedAbsoluteValue,
    v.normalizedAbsoluteValue_adicCompletion_eq_nnnorm]

/-- Any uniformizer `ϖ` of `v.adicCompletion K` has distributive Haar character
`(Ideal.absNorm v.asIdeal)⁻¹`. -/
theorem distribHaarChar_adicCompletion_of_isUniformizer [Finite (R ⧸ v.asIdeal)]
    {ϖ : (v.adicCompletion K)ˣ} (hϖ : IsUniformizer (v.adicCompletion K) ϖ) :
    distribHaarChar (v.adicCompletion K) ϖ = (Ideal.absNorm v.asIdeal : ℝ≥0)⁻¹ := by
  rw [distribHaarChar_of_isUniformizer hϖ, v.natCard_residueField_adicCompletion_eq_absNorm]

/-- If `v.asIdeal` lies over a nonzero ideal `p` of a Dedekind domain `A`, then any uniformizer `ϖ`
of `v.adicCompletion K` has distributive Haar character `(Ideal.absNorm p) ^ (-f)`, where
`f = v.asIdeal.inertiaDeg A`. -/
theorem distribHaarChar_adicCompletion_of_isUniformizer_of_liesOver
    {A : Type*} [CommRing A] [IsDedekindDomain A] [Algebra A R] [Finite (R ⧸ v.asIdeal)]
    {p : Ideal A} (hp : p ≠ ⊥) [v.asIdeal.LiesOver p] {ϖ : (v.adicCompletion K)ˣ}
    (hϖ : IsUniformizer (v.adicCompletion K) ϖ) :
    distribHaarChar (v.adicCompletion K) ϖ =
      ((Ideal.absNorm p : ℝ≥0) ^ v.asIdeal.inertiaDeg A)⁻¹ := by
  have hp_prime : p.IsPrime := Ideal.isPrime_of_liesOver v.asIdeal p
  have _ : p.IsMaximal := hp_prime.isMaximal hp
  let _ : Field (A ⧸ p) := Ideal.Quotient.field p
  have _ : Module.Finite (A ⧸ p) (R ⧸ v.asIdeal) := Module.Finite.of_finite
  have hnorm : Ideal.absNorm v.asIdeal = Ideal.absNorm p ^ v.asIdeal.inertiaDeg A := by
    rw [Ideal.absNorm_of_ne_bot v.ne_bot, Ideal.absNorm_of_ne_bot hp, Submodule.cardQuot_apply,
      Submodule.cardQuot_apply, Ideal.inertiaDeg_eq_of_isMaximal p v.asIdeal,
      Module.natCard_eq_pow_finrank (K := A ⧸ p) (V := R ⧸ v.asIdeal)]
  rw [v.distribHaarChar_adicCompletion_of_isUniformizer hϖ, hnorm, Nat.cast_pow]

/-- If `v.asIdeal` lies over `Ideal.span {(p : ℤ)}`, then any uniformizer `ϖ` of
`v.adicCompletion K` has distributive Haar character `p ^ (-f)`, where
`f = v.asIdeal.inertiaDeg ℤ`. -/
theorem distribHaarChar_adicCompletion_of_isUniformizer_of_liesOver_span
    [Finite (R ⧸ v.asIdeal)] (p : ℕ) [v.asIdeal.LiesOver (Ideal.span {(p : ℤ)})]
    {ϖ : (v.adicCompletion K)ˣ} (hϖ : IsUniformizer (v.adicCompletion K) ϖ) :
    distribHaarChar (v.adicCompletion K) ϖ = ((p : ℝ≥0) ^ v.asIdeal.inertiaDeg ℤ)⁻¹ := by
  simpa using v.distribHaarChar_adicCompletion_of_isUniformizer_of_liesOver
    (Ideal.ne_bot_of_finite_quotient_of_liesOver (Ideal.span {(p : ℤ)}) v.asIdeal) hϖ

/-- Sanity check: when `v.asIdeal` lies over `(p)` with inertia degree `f > 1`, a uniformizer of
`v.adicCompletion K` has distributive Haar character strictly smaller than `p⁻¹`. -/
example [Finite (R ⧸ v.asIdeal)] (p : ℕ) [v.asIdeal.LiesOver (Ideal.span {(p : ℤ)})]
    (hf : 1 < v.asIdeal.inertiaDeg ℤ) {ϖ : (v.adicCompletion K)ˣ}
    (hϖ : IsUniformizer (v.adicCompletion K) ϖ) :
    distribHaarChar (v.adicCompletion K) ϖ < (p : ℝ≥0)⁻¹ := by
  rw [v.distribHaarChar_adicCompletion_of_isUniformizer_of_liesOver_span p hϖ]
  have hp_prime : (Ideal.span {(p : ℤ)}).IsPrime :=
    Ideal.isPrime_of_liesOver v.asIdeal (Ideal.span {(p : ℤ)})
  have hp0 : p ≠ 0 := by
    rintro rfl
    exact Ideal.ne_bot_of_finite_quotient_of_liesOver (Ideal.span {((0 : ℕ) : ℤ)}) v.asIdeal
      (by simp)
  have hp1 : p ≠ 1 := by
    rintro rfl
    exact hp_prime.ne_top (by simp)
  have hp1_lt : (1 : ℝ≥0) < p := by
    exact_mod_cast Nat.one_lt_iff_ne_zero_and_ne_one.2 ⟨hp0, hp1⟩
  have hp0_lt : (0 : ℝ≥0) < p := zero_lt_one.trans hp1_lt
  exact inv_strictAnti₀ hp0_lt (by simpa using pow_lt_pow_right₀ hp1_lt hf)

end IsDedekindDomain.HeightOneSpectrum
