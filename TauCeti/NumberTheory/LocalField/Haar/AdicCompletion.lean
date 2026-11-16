/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RamificationInertia.Inertia
public import TauCeti.NumberTheory.LocalField.Haar.Basic
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel

/-!
# Distributive Haar character on adic completions of Dedekind domains

Let `R` be a Dedekind domain with fraction field `K` and let `v` be a height-one prime of `R` with
finite residue field `R ⧸ v.asIdeal`. Then `v.adicCompletion K` is a nonarchimedean local field
whose residue field has cardinality `Ideal.absNorm v.asIdeal`. This module specializes
`TauCeti.NumberTheory.LocalField.Haar.Basic` to `v.adicCompletion K`, with no global number-field
hypotheses:

* when `R` has finite quotients (`[Ring.HasFiniteQuotients R]`, as holds for the ring of integers
  of a number field), `MeasureTheory.distribHaarChar (v.adicCompletion K) a` coincides with the
  pinned norm `‖a‖₊` of `Mathlib.NumberTheory.NumberField.Completion.FinitePlace`;
* any uniformizer `ϖ` of `v.adicCompletion K` has distributive Haar character
  `(Ideal.absNorm v.asIdeal : ℝ≥0)⁻¹`;
* when `v.asIdeal` lies over an ideal `p` of a finite-index base Dedekind domain `A` (in particular
  `Ideal.span {(p : ℤ)}` over `ℤ`), a uniformizer has character
  `((Ideal.absNorm p : ℝ≥0) ^ v.asIdeal.inertiaDeg A)⁻¹` (respectively
  `((p : ℝ≥0) ^ v.asIdeal.inertiaDeg ℤ)⁻¹`).

## Main results

* `IsDedekindDomain.HeightOneSpectrum.distribHaarChar_adicCompletion`: identification of
  `distribHaarChar (v.adicCompletion K) a` with `‖a‖₊`.
* `IsDedekindDomain.HeightOneSpectrum.distribHaarChar_adicCompletion_of_isUniformizer`: a
  uniformizer of `v.adicCompletion K` has character `(Ideal.absNorm v.asIdeal)⁻¹`.
* `IsDedekindDomain.HeightOneSpectrum.distribHaarChar_adicCompletion_of_isUniformizer_of_liesOver`
  and `distribHaarChar_adicCompletion_of_isUniformizer_of_liesOver_span`: inertia-degree forms of
  the uniformizer character.
-/

public section

open MeasureTheory NumberField TauCeti
open scoped NNReal WithZero

namespace IsDedekindDomain.HeightOneSpectrum

variable {R K : Type*} [CommRing R] [IsDedekindDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R)

/-- **Adic completion Haar character equals pinned `nnnorm`.** When `R` has finite quotients and
`R ⧸ v.asIdeal` is finite, the distributive Haar character of `a ∈ (v.adicCompletion K)ˣ` coincides
with `‖a‖₊` for the pinned norm using `Ideal.absNorm v.asIdeal`. -/
@[simp, grind =]
theorem distribHaarChar_adicCompletion [Ring.HasFiniteQuotients R] [Finite (R ⧸ v.asIdeal)]
    (a : (v.adicCompletion K)ˣ) :
    distribHaarChar (v.adicCompletion K) a = ‖(a : v.adicCompletion K)‖₊ := by
  have hnorm : Valued.v (a : v.adicCompletion K) =
      WithZero.exp (-(normalizedValuation (v.adicCompletion K) a).toAdd) := by
    have h := v.normalizedValuationWithZero_adicCompletion (K := K) a
    rw [normalizedValuationWithZero_coe] at h
    rw [← inv_inv (Valued.v (a : v.adicCompletion K)), ← h, WithZero.exp_neg,
      WithZero.exp_eq_coe_ofAdd, ofAdd_toAdd]
  apply NNReal.coe_injective
  rw [distribHaarChar_eq_zpow, coe_nnNorm, FinitePlace.norm_def, hnorm,
    WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero, WithZero.log_exp,
    v.natCard_residueField_adicCompletion_eq_absNorm, NNReal.coe_zpow, NNReal.coe_natCast]

/-- Any uniformizer `ϖ` of `v.adicCompletion K` has distributive Haar character
`(Ideal.absNorm v.asIdeal)⁻¹`. -/
theorem distribHaarChar_adicCompletion_of_isUniformizer [Finite (R ⧸ v.asIdeal)]
    {ϖ : (v.adicCompletion K)ˣ} (hϖ : IsUniformizer (v.adicCompletion K) ϖ) :
    distribHaarChar (v.adicCompletion K) ϖ = (Ideal.absNorm v.asIdeal : ℝ≥0)⁻¹ := by
  rw [distribHaarChar_of_isUniformizer hϖ, v.natCard_residueField_adicCompletion_eq_absNorm]

/-- If `v.asIdeal` lies over an ideal `p` of a Dedekind domain `A` with `R` finite over `A`, then
any uniformizer `ϖ` of `v.adicCompletion K` has distributive Haar character
`(Ideal.absNorm p) ^ (-f)`, where `f = v.asIdeal.inertiaDeg A`. -/
theorem distribHaarChar_adicCompletion_of_isUniformizer_of_liesOver
    {A : Type*} [CommRing A] [IsDedekindDomain A] [Infinite A] [Infinite R]
    [Algebra A R] [Module.Finite A R] [Finite (R ⧸ v.asIdeal)]
    (p : Ideal A) [v.asIdeal.LiesOver p] {ϖ : (v.adicCompletion K)ˣ}
    (hϖ : IsUniformizer (v.adicCompletion K) ϖ) :
    distribHaarChar (v.adicCompletion K) ϖ =
      ((Ideal.absNorm p : ℝ≥0) ^ v.asIdeal.inertiaDeg A)⁻¹ := by
  rw [v.distribHaarChar_adicCompletion_of_isUniformizer hϖ,
    ← Ideal.absNorm_pow_inertiaDeg p v.asIdeal, Nat.cast_pow]

/-- If `R` is finite over `ℤ` and `v.asIdeal` lies over `Ideal.span {(p : ℤ)}`, then any
uniformizer `ϖ` of `v.adicCompletion K` has distributive Haar character `p ^ (-f)`, where
`f = v.asIdeal.inertiaDeg ℤ`. -/
theorem distribHaarChar_adicCompletion_of_isUniformizer_of_liesOver_span
    [Infinite R] [Module.Finite ℤ R] [Finite (R ⧸ v.asIdeal)]
    (p : ℕ) [v.asIdeal.LiesOver (Ideal.span {(p : ℤ)})] {ϖ : (v.adicCompletion K)ˣ}
    (hϖ : IsUniformizer (v.adicCompletion K) ϖ) :
    distribHaarChar (v.adicCompletion K) ϖ = ((p : ℝ≥0) ^ v.asIdeal.inertiaDeg ℤ)⁻¹ := by
  rw [v.distribHaarChar_adicCompletion_of_isUniformizer hϖ,
    ← Ideal.pow_inertiaDeg p v.asIdeal, Nat.cast_pow]

/-- Sanity check: when `v.asIdeal` lies over `(p)` with inertia degree `f > 1`, a uniformizer of
`v.adicCompletion K` has distributive Haar character strictly smaller than `p⁻¹`. -/
example [Infinite R] [Module.Finite ℤ R] [Finite (R ⧸ v.asIdeal)]
    (p : ℕ) [v.asIdeal.LiesOver (Ideal.span {(p : ℤ)})]
    (hf : 1 < v.asIdeal.inertiaDeg ℤ) {ϖ : (v.adicCompletion K)ˣ}
    (hϖ : IsUniformizer (v.adicCompletion K) ϖ) :
    distribHaarChar (v.adicCompletion K) ϖ < (p : ℝ≥0)⁻¹ := by
  rw [v.distribHaarChar_adicCompletion_of_isUniformizer_of_liesOver_span p hϖ]
  have hp_prime : (Ideal.span {(p : ℤ)}).IsPrime :=
    Ideal.isPrime_of_liesOver v.asIdeal (Ideal.span {(p : ℤ)})
  have hp0 : p ≠ 0 := by
    rintro rfl
    have hbot : Ideal.span {((0 : ℕ) : ℤ)} = ⊥ := by simp
    have : v.asIdeal.LiesOver (⊥ : Ideal ℤ) := hbot ▸ inferInstance
    exact v.ne_bot (Ideal.eq_bot_of_liesOver_bot ℤ v.asIdeal)
  have hp1 : p ≠ 1 := by
    rintro rfl
    exact hp_prime.ne_top (by simp)
  have hp1_lt : (1 : ℝ≥0) < p := by
    exact_mod_cast Nat.one_lt_iff_ne_zero_and_ne_one.2 ⟨hp0, hp1⟩
  have hp0_lt : (0 : ℝ≥0) < p := zero_lt_one.trans hp1_lt
  exact inv_strictAnti₀ hp0_lt (by simpa using pow_lt_pow_right₀ hp1_lt hf)

end IsDedekindDomain.HeightOneSpectrum
