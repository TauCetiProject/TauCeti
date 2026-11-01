/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Gaussian orthogonal and unitary ensembles

The matrix `gaussianEnsemble β n g` built from an array `g` of reals: for `β = 1` the real
symmetric matrix with entries `g i j` above the diagonal and `√2 * g i i` on it, and otherwise the
Hermitian matrix with entries `(g i j + I * g j i) / √2` above the diagonal and `g i i` on it, all
divided by `√n`. With independent standard Gaussian entries this is the GOE (`β = 1`) or the GUE
(`β = 2`).

## Main definitions

* `TauCeti.Probability.gaussianEnsemble`: the matrix built from the array `g`.

## Main results

* `TauCeti.Probability.gaussianEnsemble_isHermitian`: the matrix is Hermitian.
* `TauCeti.Probability.gaussianEnsemble_one_zero_zero_hasLaw` and
  `TauCeti.Probability.gaussianEnsemble_two_zero_zero_hasLaw`: the laws of the `1 × 1` ensembles,
  `N(0, 2)` and `N(0, 1)`.
* `TauCeti.Probability.integral_trace_sq_div_gaussianEnsemble_one` and
  `TauCeti.Probability.integral_trace_sq_div_gaussianEnsemble_two`: the normalized trace of the
  square has expectation `1 + 1 / n` for the GOE and `1` for the GUE.
-/

public section

noncomputable section

open MeasureTheory Matrix ProbabilityTheory

namespace TauCeti

namespace Probability

/-- The Gaussian ensemble built from the array `g`: for `β = 1` the real symmetric matrix with
entries `g i j` for `i < j` and `√2 * g i i` on the diagonal, and otherwise the Hermitian matrix
with entries `(g i j + I * g j i) / √2` for `i < j` and `g i i` on the diagonal, all divided by
`√n`. With independent standard Gaussian entries this is the GOE (`β = 1`) or the GUE
(`β = 2`). -/
def gaussianEnsemble (β n : ℕ) (g : Fin n → Fin n → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j ↦ ((Real.sqrt n)⁻¹ : ℂ) *
    if β = 1 then
      if i = j then ((Real.sqrt 2 * g i i : ℝ) : ℂ)
      else if i < j then (g i j : ℂ) else (g j i : ℂ)
    else
      if i = j then (g i i : ℂ)
      else if i < j then ((g i j : ℂ) + Complex.I * g j i) / (Real.sqrt 2 : ℝ)
      else ((g j i : ℂ) - Complex.I * g i j) / (Real.sqrt 2 : ℝ)

/-- The Gaussian ensemble is Hermitian for every array. -/
theorem gaussianEnsemble_isHermitian (β n : ℕ) (g : Fin n → Fin n → ℝ) :
    (gaussianEnsemble β n g).IsHermitian := by
  ext i j
  simp only [gaussianEnsemble, conjTranspose_apply, of_apply, star_mul', star_inv₀,
    Complex.star_def, Complex.conj_ofReal]
  rcases lt_trichotomy i j with h | h | h
  · by_cases hβ : β = 1 <;> simp [hβ, h, h.ne, h.ne', h.not_gt, sub_eq_add_neg]
  · subst h
    by_cases hβ : β = 1 <;> simp [hβ]
  · by_cases hβ : β = 1 <;> simp [hβ, h, h.ne, h.ne', h.not_gt, sub_eq_add_neg]

/-- For `n = 1` and `β = 1`, the single entry `√2 * g 0 0` of the ensemble is `N(0, 2)` when
`g 0 0` is a standard Gaussian. -/
theorem gaussianEnsemble_one_zero_zero_hasLaw {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} (g : Fin 1 → Fin 1 → Ω → ℝ) (hg : HasLaw (g 0 0) (gaussianReal 0 1) μ) :
    HasLaw (fun ω ↦ (gaussianEnsemble 1 1 (fun i j ↦ g i j ω) 0 0).re)
      (gaussianReal 0 2) μ := by
  have e : (fun ω ↦ (gaussianEnsemble 1 1 (fun i j ↦ g i j ω) 0 0).re) =
      fun ω ↦ Real.sqrt 2 * g 0 0 ω := by
    funext ω
    simp [gaussianEnsemble]
  have h : HasLaw (fun ω ↦ Real.sqrt 2 * g 0 0 ω) (gaussianReal (Real.sqrt 2 * 0)
      (NNReal.mk (Real.sqrt 2 ^ 2) (sq_nonneg _) * 1)) μ := gaussianReal_const_mul hg (Real.sqrt 2)
  rw [e]
  convert h using 2
  · simp
  · rw [mul_one]
    exact NNReal.eq (Real.sq_sqrt (by norm_num)).symm

/-- For `n = 1` and `β = 2`, the single entry `g 0 0` of the ensemble is `N(0, 1)` when `g 0 0` is
a standard Gaussian. -/
theorem gaussianEnsemble_two_zero_zero_hasLaw {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} (g : Fin 1 → Fin 1 → Ω → ℝ) (hg : HasLaw (g 0 0) (gaussianReal 0 1) μ) :
    HasLaw (fun ω ↦ (gaussianEnsemble 2 1 (fun i j ↦ g i j ω) 0 0).re)
      (gaussianReal 0 1) μ := by
  have e : (fun ω ↦ (gaussianEnsemble 2 1 (fun i j ↦ g i j ω) 0 0).re) = g 0 0 := by
    funext ω
    simp [gaussianEnsemble]
  rwa [e]

/-- The trace of the square of the Hermitian matrix `gaussianEnsemble β n g` is the sum of the
squared moduli of its entries. -/
theorem gaussianEnsemble_trace_sq (β n : ℕ) (g : Fin n → Fin n → ℝ) :
    ((gaussianEnsemble β n g) ^ 2).trace =
      ∑ i, ∑ j, (Complex.normSq (gaussianEnsemble β n g i j) : ℂ) := by
  have hH := gaussianEnsemble_isHermitian β n g
  simp only [sq, trace, diag_apply, mul_apply]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  have := congr_fun (congr_fun hH j) i
  rw [conjTranspose_apply] at this
  rw [← this, Complex.star_def, Complex.mul_conj]

/-- Entrywise squared moduli of the `β = 1` ensemble: `2 g i i ^ 2 / n` on the diagonal and
`g i j ^ 2 / n` above it. -/
theorem gaussianEnsemble_one_normSq_apply (n : ℕ) (g : Fin n → Fin n → ℝ) (i j : Fin n) :
    Complex.normSq (gaussianEnsemble 1 n g i j) =
      (if i = j then 2 * g i i ^ 2 else if i < j then g i j ^ 2 else g j i ^ 2) / n := by
  have h3 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs : Complex.normSq ((Real.sqrt n)⁻¹ : ℂ) = (n : ℝ)⁻¹ := by
    rw [← Complex.ofReal_inv, Complex.normSq_ofReal, ← mul_inv,
      Real.mul_self_sqrt (Nat.cast_nonneg n)]
  simp only [gaussianEnsemble, of_apply, map_mul, hs, ↓reduceIte]
  split_ifs <;> rw [Complex.normSq_ofReal] <;>
    first | linear_combination (g i i ^ 2 / n) * h3 | ring

/-- Entrywise squared moduli of the `β = 2` ensemble: `g i i ^ 2 / n` on the diagonal and
`(g i j ^ 2 + g j i ^ 2) / (2 n)` off it. -/
theorem gaussianEnsemble_two_normSq_apply (n : ℕ) (g : Fin n → Fin n → ℝ) (i j : Fin n) :
    Complex.normSq (gaussianEnsemble 2 n g i j) =
      (if i = j then g i i ^ 2 else (g i j ^ 2 + g j i ^ 2) / 2) / n := by
  have h3 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs : Complex.normSq ((Real.sqrt n)⁻¹ : ℂ) = (n : ℝ)⁻¹ := by
    rw [← Complex.ofReal_inv, Complex.normSq_ofReal, ← mul_inv,
      Real.mul_self_sqrt (Nat.cast_nonneg n)]
  have h21 : ¬ (2 : ℕ) = 1 := by norm_num
  have hadd : ∀ x y : ℝ, Complex.normSq (((x : ℂ) + Complex.I * y) / (Real.sqrt 2 : ℝ)) =
      (x ^ 2 + y ^ 2) / 2 := fun x y ↦ by
    rw [map_div₀, Complex.normSq_ofReal, mul_comm Complex.I, Complex.normSq_add_mul_I,
      Real.mul_self_sqrt (by norm_num)]
  have hsub : ∀ x y : ℝ, Complex.normSq (((x : ℂ) - Complex.I * y) / (Real.sqrt 2 : ℝ)) =
      (x ^ 2 + y ^ 2) / 2 := fun x y ↦ by
    have : (x : ℂ) - Complex.I * y = x + ((-y : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [this, map_div₀, Complex.normSq_ofReal, Complex.normSq_add_mul_I,
      Real.mul_self_sqrt (by norm_num)]
    ring
  simp only [gaussianEnsemble, of_apply, map_mul, hs, h21, ↓reduceIte]
  split_ifs
  · rw [Complex.normSq_ofReal]
    ring
  · rw [hadd]
    ring
  · rw [hsub]
    ring

/-- The expectation of the normalized trace of the square of `gaussianEnsemble β n g` is the
average of the expected squared moduli of its entries. -/
theorem integral_trace_sq_div_gaussianEnsemble {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} (β n : ℕ) (g : Fin n → Fin n → Ω → ℝ)
    (hint : ∀ i j, Integrable
      (fun ω ↦ Complex.normSq (gaussianEnsemble β n (fun a b ↦ g a b ω) i j)) μ) :
    ∫ ω, ((gaussianEnsemble β n (fun i j ↦ g i j ω) ^ 2).trace.re / n) ∂μ =
      (∑ i, ∑ j, ∫ ω, Complex.normSq (gaussianEnsemble β n (fun a b ↦ g a b ω) i j) ∂μ) / n := by
  have h : ∀ ω, (gaussianEnsemble β n (fun i j ↦ g i j ω) ^ 2).trace.re =
      ∑ i, ∑ j, Complex.normSq (gaussianEnsemble β n (fun a b ↦ g a b ω) i j) := by
    intro ω
    rw [gaussianEnsemble_trace_sq]
    simp [Complex.re_sum]
  simp_rw [h]
  rw [integral_div, integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hint i j]
  simp_rw [integral_finsetSum _ fun j _ ↦ hint _ j]

/-- The GUE has `E trₙ H² = 1`, where `trₙ = n⁻¹ tr`: it suffices that the entries of `g` have
second moment `1`. -/
theorem integral_trace_sq_div_gaussianEnsemble_two {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} {n : ℕ} (hn : 0 < n) (g : Fin n → Fin n → Ω → ℝ)
    (hint : ∀ i j, Integrable (fun ω ↦ g i j ω ^ 2) μ) (hvar : ∀ i j, ∫ ω, g i j ω ^ 2 ∂μ = 1) :
    ∫ ω, ((gaussianEnsemble 2 n (fun i j ↦ g i j ω) ^ 2).trace.re / n) ∂μ = 1 := by
  have hI : ∀ i j, Integrable
      (fun ω ↦ Complex.normSq (gaussianEnsemble 2 n (fun a b ↦ g a b ω) i j)) μ := by
    intro i j
    simp only [gaussianEnsemble_two_normSq_apply]
    by_cases h : i = j
    · simp only [h, ↓reduceIte]
      exact (hint _ _).div_const _
    · simp only [h, ↓reduceIte]
      exact (((hint i j).add (hint j i)).div_const 2).div_const _
  have hE : ∀ i j, ∫ ω, Complex.normSq (gaussianEnsemble 2 n (fun a b ↦ g a b ω) i j) ∂μ =
      (n : ℝ)⁻¹ := by
    intro i j
    simp only [gaussianEnsemble_two_normSq_apply]
    rw [integral_div]
    by_cases h : i = j
    · simp [h, hvar]
    · simp only [h, ↓reduceIte]
      rw [integral_div, integral_add (hint i j) (hint j i), hvar, hvar]
      ring
  rw [integral_trace_sq_div_gaussianEnsemble 2 n g hI]
  simp only [hE, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- The GOE has `E trₙ H² = 1 + 1 / n`, where `trₙ = n⁻¹ tr`: it suffices that the entries of `g`
have second moment `1`. The diagonal entries have variance `2 / n` and the off-diagonal ones
`1 / n`. -/
theorem integral_trace_sq_div_gaussianEnsemble_one {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} {n : ℕ} (hn : 0 < n) (g : Fin n → Fin n → Ω → ℝ)
    (hint : ∀ i j, Integrable (fun ω ↦ g i j ω ^ 2) μ) (hvar : ∀ i j, ∫ ω, g i j ω ^ 2 ∂μ = 1) :
    ∫ ω, ((gaussianEnsemble 1 n (fun i j ↦ g i j ω) ^ 2).trace.re / n) ∂μ = 1 + 1 / n := by
  have hI : ∀ i j, Integrable
      (fun ω ↦ Complex.normSq (gaussianEnsemble 1 n (fun a b ↦ g a b ω) i j)) μ := by
    intro i j
    simp only [gaussianEnsemble_one_normSq_apply]
    by_cases h : i = j
    · simp only [h, ↓reduceIte]
      exact ((hint _ _).const_mul 2).div_const _
    · simp only [h, ↓reduceIte]
      by_cases h' : i < j
      · simp only [h', ↓reduceIte]
        exact (hint _ _).div_const _
      · simp only [h', ↓reduceIte]
        exact (hint _ _).div_const _
  have hE : ∀ i j, ∫ ω, Complex.normSq (gaussianEnsemble 1 n (fun a b ↦ g a b ω) i j) ∂μ =
      (1 + if i = j then 1 else 0) / n := by
    intro i j
    simp only [gaussianEnsemble_one_normSq_apply]
    rw [integral_div]
    by_cases h : i = j
    · simp [h, integral_const_mul, hvar]
      ring
    · by_cases h' : i < j <;> simp [h, h', hvar]
  rw [integral_trace_sq_div_gaussianEnsemble 1 n g hI]
  simp only [hE, ← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  field_simp

end Probability

end TauCeti
