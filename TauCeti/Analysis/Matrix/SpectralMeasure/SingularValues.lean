/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.SpectralMeasure.Basic
public import TauCeti.Analysis.Matrix.HoffmanWielandt
public import TauCeti.Analysis.Matrix.SingularValues
public import TauCeti.MeasureTheory.Measure.ProbabilityMeasure.Borel
public import TauCeti.MeasureTheory.Measure.ProbabilityMeasure.Map

import TauCeti.Analysis.Matrix.Eigenvalues.Gram
import TauCeti.Analysis.Matrix.Frobenius

/-!
# Empirical singular-value measures

`Matrix.singularValueMeasure A` is the empirical probability measure of the first `card n`
singular values of a rectangular matrix `A : Matrix m n 𝕜`. The normalization uses the domain
size, not the rank or the minimum of the two dimensions. Thus zeros are retained, including
those forced by having more columns than rows. Only the column index type must be nonempty.

Squaring sends this measure to the spectral measure of `Aᴴ * A`; conversely, taking square roots
of that Gram spectral measure gives the singular-value measure. Consequently the measure depends
continuously and measurably on the entries of `A`. These identities connect singular-value limits
with Gram-matrix spectral limits, as used in covariance laws and hermitization.

The squared-singular-value measure needs no separate definition: it is the existing
`Matrix.spectralMeasure` of `Aᴴ * A`. Lipschitz statistics satisfy a squared perturbation bound
by the squared Lipschitz constant times the average squared Frobenius error. This controls
bounded approximations of covariance spectra using only second moments. All singular values come
from Mathlib's `LinearMap.singularValues` via `Matrix.toEuclideanLin`.

For an invertible square matrix `B`, the mean logarithm of the singular values is
`(card n)⁻¹ * log ‖det B‖`, and for any matrix the mean logarithm of the Gram eigenvalues is twice
the mean logarithm of the singular values; these are the inputs to Girko's hermitization.

## References

* T. Tao, *Topics in Random Matrix Theory*, American Mathematical Society (2012), §2.7.
-/

public section

noncomputable section

open MeasureTheory TauCeti.Probability
open scoped ComplexOrder ENNReal Matrix.Norms.Frobenius NNReal

namespace Matrix

variable {m n 𝕜 : Type*} [Fintype m] [Fintype n] [DecidableEq n]
  [RCLike 𝕜] [Nonempty n]

/-- The empirical measure of the first `card n` singular values of an `m × n` matrix,
including zero singular values, with normalization `1 / card n`. -/
def singularValueMeasure (A : Matrix m n 𝕜) : ProbabilityMeasure ℝ :=
  empiricalMeasureOfFintype fun i : Fin (Fintype.card n) => (toEuclideanLin A).singularValues i

/-- The singular-value measure is the empirical measure of Mathlib's singular values,
truncated at the dimension of the domain. -/
theorem singularValueMeasure_def (A : Matrix m n 𝕜) :
    A.singularValueMeasure = empiricalMeasureOfFintype
      (fun i : Fin (Fintype.card n) => (toEuclideanLin A).singularValues i) :=
  (rfl)

/-- The singular-value measure is the square-root pushforward of the Gram spectral measure. -/
theorem map_spectralMeasure_conjTranspose_mul_self_sqrt (A : Matrix m n 𝕜) :
    ((Aᴴ * A).spectralMeasure (isHermitian_conjTranspose_mul_self A)).map Real.sqrt =
      A.singularValueMeasure := by
  rw [spectralMeasure_eq_empiricalMeasureOfFintype_eigenvalues₀,
    map_empiricalMeasureOfFintype Real.continuous_sqrt.measurable, singularValueMeasure_def]
  congr 1
  funext i
  rw [Function.comp_apply, eigenvalues₀_conjTranspose_mul_self_eq_sq_singularValues,
    Real.sqrt_sq (LinearMap.singularValues_nonneg _ _)]

/-- Squared singular values, with multiplicity and domain-size normalization, have exactly
the Gram spectral measure. -/
@[simp]
theorem map_singularValueMeasure_sq (A : Matrix m n 𝕜) :
    A.singularValueMeasure.map (fun x => x ^ 2) =
      (Aᴴ * A).spectralMeasure (isHermitian_conjTranspose_mul_self A) := by
  rw [← map_spectralMeasure_conjTranspose_mul_self_sqrt,
    spectralMeasure_eq_empiricalMeasureOfFintype_eigenvalues₀,
    map_empiricalMeasureOfFintype Real.continuous_sqrt.measurable,
    map_empiricalMeasureOfFintype (by fun_prop)]
  congr 1
  funext i
  exact Real.sq_sqrt ((posSemidef_conjTranspose_mul_self A).eigenvalues₀_nonneg i)

/-- The singular-value measure is weakly continuous as a function of the matrix entries. -/
@[fun_prop]
theorem continuous_singularValueMeasure :
    Continuous (singularValueMeasure : Matrix m n 𝕜 → ProbabilityMeasure ℝ) := by
  have hc : Continuous (fun A : Matrix m n 𝕜 =>
      ((Aᴴ * A).spectralMeasure (isHermitian_conjTranspose_mul_self A)).map Real.sqrt) :=
    (ProbabilityMeasure.continuous_map Real.continuous_sqrt).comp
      (continuous_spectralMeasure.comp
        ((continuous_id.matrix_conjTranspose.matrix_mul continuous_id).subtype_mk
          (fun A : Matrix m n 𝕜 => isHermitian_conjTranspose_mul_self A)))
  exact hc.congr map_spectralMeasure_conjTranspose_mul_self_sqrt

/-- The singular-value measure is measurable for the entrywise Borel structure on matrices
and the evaluation σ-algebra on probability measures. -/
@[fun_prop]
theorem measurable_singularValueMeasure [MeasurableSpace 𝕜] [BorelSpace 𝕜] :
    Measurable (singularValueMeasure : Matrix m n 𝕜 → ProbabilityMeasure ℝ) := by
  exact continuous_singularValueMeasure.measurable_probabilityMeasure

/-- Evaluating the singular-value measure counts singular values with multiplicity. -/
theorem singularValueMeasure_apply (A : Matrix m n 𝕜) {s : Set ℝ} (hs : MeasurableSet s) :
    (A.singularValueMeasure : Measure ℝ) s =
      (Fintype.card n : ℝ≥0∞)⁻¹ *
        ∑ i : Fin (Fintype.card n), s.indicator 1 ((toEuclideanLin A).singularValues i) := by
  rw [singularValueMeasure_def, empiricalMeasureOfFintype_apply hs, Fintype.card_fin]

/-- Integration against the singular-value measure is averaging over the singular values.
No regularity of the integrand is needed, since this is a finitely supported measure. -/
theorem integral_singularValueMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (A : Matrix m n 𝕜) (f : ℝ → E) :
    ∫ x, f x ∂(A.singularValueMeasure : Measure ℝ) =
      (Fintype.card n : ℝ)⁻¹ •
        ∑ i : Fin (Fintype.card n), f ((toEuclideanLin A).singularValues i) := by
  rw [singularValueMeasure_def,
    ← ProbabilityMeasure.toMeasure_comp_toFiniteMeasure_eq_toMeasure,
    toFiniteMeasure_empiricalMeasureOfFintype,
    integral_empiricalFiniteMeasure_of_measurableSingletonClass, Fintype.card_fin]

/-- The singular-value measure is concentrated on the nonnegative real axis. -/
theorem ae_nonneg_singularValueMeasure (A : Matrix m n 𝕜) :
    ∀ᵐ x ∂(A.singularValueMeasure : Measure ℝ), 0 ≤ x := by
  rw [← map_spectralMeasure_conjTranspose_mul_self_sqrt, ProbabilityMeasure.toMeasure_map]
  exact (ae_map_iff Real.continuous_sqrt.measurable.aemeasurable measurableSet_Ici).2
    (Filter.Eventually.of_forall fun _ => Real.sqrt_nonneg _)

/-- The second moment of the singular-value measure is the squared Frobenius norm divided by
the number of columns. -/
theorem lintegral_sq_singularValueMeasure (A : Matrix m n 𝕜) :
    ∫⁻ x, ENNReal.ofReal (x ^ 2) ∂(A.singularValueMeasure : Measure ℝ) =
      ENNReal.ofReal (‖A‖ ^ 2 / Fintype.card n) := by
  have hmap := congrArg (fun μ : ProbabilityMeasure ℝ ↦ (μ : Measure ℝ))
    (map_singularValueMeasure_sq A)
  rw [ProbabilityMeasure.toMeasure_map] at hmap
  rw [← lintegral_map (by fun_prop : Measurable ENNReal.ofReal) (by fun_prop), hmap]
  have htrace : RCLike.re (Aᴴ * A).trace = ‖A‖ ^ 2 := by
    rw [trace_mul_comm, re_trace_mul_conjTranspose_self, frobenius_norm_sq_eq_sum_norm_sq]
  rw [lintegral_spectralMeasure,
    ← ENNReal.ofReal_sum_of_nonneg
      (fun i _ ↦ (posSemidef_conjTranspose_mul_self A).eigenvalues_nonneg i),
    ← (isHermitian_conjTranspose_mul_self A).re_trace_eq_sum_eigenvalues, htrace]
  rw [div_eq_inv_mul, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_inv_of_pos (by positivity),
    ENNReal.ofReal_natCast]

/-- An invertible square matrix has strictly positive singular values. -/
theorem ae_pos_singularValueMeasure_of_det_ne_zero {A : Matrix n n 𝕜} (hA : A.det ≠ 0) :
    ∀ᵐ x ∂(A.singularValueMeasure : Measure ℝ), 0 < x := by
  rw [singularValueMeasure_def, empiricalMeasureOfFintype_toMeasure, ae_finsetSum_measure_iff]
  intro i _
  refine Measure.ae_smul_measure ?_ _
  exact (ae_dirac_iff measurableSet_Ioi).mpr
    (((toEuclideanLin A).singularValues_pos_iff_ne_zero i).mpr
      (A.det_ne_zero_iff_forall_singularValues_ne_zero.mp hA i))

/-- For an invertible square matrix, the mean logarithm of its singular values, with multiplicity,
is the normalized logarithm of the absolute value of its determinant. -/
theorem integral_log_singularValueMeasure_eq_log_norm_det {B : Matrix n n 𝕜} (hB : B.det ≠ 0) :
    ∫ s, Real.log s ∂(B.singularValueMeasure : Measure ℝ) =
      (Fintype.card n : ℝ)⁻¹ * Real.log ‖B.det‖ := by
  rw [integral_singularValueMeasure, norm_det_eq_prod_singularValues B,
    Real.log_prod (fun i _ ↦ B.det_ne_zero_iff_forall_singularValues_ne_zero.mp hB i), smul_eq_mul]

/-- The mean logarithm of the eigenvalues of the Gram matrix `Aᴴ * A` is twice the mean logarithm
of the singular values of `A`. Zero singular values contribute `Real.log 0 = 0` on both sides. -/
theorem integral_log_spectralMeasure_conjTranspose_mul_self (A : Matrix m n 𝕜) :
    ∫ x, Real.log x ∂((Aᴴ * A).spectralMeasure (isHermitian_conjTranspose_mul_self A) :
        Measure ℝ) =
      2 * ∫ s, Real.log s ∂(A.singularValueMeasure : Measure ℝ) := by
  rw [← map_singularValueMeasure_sq, ProbabilityMeasure.toMeasure_map,
    integral_map (by fun_prop) Real.measurable_log.aestronglyMeasurable]
  simp_rw [Real.log_pow, Nat.cast_ofNat]
  exact integral_const_mul _ _

/-- Left unitary multiplication preserves the singular-value measure. -/
@[simp]
theorem singularValueMeasure_unitary_mul [DecidableEq m] (A : Matrix m n 𝕜) (U : unitaryGroup m 𝕜) :
    ((U : Matrix m m 𝕜) * A).singularValueMeasure = A.singularValueMeasure := by
  simp only [singularValueMeasure_def, singularValues_toEuclideanLin_unitary_mul]

/-- Right unitary multiplication preserves the singular-value measure. -/
@[simp]
theorem singularValueMeasure_mul_unitary (A : Matrix m n 𝕜) (U : unitaryGroup n 𝕜) :
    (A * (U : Matrix n n 𝕜)).singularValueMeasure = A.singularValueMeasure := by
  simp only [singularValueMeasure_def, singularValues_toEuclideanLin_mul_unitary]

/-- For a `K`-Lipschitz test, the squared change in its singular-value statistic is at most
`K ^ 2 * ‖A - B‖ ^ 2 / card n`, with the Frobenius norm and domain-size normalization. -/
theorem sq_norm_integral_singularValueMeasure_sub_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A B : Matrix m n 𝕜) {K : ℝ≥0} {f : ℝ → E} (hf : LipschitzWith K f) :
    ‖∫ x, f x ∂(A.singularValueMeasure : Measure ℝ) -
        ∫ x, f x ∂(B.singularValueMeasure : Measure ℝ)‖ ^ 2 ≤
      (K : ℝ) ^ 2 * ‖A - B‖ ^ 2 / Fintype.card n := by
  by_cases hE : CompleteSpace E
  swap
  · simp only [integral_of_not_completeSpace hE, sub_self, norm_zero, zero_pow two_ne_zero]
    positivity
  let _ := hE
  let a := (toEuclideanLin A).singularValues
  let b := (toEuclideanLin B).singularValues
  have hN : (0 : ℝ) < Fintype.card n := Nat.cast_pos.mpr Fintype.card_pos
  have hnorm : ‖∑ i : Fin (Fintype.card n), (f (a i) - f (b i))‖ ≤
      (K : ℝ) * ∑ i : Fin (Fintype.card n), |a i - b i| := by
    rw [Finset.mul_sum]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ by
      simpa [← dist_eq_norm, Real.dist_eq] using hf.dist_le_mul (a i) (b i))
  have hcs := sq_sum_le_card_mul_sum_sq
    (s := Finset.univ) (f := fun i : Fin (Fintype.card n) ↦ |a i - b i|)
  simp only [Finset.card_univ, Fintype.card_fin, sq_abs] at hcs
  rw [integral_singularValueMeasure, integral_singularValueMeasure, ← smul_sub,
    ← Finset.sum_sub_distrib, norm_smul, Real.norm_of_nonneg (by positivity), mul_pow]
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  rw [mul_pow] at hsq
  have hbound := mul_le_mul_of_nonneg_left
    (sum_sq_singularValues_toEuclideanLin_sub_le_frobenius_norm_sub_sq A B
      (k := Fintype.card n)) hN.le
  have hcs' := mul_le_mul_of_nonneg_left (hcs.trans hbound) (sq_nonneg (K : ℝ))
  calc
    _ ≤ (Fintype.card n : ℝ)⁻¹ ^ 2 * ((K : ℝ) ^ 2 *
        ((Fintype.card n : ℝ) * ‖A - B‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left (hsq.trans hcs') (sq_nonneg _)
    _ = _ := by field_simp

/-- For a `K`-Lipschitz test, the change in its singular-value statistic is at most
`K * ‖A - B‖ / √(card n)`, with the Frobenius norm and domain-size normalization. -/
theorem norm_integral_singularValueMeasure_sub_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A B : Matrix m n 𝕜) {K : ℝ≥0} {f : ℝ → E} (hf : LipschitzWith K f) :
    ‖∫ x, f x ∂(A.singularValueMeasure : Measure ℝ) -
        ∫ x, f x ∂(B.singularValueMeasure : Measure ℝ)‖ ≤
      (K : ℝ) * ‖A - B‖ / Real.sqrt (Fintype.card n) := by
  have h := Real.le_sqrt_of_sq_le (sq_norm_integral_singularValueMeasure_sub_le A B hf)
  rw [Real.sqrt_div (by positivity), ← mul_pow, Real.sqrt_sq (by positivity)] at h
  exact h

/-- Weak convergence of Gram spectral laws is equivalent to weak convergence of the
singular-value laws, for any filter and a nonnegative reference law. -/
theorem tendsto_spectralMeasure_conjTranspose_mul_self_iff_tendsto_singularValueMeasure
    {ι : Type*} {p n : ι → Type*} [∀ i, Fintype (p i)] [∀ i, Fintype (n i)]
    [∀ i, DecidableEq (n i)] [∀ i, Nonempty (n i)]
    (A : (i : ι) → Matrix (p i) (n i) 𝕜) {l : Filter ι} {μ : ProbabilityMeasure ℝ}
    (hμ : ∀ᵐ x ∂(μ : Measure ℝ), 0 ≤ x) :
    Filter.Tendsto (fun i ↦ ((A i)ᴴ * A i).spectralMeasure
      (isHermitian_conjTranspose_mul_self (A i))) l (nhds μ) ↔
    Filter.Tendsto (fun i ↦ (A i).singularValueMeasure) l (nhds (μ.map Real.sqrt)) := by
  simpa only [map_spectralMeasure_conjTranspose_mul_self_sqrt] using
    ProbabilityMeasure.tendsto_iff_tendsto_map_sqrt
      (Filter.Eventually.of_forall fun i ↦
        (posSemidef_conjTranspose_mul_self (A i)).ae_mem_Ici_spectralMeasure) hμ

end Matrix
