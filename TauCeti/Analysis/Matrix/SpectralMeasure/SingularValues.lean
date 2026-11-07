/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.SpectralMeasure.Basic
public import TauCeti.Analysis.Matrix.SingularValues
public import TauCeti.MeasureTheory.Measure.ProbabilityMeasure.Borel

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
`Matrix.spectralMeasure` of `Aᴴ * A`. All singular values come from Mathlib's
`LinearMap.singularValues` via `Matrix.toEuclideanLin`.

## References

* T. Tao, *Topics in Random Matrix Theory*, American Mathematical Society (2012), §2.7.
-/

public section

noncomputable section

open MeasureTheory TauCeti.Probability
open scoped ComplexOrder ENNReal

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
  rw [LinearMap.singularValues_fin _ finrank_euclideanSpace]
  congr 1
  -- Compare the adjoint Gram operator with the matrix Gram operator before taking eigenvalues.
  apply LinearMap.IsSymmetric.eigenvalues_congr
    (by
      classical
      rw [← toEuclideanLin_conjTranspose_eq_adjoint]
      exact toLpLin_mul_same 2 Aᴴ A)

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

end Matrix
