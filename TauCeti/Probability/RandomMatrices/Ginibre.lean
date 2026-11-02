/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Probability.Distributions.Gaussian.Real
public import TauCeti.Analysis.Matrix.MeasurableSpace
public import TauCeti.MeasureTheory.Constructions.Pi
public import TauCeti.Probability.Distributions.Gaussian.ProperComplex.Modulus
public import TauCeti.Probability.Distributions.Gaussian.ProperComplex.Moments
public import TauCeti.Probability.Distributions.Wishart.Moments

/-!
# Ginibre matrices and Gaussian Gram matrices

The real Ginibre law on `m × n` matrices has independent standard Gaussian entries. The complex
Ginibre law has independent standard proper complex Gaussian entries, that is, independent
entries `(a + i b) / √2` with `a` and `b` independent standard Gaussians, so that each entry has
`E |z| ^ 2 = 1`. The complex Gaussian Gram law is the image of the complex Ginibre law under
`X ↦ X * Xᴴ`, without normalization. The real Gaussian Gram law is defined as the Wishart law
`wishartGramMeasure n 1`, the law of the Gram sum of `n` independent standard Gaussian vectors,
which we reuse instead of redefining.

## Main definitions

* `TauCeti.Probability.ginibreReal`: the real Ginibre law.
* `TauCeti.Probability.ginibreComplex`: the complex Ginibre law, the image of
  `properComplexGaussianMeasure 0 1` under reshaping into a matrix.
* `TauCeti.Probability.gaussianGramReal` and `TauCeti.Probability.gaussianGramComplex`: the
  Gaussian Gram laws.

## Main results

* `TauCeti.Probability.map_apply_ginibreReal`: the entries of the real Ginibre law are standard
  Gaussian.
* `TauCeti.Probability.map_re_apply_ginibreComplex` and
  `TauCeti.Probability.map_im_apply_ginibreComplex`: the real and imaginary parts of the complex
  Ginibre entries are `N(0, 1/2)`.
* `TauCeti.Probability.ae_posSemidef_gaussianGramReal` and
  `TauCeti.Probability.ae_posSemidef_gaussianGramComplex`: the Gram laws are supported on
  positive semidefinite matrices.
* `TauCeti.Probability.integral_trace_gaussianGramReal` and
  `TauCeti.Probability.integral_trace_re_gaussianGramComplex`: the expected trace of the Gram matrix
  of an `m × n` Ginibre matrix is `m * n`.
-/

public section

noncomputable section

open MeasureTheory Matrix ProbabilityTheory
open scoped ComplexOrder

namespace TauCeti

namespace Probability

/-- The real Ginibre law on `m × n` matrices: independent standard Gaussian entries. -/
def ginibreReal (m n : ℕ) : Measure (Matrix (Fin m) (Fin n) ℝ) :=
  Measure.pi fun _ ↦ Measure.pi fun _ ↦ gaussianReal 0 1

/-- The complex Ginibre law on `m × n` matrices: the standard proper complex Gaussian law on the
entries `(i, j)`, arranged as a matrix. -/
def ginibreComplex (m n : ℕ) : Measure (Matrix (Fin m) (Fin n) ℂ) :=
  (properComplexGaussianMeasure (0 : Fin m × Fin n → ℂ) 1).map
    fun z ↦ Matrix.of fun i j ↦ z (i, j)

/-- The real Gaussian Gram law: the Wishart law `wishartGramMeasure n 1`, the law of the Gram sum
of `n` independent standard Gaussian vectors in `ℝ ^ m`, viewed on `Matrix (Fin m) (Fin m) ℝ`. -/
def gaussianGramReal (m n : ℕ) : Measure (Matrix (Fin m) (Fin m) ℝ) :=
  (wishartGramMeasure n (1 : Matrix (Fin m) (Fin m) ℝ)).map Subtype.val

/-- The complex Gaussian Gram law: the law of `X * Xᴴ` for `X` with the complex Ginibre law. -/
def gaussianGramComplex (m n : ℕ) : Measure (Matrix (Fin m) (Fin m) ℂ) :=
  (ginibreComplex m n).map fun X ↦ X * Xᴴ

instance (m n : ℕ) : IsProbabilityMeasure (ginibreReal m n) := by
  unfold ginibreReal
  exact Measure.pi.instIsProbabilityMeasure fun _ : Fin m ↦
    Measure.pi fun _ : Fin n ↦ gaussianReal 0 1

private lemma measurable_ginibreComplexEntries {m n : ℕ} :
    Measurable fun z : Fin m × Fin n → ℂ ↦ Matrix.of fun i j ↦ z (i, j) :=
  Measurable.of_eval_matrix _ fun _ _ ↦ measurable_pi_apply _

instance (m n : ℕ) : IsProbabilityMeasure (ginibreComplex m n) :=
  (Measure.isProbabilityMeasure_map_iff measurable_ginibreComplexEntries.aemeasurable).2
    inferInstance

instance (m n : ℕ) : IsProbabilityMeasure (gaussianGramReal m n) :=
  (Measure.isProbabilityMeasure_map_iff measurable_subtype_coe.aemeasurable).2 inferInstance

instance (m n : ℕ) : IsProbabilityMeasure (gaussianGramComplex m n) :=
  (Measure.isProbabilityMeasure_map_iff measurable_matrix_mul_conjTranspose.aemeasurable).2
    inferInstance

/-- Each entry of a real Ginibre matrix is a standard Gaussian. -/
theorem map_apply_ginibreReal (m n : ℕ) (i : Fin m) (j : Fin n) :
    (ginibreReal m n).map (fun X ↦ X i j) = gaussianReal 0 1 :=
  (measurePreserving_eval_eval (gaussianReal 0 1) i j).map_eq

/-- The real part of an entry of a complex Ginibre matrix is `N(0, 1/2)`. -/
theorem map_re_apply_ginibreComplex (m n : ℕ) (i : Fin m) (j : Fin n) :
    (ginibreComplex m n).map (fun X ↦ (X i j).re) = gaussianReal 0 (1 / 2) := by
  have h := congrArg (Measure.map Prod.fst)
    (map_re_im_sub_eval_properComplexGaussianMeasure (0 : Fin m × Fin n → ℂ)
      Matrix.PosSemidef.one (i, j))
  rw [Measure.map_map measurable_fst (by fun_prop), Measure.map_fst_prod] at h
  rw [ginibreComplex, Measure.map_map (by fun_prop) measurable_ginibreComplexEntries]
  simpa [Function.comp_def, Real.toNNReal_inv] using h

/-- The imaginary part of an entry of a complex Ginibre matrix is `N(0, 1/2)`. -/
theorem map_im_apply_ginibreComplex (m n : ℕ) (i : Fin m) (j : Fin n) :
    (ginibreComplex m n).map (fun X ↦ (X i j).im) = gaussianReal 0 (1 / 2) := by
  have h := congrArg (Measure.map Prod.snd)
    (map_re_im_sub_eval_properComplexGaussianMeasure (0 : Fin m × Fin n → ℂ)
      Matrix.PosSemidef.one (i, j))
  rw [Measure.map_map measurable_snd (by fun_prop), Measure.map_snd_prod] at h
  rw [ginibreComplex, Measure.map_map (by fun_prop) measurable_ginibreComplexEntries]
  simpa [Function.comp_def, Real.toNNReal_inv] using h

/-- The expected trace of the Gaussian Gram matrix of an `m × n` real Ginibre matrix is `m * n`. -/
theorem integral_trace_gaussianGramReal (m n : ℕ) :
    ∫ A, A.trace ∂(gaussianGramReal m n) = m * n := by
  have hint : ∀ i, Integrable (fun A : selfAdjoint.submodule ℝ (Matrix (Fin m) (Fin m) ℝ) ↦
      (A : Matrix (Fin m) (Fin m) ℝ) i i) (wishartGramMeasure n 1) := fun i ↦
    (memLp_coe_apply_wishartGramMeasure 1 n i i 1).integrable le_rfl
  rw [gaussianGramReal, integral_map measurable_subtype_coe.aemeasurable
    (Continuous.aestronglyMeasurable (by fun_prop))]
  simp_rw [trace, diag_apply]
  rw [integral_finsetSum _ fun i _ ↦ hint i]
  simp [integral_coe_apply_wishartGramMeasure Matrix.PosSemidef.one n]

/-- The expected trace of the Gaussian Gram matrix of an `m × n` complex Ginibre matrix is
`m * n`; the trace is real, so we take its real part. -/
theorem integral_trace_re_gaussianGramComplex (m n : ℕ) :
    ∫ A, A.trace.re ∂(gaussianGramComplex m n) = m * n := by
  have hint : ∀ i j, Integrable (fun z : Fin m × Fin n → ℂ ↦ ‖z (i, j)‖ ^ 2)
      (properComplexGaussianMeasure 0 1) := fun i j ↦ by
    simpa using integrable_norm_sq_sub_eval_properComplexGaussianMeasure
      (0 : Fin m × Fin n → ℂ) 1 (i, j)
  have hval : ∀ i j, ∫ z : Fin m × Fin n → ℂ, ‖z (i, j)‖ ^ 2
      ∂properComplexGaussianMeasure 0 1 = 1 := fun i j ↦ by
    simpa using integral_norm_sq_sub_eval_properComplexGaussianMeasure
      (0 : Fin m × Fin n → ℂ) Matrix.PosSemidef.one (i, j)
  have e : ∀ X : Matrix (Fin m) (Fin n) ℂ,
      (X * Xᴴ).trace.re = ∑ i, ∑ j, ‖X i j‖ ^ 2 := fun X ↦ by
    simp only [trace, diag_apply, mul_apply, conjTranspose_apply, Complex.star_def,
      Complex.re_sum, Complex.mul_conj, Complex.normSq_eq_norm_sq,       Complex.ofReal_pow]
    norm_cast
  rw [gaussianGramComplex, integral_map measurable_matrix_mul_conjTranspose.aemeasurable
    (Continuous.aestronglyMeasurable (by fun_prop)), ginibreComplex,
    integral_map measurable_ginibreComplexEntries.aemeasurable
      (Continuous.aestronglyMeasurable (by simp_rw [e]; fun_prop))]
  simp_rw [e, of_apply]
  rw [integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hint i j]
  simp_rw [integral_finsetSum _ fun j _ ↦ hint _ j, hval]
  simp

/-- The real Gaussian Gram law is supported on positive semidefinite matrices. -/
theorem ae_posSemidef_gaussianGramReal (m n : ℕ) :
    ∀ᵐ A ∂(gaussianGramReal m n), A.PosSemidef := by
  rw [gaussianGramReal, ae_map_iff measurable_subtype_coe.aemeasurable
    (Matrix.posSemidef_is_closed (n := Fin m) (𝕜 := ℝ)).measurableSet]
  exact ae_posSemidef_wishartGramMeasure n 1

open scoped ComplexOrder in
/-- The complex Gaussian Gram law is supported on positive semidefinite matrices. -/
theorem ae_posSemidef_gaussianGramComplex (m n : ℕ) :
    ∀ᵐ A ∂(gaussianGramComplex m n), A.PosSemidef := by
  rw [gaussianGramComplex, ae_map_iff measurable_matrix_mul_conjTranspose.aemeasurable
    (Matrix.posSemidef_is_closed (n := Fin m) (𝕜 := ℂ)).measurableSet]
  exact Filter.Eventually.of_forall fun X ↦ posSemidef_self_mul_conjTranspose X

end Probability

end TauCeti
