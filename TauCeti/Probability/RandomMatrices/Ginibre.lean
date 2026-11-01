/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Moments.Variance

/-!
# Ginibre matrices and Gaussian Gram matrices

The real Ginibre law on `m × n` matrices has independent standard Gaussian entries. The complex
Ginibre law has independent entries `(a + i b) / √2` with `a` and `b` independent standard
Gaussians, so that each entry has `E |z| ^ 2 = 1`. The Gaussian Gram laws are the images of these
laws under `X ↦ X * Xᴴ`, without normalization.

## Main definitions

* `TauCeti.Probability.ginibreReal`: the real Ginibre law.
* `TauCeti.Probability.ginibreComplex`: the complex Ginibre law.
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

namespace TauCeti

namespace Probability

/-- The real Ginibre law on `m × n` matrices: independent standard Gaussian entries. -/
def ginibreReal (m n : ℕ) : Measure (Matrix (Fin m) (Fin n) ℝ) :=
  Measure.pi fun _ ↦ Measure.pi fun _ ↦ gaussianReal 0 1

/-- The complex matrix with entries `(a + I * b) / √2` built from an array `G` of pairs `(a, b)`. -/
def complexEntries {m n : ℕ} (G : Fin m → Fin n → ℝ × ℝ) : Matrix (Fin m) (Fin n) ℂ :=
  Matrix.of fun i j ↦ (((G i j).1 : ℂ) + Complex.I * (G i j).2) / (Real.sqrt 2 : ℝ)

/-- The complex Ginibre law on `m × n` matrices: the entries are independent, and each is
`(a + I * b) / √2` for independent standard Gaussians `a` and `b`. -/
def ginibreComplex (m n : ℕ) : Measure (Matrix (Fin m) (Fin n) ℂ) :=
  (Measure.pi fun (_ : Fin m) ↦ Measure.pi fun (_ : Fin n) ↦
    (gaussianReal 0 1).prod (gaussianReal 0 1)).map complexEntries

/-- The real Gaussian Gram law: the law of `X * Xᵀ` for `X` with the real Ginibre law. -/
def gaussianGramReal (m n : ℕ) : Measure (Matrix (Fin m) (Fin m) ℝ) :=
  (ginibreReal m n).map fun X ↦ X * Xᴴ

/-- The complex Gaussian Gram law: the law of `X * Xᴴ` for `X` with the complex Ginibre law. -/
def gaussianGramComplex (m n : ℕ) : Measure (Matrix (Fin m) (Fin m) ℂ) :=
  (ginibreComplex m n).map fun X ↦ X * Xᴴ

instance (m n : ℕ) : IsProbabilityMeasure (ginibreReal m n) := by
  unfold ginibreReal
  exact Measure.pi.instIsProbabilityMeasure fun _ : Fin m ↦
    Measure.pi fun _ : Fin n ↦ gaussianReal 0 1

private lemma measurable_complexEntries {m n : ℕ} :
    Measurable (complexEntries (m := m) (n := n)) := by
  refine measurable_pi_iff.2 fun i ↦ measurable_pi_iff.2 fun j ↦ ?_
  unfold complexEntries
  fun_prop

instance (m n : ℕ) : IsProbabilityMeasure (ginibreComplex m n) := by
  unfold ginibreComplex
  exact (Measure.isProbabilityMeasure_map_iff measurable_complexEntries.aemeasurable).2
    inferInstance

private lemma measurable_mul_conjTranspose {𝕜 : Type*} [RCLike 𝕜] {m n : ℕ} :
    Measurable fun X : Matrix (Fin m) (Fin n) 𝕜 ↦ X * Xᴴ := by
  refine measurable_pi_iff.2 fun i ↦ measurable_pi_iff.2 fun j ↦ ?_
  simp only [mul_apply, conjTranspose_apply]
  fun_prop

instance (m n : ℕ) : IsProbabilityMeasure (gaussianGramReal m n) :=
  (Measure.isProbabilityMeasure_map_iff measurable_mul_conjTranspose.aemeasurable).2
    inferInstance

instance (m n : ℕ) : IsProbabilityMeasure (gaussianGramComplex m n) :=
  (Measure.isProbabilityMeasure_map_iff measurable_mul_conjTranspose.aemeasurable).2
    inferInstance

private lemma map_apply_pi_pi {α : Type*} {mα : MeasurableSpace α} (μ : Measure α)
    [IsProbabilityMeasure μ] (m n : ℕ) (i : Fin m) (j : Fin n) :
    (Measure.pi fun (_ : Fin m) ↦ Measure.pi fun (_ : Fin n) ↦ μ).map (fun X ↦ X i j) = μ :=
  ((measurePreserving_eval (fun _ : Fin n ↦ μ) j).comp
    (measurePreserving_eval (fun _ : Fin m ↦ Measure.pi fun _ : Fin n ↦ μ) i)).map_eq

/-- Each entry of a real Ginibre matrix is a standard Gaussian. -/
theorem map_apply_ginibreReal (m n : ℕ) (i : Fin m) (j : Fin n) :
    (ginibreReal m n).map (fun X ↦ X i j) = gaussianReal 0 1 :=
  map_apply_pi_pi (gaussianReal 0 1) m n i j

private lemma map_inv_sqrt_two_mul_comp (k : ℝ × ℝ → ℝ)
    (hk : MeasurePreserving k ((gaussianReal 0 1).prod (gaussianReal 0 1)) (gaussianReal 0 1))
    (m n : ℕ) (i : Fin m) (j : Fin n) :
    (Measure.pi fun (_ : Fin m) ↦ Measure.pi fun (_ : Fin n) ↦
      (gaussianReal 0 1).prod (gaussianReal 0 1)).map
      (fun G ↦ (Real.sqrt 2)⁻¹ * k (G i j)) = gaussianReal 0 (1 / 2) := by
  have h : (fun G : Fin m → Fin n → ℝ × ℝ ↦ (Real.sqrt 2)⁻¹ * k (G i j)) =
      (fun x : ℝ ↦ (Real.sqrt 2)⁻¹ * x) ∘ k ∘ (fun G ↦ G i j) := rfl
  rw [h, ← Measure.map_map (by fun_prop) (hk.measurable.comp (by fun_prop)),
    ← Measure.map_map hk.measurable (by fun_prop), map_apply_pi_pi, hk.map_eq,
    gaussianReal_map_const_mul]
  congr 1
  · simp
  · refine NNReal.eq ?_
    simp [Real.sq_sqrt]

private lemma complexEntries_apply_re {m n : ℕ} (G : Fin m → Fin n → ℝ × ℝ) (i : Fin m)
    (j : Fin n) : (complexEntries G i j).re = (Real.sqrt 2)⁻¹ * (G i j).1 := by
  rw [complexEntries, of_apply, Complex.div_ofReal_re, div_eq_inv_mul]
  simp

private lemma complexEntries_apply_im {m n : ℕ} (G : Fin m → Fin n → ℝ × ℝ) (i : Fin m)
    (j : Fin n) : (complexEntries G i j).im = (Real.sqrt 2)⁻¹ * (G i j).2 := by
  rw [complexEntries, of_apply, Complex.div_ofReal_im, div_eq_inv_mul]
  simp

/-- The real part of an entry of a complex Ginibre matrix is `N(0, 1/2)`. -/
theorem map_re_apply_ginibreComplex (m n : ℕ) (i : Fin m) (j : Fin n) :
    (ginibreComplex m n).map (fun X ↦ (X i j).re) = gaussianReal 0 (1 / 2) := by
  have h := map_inv_sqrt_two_mul_comp Prod.fst measurePreserving_fst m n i j
  rw [ginibreComplex, Measure.map_map (by fun_prop) measurable_complexEntries]
  convert h using 2
  funext G
  exact complexEntries_apply_re G i j

/-- The imaginary part of an entry of a complex Ginibre matrix is `N(0, 1/2)`. -/
theorem map_im_apply_ginibreComplex (m n : ℕ) (i : Fin m) (j : Fin n) :
    (ginibreComplex m n).map (fun X ↦ (X i j).im) = gaussianReal 0 (1 / 2) := by
  have h := map_inv_sqrt_two_mul_comp Prod.snd measurePreserving_snd m n i j
  rw [ginibreComplex, Measure.map_map (by fun_prop) measurable_complexEntries]
  convert h using 2
  funext G
  exact complexEntries_apply_im G i j

private lemma integral_sq_of_map_eq_gaussianReal {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} {Y : Ω → ℝ} (hY : Measurable Y) {v : NNReal}
    (h : μ.map Y = gaussianReal 0 v) :
    Integrable (fun ω ↦ Y ω * Y ω) μ ∧ ∫ ω, Y ω * Y ω ∂μ = v := by
  have hsq : Integrable (fun x : ℝ ↦ x * x) (gaussianReal 0 v) := by
    simpa [sq] using (memLp_id_gaussianReal (μ := 0) (v := v) 2).integrable_sq
  have hmap : ∫ ω, Y ω * Y ω ∂μ = ∫ x, x * x ∂(gaussianReal 0 v) := by
    rw [← h, integral_map hY.aemeasurable (by fun_prop)]
  refine ⟨?_, hmap.trans ?_⟩
  · rw [← h] at hsq
    exact (integrable_map_measure (by fun_prop) hY.aemeasurable).1 hsq
  · have hv := variance_id_gaussianReal (μ := 0) (v := v)
    rw [variance_of_integral_eq_zero aemeasurable_id (by simp [integral_id_gaussianReal])] at hv
    simpa [sq] using hv

/-- The expected trace of the Gaussian Gram matrix of an `m × n` real Ginibre matrix is `m * n`. -/
theorem integral_trace_gaussianGramReal (m n : ℕ) :
    ∫ A, A.trace ∂(gaussianGramReal m n) = m * n := by
  have hent : ∀ i j, Integrable (fun X : Matrix (Fin m) (Fin n) ℝ ↦ X i j * X i j)
      (ginibreReal m n) ∧ ∫ X, X i j * X i j ∂(ginibreReal m n) = 1 := fun i j ↦ by
    simpa using integral_sq_of_map_eq_gaussianReal (μ := ginibreReal m n) (Y := fun X ↦ X i j)
      (by fun_prop) (v := 1) (by simpa using map_apply_ginibreReal m n i j)
  rw [gaussianGramReal, integral_map measurable_mul_conjTranspose.aemeasurable
    (by exact (Continuous.aestronglyMeasurable (by fun_prop)))]
  have e : ∀ X : Matrix (Fin m) (Fin n) ℝ, (X * Xᴴ).trace = ∑ i, ∑ j, X i j * X i j := by
    intro X
    simp [trace, mul_apply]
  simp_rw [e]
  rw [integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ (hent i j).1]
  simp_rw [integral_finsetSum _ fun j _ ↦ (hent _ j).1, (hent _ _).2]
  simp

/-- The expected trace of the Gaussian Gram matrix of an `m × n` complex Ginibre matrix is
`m * n`; the trace is real, so we take its real part. -/
theorem integral_trace_re_gaussianGramComplex (m n : ℕ) :
    ∫ A, A.trace.re ∂(gaussianGramComplex m n) = m * n := by
  have hre : ∀ i j, Integrable (fun X : Matrix (Fin m) (Fin n) ℂ ↦ (X i j).re * (X i j).re)
      (ginibreComplex m n) ∧
      ∫ X, (X i j).re * (X i j).re ∂(ginibreComplex m n) = 1 / 2 := fun i j ↦ by
    simpa using integral_sq_of_map_eq_gaussianReal (μ := ginibreComplex m n)
      (Y := fun X ↦ (X i j).re) (by fun_prop) (v := 1 / 2)
      (by simpa using map_re_apply_ginibreComplex m n i j)
  have him : ∀ i j, Integrable (fun X : Matrix (Fin m) (Fin n) ℂ ↦ (X i j).im * (X i j).im)
      (ginibreComplex m n) ∧
      ∫ X, (X i j).im * (X i j).im ∂(ginibreComplex m n) = 1 / 2 := fun i j ↦ by
    simpa using integral_sq_of_map_eq_gaussianReal (μ := ginibreComplex m n)
      (Y := fun X ↦ (X i j).im) (by fun_prop) (v := 1 / 2)
      (by simpa using map_im_apply_ginibreComplex m n i j)
  have hent : ∀ i j, Integrable (fun X : Matrix (Fin m) (Fin n) ℂ ↦
      (X i j).re * (X i j).re + (X i j).im * (X i j).im) (ginibreComplex m n) ∧
      ∫ X, ((X i j).re * (X i j).re + (X i j).im * (X i j).im) ∂(ginibreComplex m n) = 1 :=
    fun i j ↦ ⟨(hre i j).1.add (him i j).1, by
      rw [integral_add (hre i j).1 (him i j).1, (hre i j).2, (him i j).2]
      norm_num⟩
  rw [gaussianGramComplex, integral_map measurable_mul_conjTranspose.aemeasurable
    (by exact (Continuous.aestronglyMeasurable (by fun_prop)))]
  have e : ∀ X : Matrix (Fin m) (Fin n) ℂ, (X * Xᴴ).trace.re =
      ∑ i, ∑ j, ((X i j).re * (X i j).re + (X i j).im * (X i j).im) := by
    intro X
    simp [trace, mul_apply, Complex.re_sum]
  simp_rw [e]
  rw [integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ (hent i j).1]
  simp_rw [integral_finsetSum _ fun j _ ↦ (hent _ j).1, (hent _ _).2]
  simp

private lemma isClosed_setOf_posSemidef_real {m : ℕ} :
    IsClosed {A : Matrix (Fin m) (Fin m) ℝ | A.PosSemidef} := by
  have h : {A : Matrix (Fin m) (Fin m) ℝ | A.PosSemidef} =
      {A | Aᴴ = A} ∩ ⋂ x : Fin m → ℝ, {A | 0 ≤ star x ⬝ᵥ A *ᵥ x} := by
    ext A
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter,
      posSemidef_iff_dotProduct_mulVec]
    rfl
  rw [h]
  refine (isClosed_eq (by fun_prop) continuous_id).inter (isClosed_iInter fun x ↦ ?_)
  exact isClosed_le continuous_const (by fun_prop)

/-- The real Gaussian Gram law is supported on positive semidefinite matrices. -/
theorem ae_posSemidef_gaussianGramReal (m n : ℕ) :
    ∀ᵐ A ∂(gaussianGramReal m n), A.PosSemidef := by
  rw [gaussianGramReal, ae_map_iff measurable_mul_conjTranspose.aemeasurable
    isClosed_setOf_posSemidef_real.measurableSet]
  exact Filter.Eventually.of_forall fun X ↦ posSemidef_self_mul_conjTranspose X

open scoped ComplexOrder in
private lemma isClosed_setOf_posSemidef_complex {m : ℕ} :
    IsClosed {A : Matrix (Fin m) (Fin m) ℂ | A.PosSemidef} := by
  have h : {A : Matrix (Fin m) (Fin m) ℂ | A.PosSemidef} =
      {A | Aᴴ = A} ∩ ⋂ x : Fin m → ℂ, {A | 0 ≤ star x ⬝ᵥ A *ᵥ x} := by
    ext A
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter,
      posSemidef_iff_dotProduct_mulVec]
    rfl
  rw [h]
  refine (isClosed_eq (by fun_prop) continuous_id).inter (isClosed_iInter fun x ↦ ?_)
  exact isClosed_le continuous_const (by fun_prop)

open scoped ComplexOrder in
/-- The complex Gaussian Gram law is supported on positive semidefinite matrices. -/
theorem ae_posSemidef_gaussianGramComplex (m n : ℕ) :
    ∀ᵐ A ∂(gaussianGramComplex m n), A.PosSemidef := by
  rw [gaussianGramComplex, ae_map_iff measurable_mul_conjTranspose.aemeasurable
    isClosed_setOf_posSemidef_complex.measurableSet]
  exact Filter.Eventually.of_forall fun X ↦ posSemidef_self_mul_conjTranspose X

end Probability

end TauCeti
