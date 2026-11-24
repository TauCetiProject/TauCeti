/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Probability.Distributions.Gaussian.Real
public import TauCeti.Analysis.Matrix.MeasurableSpace
public import TauCeti.Analysis.Matrix.Frobenius
public import TauCeti.MeasureTheory.Measure.Dirac
public import TauCeti.Probability.Distributions.Gaussian.ProperComplex.Modulus
public import TauCeti.Probability.Distributions.Gaussian.ProperComplex.Moments
public import TauCeti.Probability.Distributions.Gaussian.ProperComplex.Product
public import TauCeti.Probability.Distributions.Gaussian.Product
public import TauCeti.Probability.Distributions.MatrixNormal.Basic
public import TauCeti.Probability.Distributions.Wishart.Moments
public import TauCeti.Probability.Independence.Matrix

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
  a product of scalar proper complex Gaussian laws under reshaping into a matrix.
* `TauCeti.Probability.gaussianGramReal` and `TauCeti.Probability.gaussianGramComplex`: the
  Gaussian Gram laws.

## Main results

* `TauCeti.Probability.map_apply_ginibreReal` and
  `TauCeti.Probability.iIndepFun_apply_ginibreReal`: the entries of the real Ginibre law are
  independent standard Gaussians.
* `TauCeti.Probability.map_columns_ginibreReal`: its columns are independent standard Gaussian
  vectors.
* `TauCeti.Probability.gaussianGramReal_eq_map_ginibreReal`: the real Gaussian Gram law is the
  pushforward of the real Ginibre law under `X ↦ X * Xᵀ`.
* `TauCeti.Probability.map_apply_ginibreComplex` and
  `TauCeti.Probability.iIndepFun_apply_ginibreComplex`: the complex entries have the standard
  proper complex Gaussian law and are independent.
* `TauCeti.Probability.hasLaw_ginibreReal_iff` and
  `TauCeti.Probability.hasLaw_ginibreComplex_iff`:
  the independent-entry characterizations on arbitrary sample spaces.
* `TauCeti.Probability.map_vec_ginibreComplex` and
  `TauCeti.Probability.ginibreComplex_eq_map_properComplexGaussianMeasure`: vectorization and
  reshaping identify the law with the centered identity-covariance proper complex Gaussian.
* `TauCeti.Probability.map_re_apply_ginibreComplex` and
  `TauCeti.Probability.map_im_apply_ginibreComplex`: the real and imaginary parts of the complex
  Ginibre entries are `N(0, 1/2)`; the pair is a product law by
  `TauCeti.Probability.map_re_im_apply_ginibreComplex`.
* `TauCeti.Probability.ae_posSemidef_gaussianGramReal` and
  `TauCeti.Probability.ae_posSemidef_gaussianGramComplex`: the Gram laws are supported on
  positive semidefinite matrices.
* `TauCeti.Probability.integral_trace_gaussianGramReal`: the expected trace of the Wishart-defined
  real Gaussian Gram law is `m * n`.
* `TauCeti.Probability.integral_trace_re_gaussianGramComplex`: the expected trace of the Gram
  matrix of an `m × n` complex Ginibre matrix is `m * n`.
-/

public section

noncomputable section

open MeasureTheory Matrix ProbabilityTheory
open scoped ComplexOrder Kronecker

namespace TauCeti

namespace Probability

/-- The real Ginibre law on `m × n` matrices: independent standard Gaussian entries. -/
def ginibreReal (m n : ℕ) : Measure (Matrix (Fin m) (Fin n) ℝ) :=
  matrixNormalMeasure 0 1 1

/-- The real Ginibre law is the standard matrix normal law. -/
theorem ginibreReal_def (m n : ℕ) : ginibreReal m n = matrixNormalMeasure 0 1 1 :=
  (rfl)

/-- The real Ginibre law is a product of independent standard Gaussian scalars reshaped into
an `m × n` matrix. -/
theorem ginibreReal_eq_map_pi (m n : ℕ) :
    ginibreReal m n = (Measure.pi fun _ : Fin m × Fin n ↦ gaussianReal 0 1).map
      (fun z ↦ Matrix.of fun i j ↦ z (i, j)) := by
  have hswap := (TauCeti.measurePreserving_pi_comp_embedding
    (fun _ : Fin m × Fin n ↦ gaussianReal 0 1)
    (Equiv.prodComm (Fin n) (Fin m)).toEmbedding).map_eq
  have hgauss :
      multivariateGaussian (WithLp.toLp 2 (0 : Matrix (Fin m) (Fin n) ℝ).vec)
        ((1 : Matrix (Fin n) (Fin n) ℝ) ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℝ)) =
          (Measure.pi fun _ : Fin n × Fin m ↦ gaussianReal 0 1).map (WithLp.toLp 2) := by
    simpa [Matrix.one_kronecker_one] using
      (multivariateGaussian_one_eq_map_pi (0 : EuclideanSpace ℝ (Fin n × Fin m)))
  rw [ginibreReal_def, matrixNormalMeasure_of_posSemidef _ Matrix.PosSemidef.one
    Matrix.PosSemidef.one, hgauss, ← hswap,
    Measure.map_map (by fun_prop) (by fun_prop), Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext z
  ext i j
  simp [matrixVecMeasurableEquiv_symm_apply]

/-- The complex Ginibre law on `m × n` matrices: a product of standard proper complex Gaussian
entry laws, arranged as a matrix. -/
def ginibreComplex (m n : ℕ) : Measure (Matrix (Fin m) (Fin n) ℂ) :=
  (Measure.pi fun _ : Fin m × Fin n ↦ properComplexGaussianScalar).map
    fun z ↦ Matrix.of fun i j ↦ z (i, j)

/-- The complex Ginibre law as the pushforward of a product of scalar proper complex Gaussian
laws. -/
theorem ginibreComplex_def (m n : ℕ) :
    ginibreComplex m n =
      (Measure.pi fun _ : Fin m × Fin n ↦ properComplexGaussianScalar).map
        (fun z ↦ Matrix.of fun i j ↦ z (i, j)) :=
  (rfl)

/-- The real Gaussian Gram law: the Wishart law `wishartGramMeasure n 1`, the law of the Gram sum
of `n` independent standard Gaussian vectors in `ℝ ^ m`, viewed on `Matrix (Fin m) (Fin m) ℝ`. -/
def gaussianGramReal (m n : ℕ) : Measure (Matrix (Fin m) (Fin m) ℝ) :=
  (wishartGramMeasure n (1 : Matrix (Fin m) (Fin m) ℝ)).map Subtype.val

/-- The real Gaussian Gram law as the image of the corresponding Wishart law. -/
theorem gaussianGramReal_def (m n : ℕ) :
    gaussianGramReal m n =
      (wishartGramMeasure n (1 : Matrix (Fin m) (Fin m) ℝ)).map Subtype.val :=
  (rfl)

/-- The columns of a real Ginibre matrix are independent standard Gaussian vectors. -/
theorem map_columns_ginibreReal (m n : ℕ) :
    (ginibreReal m n).map
      (fun X j ↦ WithLp.toLp 2 fun i : Fin m ↦ X i j) =
        Measure.pi fun _ : Fin n ↦ multivariateGaussian 0
          (1 : Matrix (Fin m) (Fin m) ℝ) := by
  have hswap := (TauCeti.measurePreserving_pi_comp_embedding
    (fun _ : Fin m × Fin n ↦ gaussianReal 0 1)
    (Equiv.prodComm (Fin n) (Fin m)).toEmbedding).map_eq
  rw [ginibreReal_eq_map_pi, Measure.map_map (by fun_prop) (by fun_prop),
    ← map_pi_gaussianReal_to_vectors, ← hswap,
    Measure.map_map (by fun_prop) (by fun_prop)]
  exact congrArg (fun f ↦ Measure.map f _) (by
    funext z j
    ext i
    simp)

/-- The real Gaussian Gram law is the pushforward of the real Ginibre law under
`X ↦ X * Xᵀ`. -/
theorem gaussianGramReal_eq_map_ginibreReal (m n : ℕ) :
    gaussianGramReal m n =
      (ginibreReal m n).map fun X ↦ X * Xᵀ := by
  rw [gaussianGramReal_def, wishartGramMeasure_eq_map_pi,
    Measure.map_map measurable_subtypeVal measurable_wishartGram]
  rw [← map_columns_ginibreReal m n]
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext X
  ext i k
  simp [Matrix.mul_apply, Matrix.transpose_apply, coe_wishartGram, Matrix.sum_apply,
    Matrix.vecMulVec_apply]

/-- The complex Gaussian Gram law: the law of `X * Xᴴ` for `X` with the complex Ginibre law. -/
def gaussianGramComplex (m n : ℕ) : Measure (Matrix (Fin m) (Fin m) ℂ) :=
  (ginibreComplex m n).map fun X ↦ X * Xᴴ

/-- The complex Gaussian Gram law as a pushforward of the complex Ginibre law. -/
theorem gaussianGramComplex_def (m n : ℕ) :
    gaussianGramComplex m n = (ginibreComplex m n).map fun X ↦ X * Xᴴ :=
  (rfl)

instance (m n : ℕ) : IsProbabilityMeasure (ginibreReal m n) := by
  unfold ginibreReal
  infer_instance

instance (m n : ℕ) : IsProbabilityMeasure (ginibreComplex m n) := by
  have hreshape : Measurable
      (fun z : Fin m × Fin n → ℂ ↦ Matrix.of fun i j ↦ z (i, j)) :=
    (Matrix.ofMeasurableEquiv (Fin m) (Fin n) ℂ).measurable.comp measurable_curry
  exact (Measure.isProbabilityMeasure_map_iff hreshape.aemeasurable).2 inferInstance

instance (m n : ℕ) : IsProbabilityMeasure (gaussianGramReal m n) :=
  (Measure.isProbabilityMeasure_map_iff measurable_subtypeVal.aemeasurable).2 inferInstance

instance (m n : ℕ) : IsProbabilityMeasure (gaussianGramComplex m n) :=
  (Measure.isProbabilityMeasure_map_iff
    (measurable_matrix_mul_conjTranspose (R := ℂ) continuous_star.measurable).aemeasurable).2
    inferInstance

/-- With zero rows, the real Ginibre law is the point mass at zero. -/
@[simp]
theorem ginibreReal_zero_left (n : ℕ) : ginibreReal 0 n = Measure.dirac 0 := by
  rw [ginibreReal_def, matrixNormalMeasure_of_subsingleton]

/-- With zero columns, the real Ginibre law is the point mass at zero. -/
@[simp]
theorem ginibreReal_zero_right (m : ℕ) : ginibreReal m 0 = Measure.dirac 0 := by
  rw [ginibreReal_def, matrixNormalMeasure_of_subsingleton]

/-- With zero rows, the complex Ginibre law is the point mass at zero. -/
@[simp]
theorem ginibreComplex_zero_left (n : ℕ) : ginibreComplex 0 n = Measure.dirac 0 :=
  Measure.eq_dirac_of_subsingleton _ _

/-- With zero columns, the complex Ginibre law is the point mass at zero. -/
@[simp]
theorem ginibreComplex_zero_right (m : ℕ) : ginibreComplex m 0 = Measure.dirac 0 :=
  Measure.eq_dirac_of_subsingleton _ _

/-- With zero rows, the real Gaussian Gram law is the point mass at zero. -/
@[simp]
theorem gaussianGramReal_zero_left (n : ℕ) : gaussianGramReal 0 n = Measure.dirac 0 :=
  Measure.eq_dirac_of_subsingleton _ _

/-- With zero samples, the real Gaussian Gram law is the point mass at zero. -/
@[simp]
theorem gaussianGramReal_zero_right (m : ℕ) : gaussianGramReal m 0 = Measure.dirac 0 := by
  simp [gaussianGramReal_def, Measure.map_dirac' measurable_subtypeVal]

/-- With zero samples, the complex Gaussian Gram law is the point mass at zero. -/
@[simp]
theorem gaussianGramComplex_zero_right (m : ℕ) : gaussianGramComplex m 0 = Measure.dirac 0 := by
  rw [gaussianGramComplex_def, ginibreComplex_zero_right,
    Measure.map_dirac' (by fun_prop)]
  simp only [Matrix.conjTranspose_zero, Matrix.zero_mul]

/-- In zero dimension the complex Gaussian Gram law is the point mass at the empty matrix. -/
@[simp]
theorem gaussianGramComplex_zero_left (n : ℕ) : gaussianGramComplex 0 n = Measure.dirac 0 :=
  Measure.eq_dirac_of_subsingleton _ _

/-- Each entry of a real Ginibre matrix is a standard Gaussian. -/
theorem map_apply_ginibreReal (m n : ℕ) (i : Fin m) (j : Fin n) :
    (ginibreReal m n).map (fun X ↦ X i j) = gaussianReal 0 1 :=
  by
    rw [ginibreReal_def]
    simpa using
      (map_apply_matrixNormalMeasure (0 : Matrix (Fin m) (Fin n) ℝ)
        Matrix.PosSemidef.one Matrix.PosSemidef.one i j)

/-- Every complex Ginibre entry has the standard scalar proper complex Gaussian law. -/
theorem map_apply_ginibreComplex (m n : ℕ) (i : Fin m) (j : Fin n) :
    (ginibreComplex m n).map (fun X ↦ X i j) = properComplexGaussianScalar := by
  rw [ginibreComplex_def, Measure.map_map (by fun_prop) (by fun_prop)]
  exact (measurePreserving_eval
    (fun _ : Fin m × Fin n ↦ properComplexGaussianScalar) (i, j)).map_eq

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {m n : ℕ}

/-- A matrix has the real Ginibre law exactly when all its entries are independent
standard real Gaussians. No prior measurability of the whole matrix is required. -/
theorem hasLaw_ginibreReal_iff {X : Ω → Matrix (Fin m) (Fin n) ℝ} :
    HasLaw X (ginibreReal m n) P ↔
      iIndepFun (fun p : Fin m × Fin n ↦ fun ω ↦ X ω p.1 p.2) P ∧
        ∀ i j, HasLaw (fun ω ↦ X ω i j) (gaussianReal 0 1) P := by
  rw [ginibreReal_eq_map_pi, hasLaw_map_pi_matrix_iff]

/-- A matrix has the complex Ginibre law exactly when all its entries are independent
standard proper complex Gaussians. No prior measurability of the whole matrix is required. -/
theorem hasLaw_ginibreComplex_iff {X : Ω → Matrix (Fin m) (Fin n) ℂ} :
    HasLaw X (ginibreComplex m n) P ↔
      iIndepFun (fun p : Fin m × Fin n ↦ fun ω ↦ X ω p.1 p.2) P ∧
        ∀ i j, HasLaw (fun ω ↦ X ω i j) properComplexGaussianScalar P := by
  rw [ginibreComplex_def, hasLaw_map_pi_matrix_iff]

/-- The entries of a real Ginibre matrix are independent. -/
theorem iIndepFun_apply_ginibreReal (m n : ℕ) :
    iIndepFun (fun (p : Fin m × Fin n) (X : Matrix (Fin m) (Fin n) ℝ) ↦ X p.1 p.2)
      (ginibreReal m n) :=
  (hasLaw_ginibreReal_iff.mp HasLaw.id).1

/-- The entries of a complex Ginibre matrix are independent. -/
theorem iIndepFun_apply_ginibreComplex (m n : ℕ) :
    iIndepFun (fun (p : Fin m × Fin n) (X : Matrix (Fin m) (Fin n) ℂ) ↦ X p.1 p.2)
      (ginibreComplex m n) :=
  (hasLaw_ginibreComplex_iff.mp HasLaw.id).1

/-- Column-stacking a complex Ginibre matrix gives the centered identity-covariance
proper complex Gaussian vector. -/
theorem map_vec_ginibreComplex (m n : ℕ) :
    (ginibreComplex m n).map Matrix.vec =
      properComplexGaussianMeasure (0 : Fin n × Fin m → ℂ) 1 := by
  rw [ginibreComplex_def, Measure.map_map measurable_matrix_vec (by fun_prop),
    properComplexGaussianMeasure_zero_one_eq_pi]
  have hreshape :
      Matrix.vec ∘ (fun z : Fin m × Fin n → ℂ ↦ Matrix.of fun i j ↦ z (i, j)) =
        fun z p ↦ z ((Equiv.prodComm (Fin n) (Fin m)).toEmbedding p) := by
    funext z p
    rcases p with ⟨j, i⟩
    simp
  rw [hreshape]
  exact (TauCeti.measurePreserving_pi_comp_embedding
    (fun _ : Fin m × Fin n ↦ properComplexGaussianScalar)
    (Equiv.prodComm (Fin n) (Fin m)).toEmbedding).map_eq

/-- Reshaping the centered identity-covariance complex Gaussian vector gives the complex
Ginibre law. -/
theorem ginibreComplex_eq_map_properComplexGaussianMeasure (m n : ℕ) :
    ginibreComplex m n =
      (properComplexGaussianMeasure (0 : Fin m × Fin n → ℂ) 1).map
        (fun z ↦ Matrix.of fun i j ↦ z (i, j)) := by
  rw [properComplexGaussianMeasure_zero_one_eq_pi, ginibreComplex_def]

/-- The real and imaginary parts of a complex Ginibre entry have their joint product Gaussian
law. -/
theorem map_re_im_apply_ginibreComplex (m n : ℕ) (i : Fin m) (j : Fin n) :
    (ginibreComplex m n).map (fun X ↦ ((X i j).re, (X i j).im)) =
      (gaussianReal 0 (1 / 2)).prod (gaussianReal 0 (1 / 2)) := by
  calc
    _ = ((ginibreComplex m n).map (fun X ↦ X i j)).map
        (fun z ↦ (z.re, z.im)) := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      rfl
    _ = (gaussianReal 0 (1 / 2)).prod (gaussianReal 0 (1 / 2)) := by
      rw [map_apply_ginibreComplex]
      exact map_re_im_properComplexGaussianScalar

/-- The real part of an entry of a complex Ginibre matrix is `N(0, 1/2)`. -/
theorem map_re_apply_ginibreComplex (m n : ℕ) (i : Fin m) (j : Fin n) :
    (ginibreComplex m n).map (fun X ↦ (X i j).re) = gaussianReal 0 (1 / 2) := by
  calc
    _ = ((ginibreComplex m n).map
        (fun X ↦ ((X i j).re, (X i j).im))).map Prod.fst := by
      rw [Measure.map_map measurable_fst (by fun_prop)]
      rfl
    _ = gaussianReal 0 (1 / 2) := by
      rw [map_re_im_apply_ginibreComplex, Measure.map_fst_prod]
      simp

/-- The imaginary part of an entry of a complex Ginibre matrix is `N(0, 1/2)`. -/
theorem map_im_apply_ginibreComplex (m n : ℕ) (i : Fin m) (j : Fin n) :
    (ginibreComplex m n).map (fun X ↦ (X i j).im) = gaussianReal 0 (1 / 2) := by
  calc
    _ = ((ginibreComplex m n).map
        (fun X ↦ ((X i j).re, (X i j).im))).map Prod.snd := by
      rw [Measure.map_map measurable_snd (by fun_prop)]
      rfl
    _ = gaussianReal 0 (1 / 2) := by
      rw [map_re_im_apply_ginibreComplex, Measure.map_snd_prod]
      simp

/-- The expected trace of the Wishart-defined real Gaussian Gram law on `m × m` matrices is
`m * n`. -/
theorem integral_trace_gaussianGramReal (m n : ℕ) :
    ∫ A, A.trace ∂(gaussianGramReal m n) = m * n := by
  rw [gaussianGramReal, integral_map measurable_subtypeVal.aemeasurable
    (Continuous.aestronglyMeasurable (by fun_prop))]
  simpa [mul_comm] using
    (integral_trace_mul_wishartGramMeasure Matrix.PosSemidef.one
      (⟨1, Matrix.isSymm_one⟩ :
        selfAdjoint.submodule ℝ (Matrix (Fin m) (Fin m) ℝ)) n)

/-- The expected trace of the Gaussian Gram matrix of an `m × n` complex Ginibre matrix is
`m * n`; the trace is real, so we take its real part. -/
theorem integral_trace_re_gaussianGramComplex (m n : ℕ) :
    ∫ A, A.trace.re ∂(gaussianGramComplex m n) = m * n := by
  have hscalar_int := integrable_norm_sq_properComplexGaussianScalar
  have hscalar_val := integral_norm_sq_properComplexGaussianScalar
  have hint : ∀ i j, Integrable (fun z : Fin m × Fin n → ℂ ↦ ‖z (i, j)‖ ^ 2)
      (Measure.pi fun _ : Fin m × Fin n ↦ properComplexGaussianScalar) :=
    fun i j ↦ integrable_comp_eval
      (μ := fun _ : Fin m × Fin n ↦ properComplexGaussianScalar)
      (X := fun _ : Fin m × Fin n ↦ ℂ) (i := (i, j)) (E := ℝ)
      (f := fun z : ℂ ↦ ‖z‖ ^ 2) hscalar_int
  have hval : ∀ i j,
      ∫ z : Fin m × Fin n → ℂ, ‖z (i, j)‖ ^ 2
        ∂(Measure.pi fun _ : Fin m × Fin n ↦ properComplexGaussianScalar) = 1 :=
    fun i j ↦ by
      rw [integral_comp_eval (μ := fun _ : Fin m × Fin n ↦ properComplexGaussianScalar)
        (X := fun _ : Fin m × Fin n ↦ ℂ) (i := (i, j)) (E := ℝ)
        (f := fun z : ℂ ↦ ‖z‖ ^ 2)
        hscalar_int.aestronglyMeasurable, hscalar_val]
  have he : ∀ X : Matrix (Fin m) (Fin n) ℂ,
      (X * Xᴴ).trace.re = ∑ i, ∑ j, ‖X i j‖ ^ 2 := fun X ↦ by
    simpa using X.re_trace_mul_conjTranspose_self
  have hreshape : Measurable
      (fun z : Fin m × Fin n → ℂ ↦ Matrix.of fun i j ↦ z (i, j)) :=
    (Matrix.ofMeasurableEquiv (Fin m) (Fin n) ℂ).measurable.comp measurable_curry
  rw [gaussianGramComplex, integral_map
    (measurable_matrix_mul_conjTranspose (R := ℂ) continuous_star.measurable).aemeasurable
    (Continuous.aestronglyMeasurable (by fun_prop)), ginibreComplex_def,
    integral_map hreshape.aemeasurable
      (Continuous.aestronglyMeasurable (by fun_prop))]
  simp_rw [he]
  simp_rw [Matrix.of_apply]
  rw [integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hint i j]
  simp_rw [integral_finsetSum _ fun j _ ↦ hint _ j, hval]
  simp

/-- The real Gaussian Gram law is supported on positive semidefinite matrices. -/
theorem ae_posSemidef_gaussianGramReal (m n : ℕ) :
    ∀ᵐ A ∂(gaussianGramReal m n), A.PosSemidef := by
  rw [gaussianGramReal, ae_map_iff measurable_subtypeVal.aemeasurable
      _root_.isClosed_setOfPred_posSemidef.measurableSet]
  exact ae_posSemidef_wishartGramMeasure n 1

/-- The complex Gaussian Gram law is supported on positive semidefinite matrices. -/
theorem ae_posSemidef_gaussianGramComplex (m n : ℕ) :
    ∀ᵐ A ∂(gaussianGramComplex m n), A.PosSemidef := by
  rw [gaussianGramComplex, ae_map_iff
      (measurable_matrix_mul_conjTranspose (R := ℂ) continuous_star.measurable).aemeasurable
      _root_.isClosed_setOfPred_posSemidef.measurableSet]
  exact Filter.Eventually.of_forall fun X ↦ posSemidef_self_mul_conjTranspose X

end Probability

end TauCeti

namespace ProbabilityTheory

open TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {m n : ℕ}
  {X : Ω → Matrix (Fin m) (Fin n) ℂ}

/-- The Gram matrix of a real Ginibre random matrix has the real Gaussian Gram law. -/
theorem HasLaw.mul_transpose_self_ginibreReal {X : Ω → Matrix (Fin m) (Fin n) ℝ}
    (hX : HasLaw X (ginibreReal m n) P) :
    HasLaw (fun ω ↦ X ω * (X ω)ᵀ) (gaussianGramReal m n) P :=
  (HasLaw.mk (by fun_prop) (gaussianGramReal_eq_map_ginibreReal m n).symm).comp hX

/-- The Gram matrix of a complex Ginibre random matrix has the complex Gaussian Gram law. -/
theorem HasLaw.mul_conjTranspose_self_ginibreComplex {X : Ω → Matrix (Fin m) (Fin n) ℂ}
    (hX : HasLaw X (ginibreComplex m n) P) :
    HasLaw (fun ω ↦ X ω * (X ω)ᴴ) (gaussianGramComplex m n) P :=
  (HasLaw.mk (by fun_prop) (gaussianGramComplex_def m n).symm).comp hX

end ProbabilityTheory
