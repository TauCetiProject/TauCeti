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
public import TauCeti.Probability.Distributions.Gaussian.ProperComplex.Modulus
public import TauCeti.Probability.Distributions.Gaussian.ProperComplex.Moments
public import TauCeti.Probability.Distributions.MatrixNormal.Basic
public import TauCeti.Probability.Distributions.Wishart.Moments
public import TauCeti.MeasureTheory.Constructions.Pi

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

* `TauCeti.Probability.map_apply_ginibreReal`: the entries of the real Ginibre law are standard
  Gaussian.
* `TauCeti.Probability.map_columns_ginibreReal`: its columns are independent standard Gaussian
  vectors.
* `TauCeti.Probability.gaussianGramReal_eq_map_ginibreReal`: the real Gaussian Gram law is the
  pushforward of the real Ginibre law under `X ↦ X * Xᵀ`.
* `TauCeti.Probability.map_apply_ginibreComplex` and
  `TauCeti.Probability.iIndepFun_apply_ginibreComplex`: the complex entries have the standard
  proper complex Gaussian law and are independent.
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

/-- The standard scalar proper complex Gaussian law, obtained as a coordinate of the proper
complex Gaussian with unit covariance. -/
def properComplexGaussianScalar : Measure ℂ :=
  (properComplexGaussianMeasure (fun _ : Unit ↦ (0 : ℂ)) 1).map fun z ↦ z ()

instance : IsProbabilityMeasure properComplexGaussianScalar := by
  unfold properComplexGaussianScalar
  infer_instance

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

/-- Reindexing independent standard Gaussian coordinates by columns gives independent standard
Gaussian vectors. -/
private theorem measurePreserving_pi_matrixColumns (m n : ℕ) :
    MeasurePreserving
      (fun z : Fin n × Fin m → ℝ ↦ fun j ↦ WithLp.toLp 2 fun i ↦ z (j, i))
      (Measure.pi fun _ : Fin n × Fin m ↦ gaussianReal 0 1)
      (Measure.pi fun _ : Fin n ↦
        (Measure.pi fun _ : Fin m ↦ gaussianReal 0 1).map (WithLp.toLp 2)) := by
  let e := Equiv.sigmaEquivProd (Fin n) (Fin m)
  let μ : Fin n × Fin m → Measure ℝ := fun _ ↦ gaussianReal 0 1
  have h₁ := (measurePreserving_piCongrLeft μ e).symm
  have h₂ := TauCeti.measurePreserving_piCurry
    (fun _ : Fin n ↦ fun _ : Fin m ↦ gaussianReal 0 1)
  have h := h₂.comp h₁
  have hfun :
      (MeasurableEquiv.piCurry (fun _ : Fin n ↦ fun _ : Fin m ↦ ℝ) ∘
        (MeasurableEquiv.piCongrLeft (fun _ : Fin n × Fin m ↦ ℝ) e).symm) =
        fun z : Fin n × Fin m → ℝ ↦ fun j i ↦ z (j, i) := by
    funext z j i
    rfl
  rw [hfun] at h
  have hpi : (Measure.pi fun j : Fin n ↦
      (Measure.pi fun i : Fin m ↦ gaussianReal 0 1).map (WithLp.toLp 2)) =
      (Measure.pi fun j : Fin n ↦
        Measure.pi fun i : Fin m ↦ gaussianReal 0 1).map
          (fun x j ↦ WithLp.toLp 2 (x j)) := by
    rw [Measure.pi_map_pi fun _ ↦ (WithLp.measurable_toLp 2 _).aemeasurable]
  refine ⟨(by fun_prop), ?_⟩
  calc
    _ = Measure.map (fun x j ↦ WithLp.toLp 2 (x j))
          (Measure.map (fun z j i ↦ z (j, i))
            (Measure.pi fun _ : Fin n × Fin m ↦ gaussianReal 0 1)) := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      rfl
    _ = Measure.map (fun x j ↦ WithLp.toLp 2 (x j))
          (Measure.pi fun j : Fin n ↦ Measure.pi fun i : Fin m ↦ gaussianReal 0 1) :=
      congrArg (Measure.map _) h.map_eq
    _ = _ := hpi.symm

/-- The columns of a real Ginibre matrix are independent standard Gaussian vectors. -/
theorem map_columns_ginibreReal (m n : ℕ) :
    (ginibreReal m n).map
      (fun X j ↦ WithLp.toLp 2 fun i : Fin m ↦ X i j) =
        Measure.pi fun _ : Fin n ↦ multivariateGaussian 0
          (1 : Matrix (Fin m) (Fin m) ℝ) := by
  let E : Matrix (Fin m) (Fin n) ℝ ≃ᵐ
      WithLp 2 (Fin n × Fin m → ℝ) := matrixVecMeasurableEquiv 2
  rw [ginibreReal_def, matrixNormalMeasure_of_posSemidef
    (0 : Matrix (Fin m) (Fin n) ℝ) Matrix.PosSemidef.one Matrix.PosSemidef.one,
    Measure.map_map (by fun_prop) E.symm.measurable]
  have hgauss :
      multivariateGaussian (WithLp.toLp 2 (0 : Matrix (Fin m) (Fin n) ℝ).vec)
        ((1 : Matrix (Fin n) (Fin n) ℝ) ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℝ)) =
          (Measure.pi fun _ : Fin n × Fin m ↦ gaussianReal 0 1).map (WithLp.toLp 2) := by
    simpa [Matrix.one_kronecker_one] using
      (multivariateGaussian_one_eq_map_pi
        (0 : EuclideanSpace ℝ (Fin n × Fin m)))
  rw [hgauss]
  have hregroup := measurePreserving_pi_matrixColumns m n
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  simp_rw [multivariateGaussian_one_eq_map_pi]
  calc
    _ = Measure.map (fun z j ↦ WithLp.toLp 2 fun i : Fin m ↦ z (j, i))
          (Measure.pi fun _ : Fin n × Fin m ↦ gaussianReal 0 1) := by
      congr 1
      funext z j
      ext i
      simp [E, matrixVecMeasurableEquiv_symm_apply]
    _ = _ := hregroup.map_eq

/-- The real Gaussian Gram law is the pushforward of the real Ginibre law under
`X ↦ X * Xᵀ`. -/
theorem gaussianGramReal_eq_map_ginibreReal (m n : ℕ) :
    gaussianGramReal m n =
      (ginibreReal m n).map fun X ↦ X * Xᵀ := by
  rw [gaussianGramReal_def, wishartGramMeasure_eq_map_pi,
    Measure.map_map measurable_subtype_coe measurable_wishartGram]
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

instance (m n : ℕ) : IsProbabilityMeasure (ginibreComplex m n) :=
  (Measure.isProbabilityMeasure_map_iff measurable_matrix_of_curry.aemeasurable).2
    inferInstance

instance (m n : ℕ) : IsProbabilityMeasure (gaussianGramReal m n) :=
  (Measure.isProbabilityMeasure_map_iff measurable_subtype_coe.aemeasurable).2 inferInstance

instance (m n : ℕ) : IsProbabilityMeasure (gaussianGramComplex m n) :=
  (Measure.isProbabilityMeasure_map_iff measurable_matrix_mul_conjTranspose.aemeasurable).2
    inferInstance

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
  rw [ginibreComplex_def, Measure.map_map (by fun_prop) measurable_matrix_of_curry]
  exact (measurePreserving_eval
    (fun _ : Fin m × Fin n ↦ properComplexGaussianScalar) (i, j)).map_eq

/-- The entries of a complex Ginibre matrix are independent. -/
theorem iIndepFun_apply_ginibreComplex (m n : ℕ) :
    iIndepFun (fun (p : Fin m × Fin n) (X : Matrix (Fin m) (Fin n) ℂ) ↦ X p.1 p.2)
      (ginibreComplex m n) := by
  have hmeas : ∀ p : Fin m × Fin n,
      AEMeasurable (fun X : Matrix (Fin m) (Fin n) ℂ ↦ X p.1 p.2)
        (ginibreComplex m n) := by
    intro p
    change AEMeasurable (fun X : Fin m → Fin n → ℂ ↦ X p.1 p.2) _
    exact ((measurable_pi_apply p.2).comp (measurable_pi_apply p.1)).aemeasurable
  apply (iIndepFun_iff_map_fun_eq_pi_map hmeas).2
  rw [ginibreComplex_def, Measure.map_map (by fun_prop) measurable_matrix_of_curry]
  calc
    _ = Measure.pi (fun _ : Fin m × Fin n ↦ properComplexGaussianScalar) := by
      have hfun :
          (fun X : Matrix (Fin m) (Fin n) ℂ ↦
            fun p : Fin m × Fin n ↦ X p.1 p.2) ∘
              (fun z : Fin m × Fin n → ℂ ↦ Matrix.of fun i j ↦ z (i, j)) = id := by
        funext z p
        rfl
      rw [hfun, Measure.map_id]
    _ = Measure.pi (fun p ↦
        (ginibreComplex m n).map (fun X ↦ X p.1 p.2)) := by
      congr 1
      funext p
      rw [map_apply_ginibreComplex]

/-- A standard scalar proper complex Gaussian has independent real and imaginary parts, each
`N(0, 1/2)`. -/
theorem map_re_im_properComplexGaussianScalar :
    properComplexGaussianScalar.map (fun z ↦ (z.re, z.im)) =
      (gaussianReal 0 (1 / 2)).prod (gaussianReal 0 (1 / 2)) := by
  have h := map_re_im_sub_eval_properComplexGaussianMeasure
    (fun _ : Unit ↦ (0 : ℂ)) (Matrix.PosSemidef.one : (1 : Matrix Unit Unit ℂ).PosSemidef) ()
  rw [properComplexGaussianScalar,
    Measure.map_map (by fun_prop) (by fun_prop)]
  simpa [Function.comp_def, Matrix.one_apply_eq, Real.toNNReal_inv] using h

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
  rw [gaussianGramReal, integral_map measurable_subtype_coe.aemeasurable
    (Continuous.aestronglyMeasurable (by fun_prop))]
  simpa [mul_comm] using
    (integral_trace_mul_wishartGramMeasure Matrix.PosSemidef.one
      (⟨1, Matrix.isSymm_one⟩ :
        selfAdjoint.submodule ℝ (Matrix (Fin m) (Fin m) ℝ)) n)

/-- The expected trace of the Gaussian Gram matrix of an `m × n` complex Ginibre matrix is
`m * n`; the trace is real, so we take its real part. -/
theorem integral_trace_re_gaussianGramComplex (m n : ℕ) :
    ∫ A, A.trace.re ∂(gaussianGramComplex m n) = m * n := by
  have hscalar_int : Integrable (fun z : ℂ ↦ ‖z‖ ^ 2) properComplexGaussianScalar := by
    rw [properComplexGaussianScalar]
    have hcont : Continuous (fun z : ℂ ↦ ‖z‖ ^ 2) := by fun_prop
    apply (integrable_map_measure (f := fun z : Unit → ℂ ↦ z ())
      (g := fun z : ℂ ↦ ‖z‖ ^ 2) hcont.aestronglyMeasurable
      (measurable_pi_apply ()).aemeasurable).2
    simpa [Function.comp_def] using integrable_norm_sq_sub_eval_properComplexGaussianMeasure
      (fun _ : Unit ↦ (0 : ℂ)) 1 ()
  have hscalar_val : ∫ z : ℂ, ‖z‖ ^ 2 ∂properComplexGaussianScalar = 1 := by
    rw [properComplexGaussianScalar,
      integral_map (measurable_pi_apply ()).aemeasurable (by fun_prop)]
    simpa using integral_norm_sq_sub_eval_properComplexGaussianMeasure
      (fun _ : Unit ↦ (0 : ℂ)) Matrix.PosSemidef.one ()
  have hint : ∀ i j, Integrable (fun z : Fin m × Fin n → ℂ ↦ ‖z (i, j)‖ ^ 2)
      (Measure.pi fun _ : Fin m × Fin n ↦ properComplexGaussianScalar) := by
    intro i j
    let e := measurePreserving_eval
      (fun _ : Fin m × Fin n ↦ properComplexGaussianScalar) (i, j)
    have hmap : Integrable (fun z : ℂ ↦ ‖z‖ ^ 2)
        ((Measure.pi fun _ : Fin m × Fin n ↦ properComplexGaussianScalar).map
          (fun z ↦ z (i, j))) := by
      rw [e.map_eq]
      exact hscalar_int
    have hcont : Continuous (fun z : ℂ ↦ ‖z‖ ^ 2) := by fun_prop
    exact (integrable_map_measure (f := fun z : Fin m × Fin n → ℂ ↦ z (i, j))
      (g := fun z : ℂ ↦ ‖z‖ ^ 2) hcont.aestronglyMeasurable
      (measurable_pi_apply (i, j)).aemeasurable).mp hmap
  have hval : ∀ i j,
      ∫ z : Fin m × Fin n → ℂ, ‖z (i, j)‖ ^ 2
        ∂(Measure.pi fun _ : Fin m × Fin n ↦ properComplexGaussianScalar) = 1 := by
    intro i j
    let e := measurePreserving_eval
      (fun _ : Fin m × Fin n ↦ properComplexGaussianScalar) (i, j)
    calc
      _ = ∫ z : ℂ, ‖z‖ ^ 2
          ∂((Measure.pi fun _ : Fin m × Fin n ↦ properComplexGaussianScalar).map
            (fun z ↦ z (i, j))) :=
        (integral_map (measurable_pi_apply (i, j)).aemeasurable (by fun_prop)).symm
      _ = 1 := by rw [e.map_eq]; exact hscalar_val
  have he : ∀ X : Matrix (Fin m) (Fin n) ℂ,
      (X * Xᴴ).trace.re = ∑ i, ∑ j, ‖X i j‖ ^ 2 := fun X ↦ by
    simpa using re_trace_mul_conjTranspose_self X
  rw [gaussianGramComplex, integral_map measurable_matrix_mul_conjTranspose.aemeasurable
    (Continuous.aestronglyMeasurable (by fun_prop)), ginibreComplex_def,
    integral_map measurable_matrix_of_curry.aemeasurable
      (Continuous.aestronglyMeasurable (by fun_prop))]
  simp_rw [he, of_apply]
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
