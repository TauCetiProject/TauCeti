/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import TauCeti.MeasureTheory.Measure.HermitianMatrix.Lebesgue
public import TauCeti.MeasureTheory.Measure.SymmetricMatrix.Orthogonal
public import TauCeti.Probability.RandomMatrices.GaussianEnsemble.Basic
import TauCeti.MeasureTheory.Constructions.Pi
import TauCeti.Probability.Distributions.Gaussian.Affine

/-!
# Laws, moments, conjugation invariance, and entry characterizations of the GOE and GUE

`TauCeti.Probability.gaussianEnsemble` builds an `n × n` matrix over `ℂ` from
`g : Fin n × Fin n → ℝ`: for `β = 1` a real symmetric matrix `TauCeti.Probability.goeMatrix n g`,
and for `β ≠ 1` a complex Hermitian matrix `TauCeti.Probability.gueMatrix n g`, bundled as
continuous ℝ-linear maps. Pushing standard Gaussian product measure forward gives `goeMeasure n`
and `gueMeasure n` on their real self-adjoint subspaces—each a rescaled `stdGaussian` (with explicit
`covarianceBilin` and `charFun`) invariant under orthogonal/unitary conjugation and characterized by
mutually independent Gaussian entries—and their ambient pushforward `gaussianEnsembleLaw β n`.

## Main definitions and results

* `TauCeti.Probability.goeMatrix`, `TauCeti.Probability.gueMatrix`,
  `TauCeti.Probability.goeMeasure`, `TauCeti.Probability.gueMeasure`, `gaussianEnsembleLaw`.
* `TauCeti.Probability.goeMeasure_eq_map_stdGaussian`,
  `TauCeti.Probability.gueMeasure_eq_map_stdGaussian`,
  `TauCeti.Probability.covarianceBilin_goeMeasure`,
  `TauCeti.Probability.covarianceBilin_gueMeasure`, `TauCeti.Probability.charFun_goeMeasure`,
  `TauCeti.Probability.charFun_gueMeasure`.
* `TauCeti.Probability.measurePreserving_symmetricConj_goeMeasure`,
  `TauCeti.Probability.measurePreserving_hermitianConj_gueMeasure`,
  `TauCeti.Probability.hasLaw_goeMeasure_iff`, `TauCeti.Probability.hasLaw_gueMeasure_iff`.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, §2.5.1.
-/

public section

noncomputable section

open MeasureTheory Matrix Module ProbabilityTheory
open scoped ComplexConjugate ENNReal NNReal RealInnerProductSpace

namespace TauCeti.Probability

/-- The continuous ℝ-linear map building a real symmetric matrix from upper-triangular
coordinates: `√2 / √n` on the diagonal and `1 / √n` above it. -/
private def goeUpperMatrix (n : ℕ) :
    (upperTriangle n → ℝ) →L[ℝ] selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ) :=
  (symmetricCoordinates n).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.piMap fun ij : upperTriangle n ↦
      ((Real.sqrt n)⁻¹ * (if ij.val.1 = ij.val.2 then Real.sqrt 2 else 1)) •
        ContinuousLinearMap.id ℝ ℝ)

private theorem goeUpperMatrix_apply (n : ℕ) (x : upperTriangle n → ℝ) :
    goeUpperMatrix n x = (symmetricCoordinates n).symm fun ij ↦
      (Real.sqrt n)⁻¹ * ((if ij.val.1 = ij.val.2 then Real.sqrt 2 else 1) * x ij) :=
  congrArg (symmetricCoordinates n).symm (funext fun _ ↦ mul_assoc _ _ _)

/-- The continuous ℝ-linear map building the GOE (`β = 1`) symmetric matrix: diagonal entries
`(√2 * g (i, i)) / √n` and off-diagonal entries `g (min i j, max i j) / √n`. -/
def goeMatrix (n : ℕ) :
    (Fin n × Fin n → ℝ) →L[ℝ] selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ) :=
  (goeUpperMatrix n).comp (Pi.compRightL ℝ (fun _ ↦ ℝ) Subtype.val)

/-- Defining formula for `TauCeti.Probability.goeMatrix`. -/
theorem goeMatrix_def (n : ℕ) (g : Fin n × Fin n → ℝ) :
    goeMatrix n g = (symmetricCoordinates n).symm fun ij ↦
      (Real.sqrt n)⁻¹ * ((if ij.val.1 = ij.val.2 then Real.sqrt 2 else 1) * g ij.val) :=
  goeUpperMatrix_apply n _

/-- Upper-triangular coordinates of `TauCeti.Probability.goeMatrix`. -/
theorem symmetricCoordinates_goeMatrix (n : ℕ) (g : Fin n × Fin n → ℝ) (ij : upperTriangle n) :
    symmetricCoordinates n (goeMatrix n g) ij =
      (Real.sqrt n)⁻¹ * ((if ij.val.1 = ij.val.2 then Real.sqrt 2 else 1) * g ij.val) := by
  rw [goeMatrix_def, ContinuousLinearEquiv.apply_symm_apply]

/-- Diagonal entries of `TauCeti.Probability.goeMatrix`. -/
@[simp] theorem coe_goeMatrix_apply_self {n : ℕ} (g : Fin n × Fin n → ℝ) (i : Fin n) :
    (goeMatrix n g : Matrix (Fin n) (Fin n) ℝ) i i =
      (Real.sqrt n)⁻¹ * (Real.sqrt 2 * g (i, i)) := by simp [goeMatrix_def]

/-- Strict upper-triangular entries (`i < j`) of `TauCeti.Probability.goeMatrix`. -/
@[simp] theorem coe_goeMatrix_apply_of_lt {n : ℕ} (g : Fin n × Fin n → ℝ) {i j : Fin n}
    (h : i < j) : (goeMatrix n g : Matrix (Fin n) (Fin n) ℝ) i j = (Real.sqrt n)⁻¹ * g (i, j) := by
  rw [goeMatrix_def, coe_symmetricCoordinates_symm_apply_of_le n _ h.le]; simp [h.ne]

/-- Strict lower-triangular entries (`j < i`) of `TauCeti.Probability.goeMatrix`. -/
@[simp] theorem coe_goeMatrix_apply_of_gt {n : ℕ} (g : Fin n × Fin n → ℝ) {i j : Fin n}
    (h : j < i) : (goeMatrix n g : Matrix (Fin n) (Fin n) ℝ) i j = (Real.sqrt n)⁻¹ * g (j, i) := by
  rw [goeMatrix_def, coe_symmetricCoordinates_symm_apply_of_ge n _ h.le]; simp [h.ne]

/-- Casting `TauCeti.Probability.goeMatrix` from `ℝ` to `ℂ` recovers `gaussianEnsemble 1 n g`. -/
@[simp] theorem map_ofReal_coe_goeMatrix (n : ℕ) (g : Fin n × Fin n → ℝ) :
    (goeMatrix n g : Matrix (Fin n) (Fin n) ℝ).map Complex.ofReal = gaussianEnsemble 1 n g := by
  ext i j; rcases lt_trichotomy i j with h | rfl | h <;> simp [*]

/-- Each entry of `goeMatrix n g` is the real part of `(gaussianEnsemble 1 n g i j)`. -/
theorem coe_goeMatrix_apply_eq_re_gaussianEnsemble_one (n : ℕ) (g : Fin n × Fin n → ℝ)
    (i j : Fin n) :
    (goeMatrix n g : Matrix (Fin n) (Fin n) ℝ) i j = (gaussianEnsemble 1 n g i j).re := by
  rw [← map_ofReal_coe_goeMatrix]; simp

/-- `TauCeti.Probability.goeMatrix` is continuous in the input array. -/
@[fun_prop] theorem continuous_goeMatrix (n : ℕ) : Continuous (goeMatrix n) :=
  (goeMatrix n).continuous

/-- `TauCeti.Probability.goeMatrix` is measurable in the input array. -/
@[fun_prop] theorem measurable_goeMatrix (n : ℕ) : Measurable (goeMatrix n) :=
  (goeMatrix n).measurable

/-- The continuous ℝ-linear map building the GUE (`β = 2`) complex Hermitian matrix. -/
def gueMatrix (n : ℕ) :
    (Fin n × Fin n → ℝ) →L[ℝ] selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun g := ⟨gaussianEnsemble 2 n g,
        Matrix.isHermitian_iff_isSelfAdjoint.mp (isHermitian_gaussianEnsemble 2 n g)⟩
      map_add' g₁ g₂ := Subtype.ext (gaussianEnsemble_add g₁ g₂)
      map_smul' c g := Subtype.ext (gaussianEnsemble_smul c g) }

/-- Defining formula for `TauCeti.Probability.gueMatrix`. -/
theorem gueMatrix_def (n : ℕ) (g : Fin n × Fin n → ℝ) :
    gueMatrix n g = ⟨gaussianEnsemble 2 n g,
      Matrix.isHermitian_iff_isSelfAdjoint.mp (isHermitian_gaussianEnsemble 2 n g)⟩ := (rfl)

/-- Underlying complex matrix of `TauCeti.Probability.gueMatrix`. -/
@[simp] theorem coe_gueMatrix (n : ℕ) (g : Fin n × Fin n → ℝ) :
    (gueMatrix n g : Matrix (Fin n) (Fin n) ℂ) = gaussianEnsemble 2 n g := (rfl)

/-- Real coordinates of `TauCeti.Probability.gueMatrix` in `TauCeti.hermitianCoordinates`. -/
theorem hermitianCoordinates_gueMatrix (n : ℕ) (g : Fin n × Fin n → ℝ) (ij : Fin n × Fin n) :
    hermitianCoordinates n (gueMatrix n g) ij =
      (Real.sqrt n)⁻¹ * ((if ij.1 = ij.2 then 1 else (Real.sqrt 2)⁻¹) * g ij) := by
  obtain ⟨i, j⟩ := ij; rcases lt_trichotomy i j with h | rfl | h
  · rw [hermitianCoordinates_apply_of_le n _ h.le, coe_gueMatrix,
      gaussianEnsemble_apply_of_lt_of_ne_one g (by decide) h, ← Complex.ofReal_inv,
      div_eq_mul_inv, ← Complex.ofReal_inv]
    simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, h.ne, ↓reduceIte]; ring
  · rw [hermitianCoordinates_apply_of_le n _ le_rfl, coe_gueMatrix,
      gaussianEnsemble_apply_self_of_ne_one g (by decide) i, ← Complex.ofReal_inv,
      ← Complex.ofReal_mul, Complex.ofReal_re]; simp only [↓reduceIte, one_mul]
  · rw [hermitianCoordinates_apply_of_gt n _ h, coe_gueMatrix,
      im_gaussianEnsemble_of_lt_of_ne_one g (by decide) h]; simp only [h.ne', ↓reduceIte]

/-- `TauCeti.Probability.gueMatrix` is continuous in the input array. -/
@[fun_prop] theorem continuous_gueMatrix (n : ℕ) : Continuous (gueMatrix n) :=
  (gueMatrix n).continuous

/-- `TauCeti.Probability.gueMatrix` is measurable in the input array. -/
@[fun_prop] theorem measurable_gueMatrix (n : ℕ) : Measurable (gueMatrix n) :=
  (gueMatrix n).measurable

/-- `goeMatrix` expands in `symmetricOrthonormalBasis` with global scale `√2 / √n`. -/
theorem goeMatrix_eq_smul_sum_orthonormalBasis (n : ℕ) (g : Fin n × Fin n → ℝ) :
    goeMatrix n g = (Real.sqrt 2 / Real.sqrt n) •
      ∑ ij : upperTriangle n, g ij.val • symmetricOrthonormalBasis n ij := by
  refine (symmetricCoordinates n).injective (funext fun kl ↦ ?_)
  rw [symmetricCoordinates_goeMatrix, map_smul, map_sum]
  simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, symmetricOrthonormalBasis_apply,
    map_smul, symmetricBasis_apply, ContinuousLinearEquiv.apply_symm_apply, Pi.single_apply,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  by_cases hd : kl.val.1 = kl.val.2
  · simp only [hd, ↓reduceIte]; ring
  · simp only [hd, ↓reduceIte, one_mul, div_eq_mul_inv]
    calc (Real.sqrt n)⁻¹ * g kl.val
        = (Real.sqrt 2 * (Real.sqrt 2)⁻¹) * ((Real.sqrt n)⁻¹ * g kl.val) := by
          rw [mul_inv_cancel₀ (by positivity), one_mul]
      _ = Real.sqrt 2 * (Real.sqrt n)⁻¹ * (g kl.val * (Real.sqrt 2)⁻¹) := by ring

/-- `gueMatrix` expands in `hermitianOrthonormalBasis` with global scale `(√n)⁻¹`. -/
theorem gueMatrix_eq_smul_sum_orthonormalBasis (n : ℕ) (g : Fin n × Fin n → ℝ) :
    gueMatrix n g =
      (Real.sqrt n)⁻¹ • ∑ ij : Fin n × Fin n, g ij • hermitianOrthonormalBasis n ij := by
  refine (hermitianCoordinates n).injective (funext fun kl ↦ ?_)
  rw [hermitianCoordinates_gueMatrix, map_smul, map_sum]
  simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, hermitianOrthonormalBasis_apply,
    map_smul, hermitianBasis_apply, ContinuousLinearEquiv.apply_symm_apply, Pi.single_apply,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  by_cases hd : kl.1 = kl.2 <;> simp only [hd, ↓reduceIte] <;> ring

/-- The **Gaussian orthogonal ensemble** (`β = 1`) law on `n × n` real symmetric matrices. -/
def goeMeasure (n : ℕ) : Measure (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)) :=
  (Measure.pi fun _ : Fin n × Fin n ↦ gaussianReal 0 1).map (goeMatrix n)

/-- Defining formula for `TauCeti.Probability.goeMeasure`. -/
theorem goeMeasure_def (n : ℕ) :
    goeMeasure n = (Measure.pi fun _ : Fin n × Fin n ↦ gaussianReal 0 1).map (goeMatrix n) := (rfl)

/-- The **Gaussian unitary ensemble** (`β = 2`) law on `n × n` complex Hermitian matrices. -/
def gueMeasure (n : ℕ) : Measure (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) :=
  (Measure.pi fun _ : Fin n × Fin n ↦ gaussianReal 0 1).map (gueMatrix n)

/-- Defining formula for `TauCeti.Probability.gueMeasure`. -/
theorem gueMeasure_def (n : ℕ) :
    gueMeasure n = (Measure.pi fun _ : Fin n × Fin n ↦ gaussianReal 0 1).map (gueMatrix n) := (rfl)

/-- The ambient complex-matrix law of `TauCeti.Probability.gaussianEnsemble β n` under independent
standard Gaussian inputs. -/
def gaussianEnsembleLaw (β n : ℕ) : Measure (Matrix (Fin n) (Fin n) ℂ) :=
  (Measure.pi fun _ : Fin n × Fin n ↦ gaussianReal 0 1).map (gaussianEnsemble β n)

/-- Defining formula for `TauCeti.Probability.gaussianEnsembleLaw`. -/
theorem gaussianEnsembleLaw_def (β n : ℕ) :
    gaussianEnsembleLaw β n =
      (Measure.pi fun _ : Fin n × Fin n ↦ gaussianReal 0 1).map (gaussianEnsemble β n) := (rfl)

instance isProbabilityMeasure_goeMeasure (n : ℕ) : IsProbabilityMeasure (goeMeasure n) := by
  rw [goeMeasure_def]; infer_instance

instance isProbabilityMeasure_gueMeasure (n : ℕ) : IsProbabilityMeasure (gueMeasure n) := by
  rw [gueMeasure_def]; infer_instance

instance isProbabilityMeasure_gaussianEnsembleLaw (β n : ℕ) :
    IsProbabilityMeasure (gaussianEnsembleLaw β n) := by
  rw [gaussianEnsembleLaw_def]; infer_instance

private abbrev castSym (n : ℕ) (A : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)) :
    Matrix (Fin n) (Fin n) ℂ := (A : Matrix (Fin n) (Fin n) ℝ).map Complex.ofReal

private theorem measurable_castSym (n : ℕ) : Measurable (castSym n) :=
  (continuous_matrix fun i j ↦
    Complex.continuous_ofReal.comp (selfAdjoint.continuous_coe_apply i j)).measurable

/-- The ambient `β = 1` law is the cast pushforward of `TauCeti.Probability.goeMeasure`. -/
theorem gaussianEnsembleLaw_one_eq_map_goeMeasure (n : ℕ) :
    gaussianEnsembleLaw 1 n =
      (goeMeasure n).map fun A : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ) ↦
        (A : Matrix (Fin n) (Fin n) ℝ).map Complex.ofReal := by
  rw [gaussianEnsembleLaw_def, goeMeasure_def,
    Measure.map_map (measurable_castSym n) (measurable_goeMatrix n)]
  exact congrArg (Measure.map · _) (funext fun g ↦ (map_ofReal_coe_goeMatrix n g).symm)

/-- For `β ≠ 1`, `gaussianEnsembleLaw β n` is the subtype-coercion pushforward of `gueMeasure n`. -/
theorem gaussianEnsembleLaw_eq_map_gueMeasure {β : ℕ} (hβ : β ≠ 1) (n : ℕ) :
    gaussianEnsembleLaw β n = (gueMeasure n).map Subtype.val := by
  rw [gaussianEnsembleLaw_def, gueMeasure_def,
    Measure.map_map measurable_subtypeVal (measurable_gueMatrix n)]
  exact congrArg (Measure.map · _) (funext (gaussianEnsemble_eq_gaussianEnsemble_two_of_ne_one hβ))

/-- The ambient `β = 2` law is the subtype-coercion pushforward of `gueMeasure`. -/
theorem gaussianEnsembleLaw_two_eq_map_gueMeasure (n : ℕ) :
    gaussianEnsembleLaw 2 n = (gueMeasure n).map Subtype.val :=
  gaussianEnsembleLaw_eq_map_gueMeasure (by decide) n

/-- `goeMeasure n` is the pushforward of standard Gaussian product measure on `upperTriangle n`. -/
theorem goeMeasure_eq_map_pi_upperTriangle (n : ℕ) :
    goeMeasure n =
      (Measure.pi fun _ : upperTriangle n ↦ gaussianReal 0 1).map fun x ↦
        (symmetricCoordinates n).symm fun ij ↦
          (Real.sqrt n)⁻¹ * ((if ij.val.1 = ij.val.2 then Real.sqrt 2 else 1) * x ij) := by
  have hproj := measurePreserving_pi_comp_embedding (fun _ : Fin n × Fin n ↦ gaussianReal 0 1)
    (Function.Embedding.subtype fun ij : Fin n × Fin n ↦ ij.1 ≤ ij.2)
  simp_rw [← goeUpperMatrix_apply]
  rw [← hproj.map_eq, Measure.map_map (goeUpperMatrix n).continuous.measurable hproj.measurable,
    goeMeasure_def]
  exact congrArg (Measure.map · _)
    (funext fun g ↦ (goeMatrix_def n g).trans (goeUpperMatrix_apply n _).symm)

private theorem hasLaw_goeMatrix_of_upperTriangle_smul {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {n : ℕ} (g : Fin n × Fin n → Ω → ℝ) {v : ℝ≥0}
    (hindep : iIndepFun (fun (ij : upperTriangle n) ω ↦ g ij.val ω) P)
    (hlaw : ∀ ij : upperTriangle n, HasLaw (g ij.val) (gaussianReal 0 v) P) :
    HasLaw (fun ω ↦ goeMatrix n (fun p ↦ g p ω))
      ((goeMeasure n).map (Real.sqrt v • ·)) P := by
  have hfun : (fun ω ↦ goeMatrix n (fun p ↦ g p ω)) =
      fun ω ↦ goeUpperMatrix n (fun ij ↦ g ij.val ω) :=
    funext fun ω ↦ rfl
  rw [hfun, goeMeasure_eq_map_pi_upperTriangle]
  simp_rw [← goeUpperMatrix_apply]
  rw [Measure.map_map (measurable_const_smul _) (goeUpperMatrix n).continuous.measurable,
    show (Real.sqrt v • ·) ∘ ⇑(goeUpperMatrix n) = ⇑(goeUpperMatrix n) ∘ (Real.sqrt v • ·) from
      funext fun x ↦ ((goeUpperMatrix n).map_smul (Real.sqrt v) x).symm,
    ← Measure.map_map (goeUpperMatrix n).continuous.measurable (measurable_const_smul _),
    ← pi_gaussianReal_zero_eq_map_smul]
  exact (hasLaw_map (goeUpperMatrix n).continuous.measurable.aemeasurable).fun_comp
    (hindep.hasLaw_pi hlaw)

/-- Independent standard Gaussian upper-triangular entries give `goeMeasure n`. -/
theorem hasLaw_goeMatrix_of_upperTriangle {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}
    (g : Fin n × Fin n → Ω → ℝ) (hindep : iIndepFun (fun (ij : upperTriangle n) ω ↦ g ij.val ω) P)
    (hlaw : ∀ ij : upperTriangle n, HasLaw (g ij.val) (gaussianReal 0 1) P) :
    HasLaw (fun ω ↦ goeMatrix n (fun p ↦ g p ω)) (goeMeasure n) P := by
  simpa using hasLaw_goeMatrix_of_upperTriangle_smul g hindep hlaw

/-- Independent standard Gaussian entries give `goeMeasure n`. -/
theorem hasLaw_goeMatrix {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}
    (g : Fin n × Fin n → Ω → ℝ) (hindep : iIndepFun g P)
    (hlaw : ∀ ij : Fin n × Fin n, HasLaw (g ij) (gaussianReal 0 1) P) :
    HasLaw (fun ω ↦ goeMatrix n (fun p ↦ g p ω)) (goeMeasure n) P :=
  (hasLaw_map (measurable_goeMatrix n).aemeasurable).fun_comp (hindep.hasLaw_pi hlaw)

/-- Independent standard Gaussian entries give `gueMeasure n`. -/
theorem hasLaw_gueMatrix {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}
    (g : Fin n × Fin n → Ω → ℝ) (hindep : iIndepFun g P)
    (hlaw : ∀ ij : Fin n × Fin n, HasLaw (g ij) (gaussianReal 0 1) P) :
    HasLaw (fun ω ↦ gueMatrix n (fun p ↦ g p ω)) (gueMeasure n) P :=
  (hasLaw_map (measurable_gueMatrix n).aemeasurable).fun_comp (hindep.hasLaw_pi hlaw)

/-- `goeMeasure n` is `stdGaussian` on the real symmetric subspace rescaled by `√2 / √n`. -/
theorem goeMeasure_eq_map_stdGaussian (n : ℕ) :
    goeMeasure n =
      (stdGaussian (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ))).map
        ((Real.sqrt 2 / Real.sqrt n) • ·) := by
  have hx (x : upperTriangle n → ℝ) (ij : upperTriangle n) :
      (if h : ij.val.1 ≤ ij.val.2 then x ⟨ij.val, h⟩ else 0) = x ij := dite_eq_left ij.property
  rw [goeMeasure_eq_map_pi_upperTriangle,
    stdGaussian_eq_map_pi_orthonormalBasis (symmetricOrthonormalBasis n),
    Measure.map_map (by fun_prop) (by fun_prop)]
  refine congrArg (Measure.map · _) (funext fun x ↦ ?_)
  simpa [goeMatrix_def, hx] using
    goeMatrix_eq_smul_sum_orthonormalBasis n fun p ↦ if h : p.1 ≤ p.2 then x ⟨p, h⟩ else 0

/-- `gueMeasure n` is `stdGaussian` on the complex Hermitian subspace rescaled by `(√n)⁻¹`. -/
theorem gueMeasure_eq_map_stdGaussian (n : ℕ) :
    gueMeasure n =
      (stdGaussian (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ))).map
        ((Real.sqrt n)⁻¹ • ·) := by
  rw [stdGaussian_eq_map_pi_orthonormalBasis (hermitianOrthonormalBasis n),
    Measure.map_map (by fun_prop) (by fun_prop), gueMeasure_def]
  exact congrArg (Measure.map · _) (funext (gueMatrix_eq_smul_sum_orthonormalBasis n))

/-- `TauCeti.Probability.goeMeasure` is a Gaussian measure on the real symmetric subspace. -/
instance isGaussian_goeMeasure (n : ℕ) : IsGaussian (goeMeasure n) := by
  rw [goeMeasure_eq_map_stdGaussian]
  exact isGaussian_map_smul _

/-- `TauCeti.Probability.gueMeasure` is a Gaussian measure on the complex Hermitian subspace. -/
instance isGaussian_gueMeasure (n : ℕ) : IsGaussian (gueMeasure n) := by
  rw [gueMeasure_eq_map_stdGaussian]
  exact isGaussian_map_smul _

/-- Characteristic function of `TauCeti.Probability.goeMeasure n`. -/
theorem charFun_goeMeasure (n : ℕ)
    (Θ : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)) :
    charFun (goeMeasure n) Θ = Complex.exp (-(‖Θ‖ : ℂ) ^ 2 / n) := by
  rw [goeMeasure_eq_map_stdGaussian, charFun_map_smul, charFun_stdGaussian,
    ← Complex.ofReal_pow, norm_smul, Real.norm_of_nonneg (by positivity), mul_pow, div_pow,
    Real.sq_sqrt (by positivity), Real.sq_sqrt (Nat.cast_nonneg n)]
  push_cast; simp only [div_eq_mul_inv]; exact congrArg Complex.exp (by ring)

/-- Characteristic function of `TauCeti.Probability.gueMeasure n`. -/
theorem charFun_gueMeasure (n : ℕ)
    (Θ : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) :
    charFun (gueMeasure n) Θ = Complex.exp (-(‖Θ‖ : ℂ) ^ 2 / (2 * n)) := by
  rw [gueMeasure_eq_map_stdGaussian, charFun_map_smul, charFun_stdGaussian,
    ← Complex.ofReal_pow, norm_smul, Real.norm_of_nonneg (by positivity), mul_pow, inv_pow,
    Real.sq_sqrt (Nat.cast_nonneg n)]
  push_cast; simp only [div_eq_mul_inv, mul_inv]; exact congrArg Complex.exp (by ring)

private theorem gaussian_charFun_goeMeasure (n : ℕ) :
    (0 : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)) = ∫ H, H ∂goeMeasure n ∧
      (2 / (n : ℝ)) • innerSL ℝ = covarianceBilin (goeMeasure n) := by
  refine gaussian_charFun_congr 0 _
    ⟨⟨fun x y ↦ by simp [innerSL_apply_apply ℝ, real_inner_comm]⟩,
      ⟨fun x ↦ by simp only [ContinuousLinearMap.toBilinForm_apply, smul_apply,
        innerSL_apply_apply ℝ, smul_eq_mul, real_inner_self_eq_norm_sq]; positivity⟩⟩ fun Θ ↦ ?_
  rw [charFun_goeMeasure]; simp only [inner_zero_right, Complex.ofReal_zero, zero_mul, zero_sub,
    smul_apply, innerSL_apply_apply ℝ, smul_eq_mul, real_inner_self_eq_norm_sq]
  push_cast; simp only [div_eq_mul_inv]; exact congrArg Complex.exp (by ring)

private theorem gaussian_charFun_gueMeasure (n : ℕ) :
    (0 : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) = ∫ H, H ∂gueMeasure n ∧
      (n : ℝ)⁻¹ • innerSL ℝ = covarianceBilin (gueMeasure n) := by
  refine gaussian_charFun_congr 0 _
    ⟨⟨fun x y ↦ by simp [innerSL_apply_apply ℝ, real_inner_comm]⟩,
      ⟨fun x ↦ by simp only [ContinuousLinearMap.toBilinForm_apply, smul_apply,
        innerSL_apply_apply ℝ, smul_eq_mul, real_inner_self_eq_norm_sq]; positivity⟩⟩ fun Θ ↦ ?_
  rw [charFun_gueMeasure]; simp only [inner_zero_right, Complex.ofReal_zero, zero_mul, zero_sub,
    smul_apply, innerSL_apply_apply ℝ, smul_eq_mul, real_inner_self_eq_norm_sq]
  push_cast; simp only [div_eq_mul_inv, mul_inv]; exact congrArg Complex.exp (by ring)

/-- `TauCeti.Probability.goeMeasure` is centered. -/
@[simp] theorem integral_id_goeMeasure (n : ℕ) : ∫ H, H ∂goeMeasure n = 0 :=
  (gaussian_charFun_goeMeasure n).1.symm

/-- `TauCeti.Probability.gueMeasure` is centered. -/
@[simp] theorem integral_id_gueMeasure (n : ℕ) : ∫ H, H ∂gueMeasure n = 0 :=
  (gaussian_charFun_gueMeasure n).1.symm

/-- Covariance bilinear form of `TauCeti.Probability.goeMeasure n`. -/
theorem covarianceBilin_goeMeasure (n : ℕ) :
    covarianceBilin (goeMeasure n) = (2 / (n : ℝ)) • innerSL ℝ :=
  (gaussian_charFun_goeMeasure n).2.symm

/-- Covariance bilinear form of `TauCeti.Probability.gueMeasure n`. -/
theorem covarianceBilin_gueMeasure (n : ℕ) :
    covarianceBilin (gueMeasure n) = (n : ℝ)⁻¹ • innerSL ℝ :=
  (gaussian_charFun_gueMeasure n).2.symm

/-- In dimension zero, `TauCeti.Probability.goeMeasure` is the Dirac mass at zero. -/
@[simp] theorem goeMeasure_zero : goeMeasure 0 = Measure.dirac 0 := by
  rw [goeMeasure_eq_map_stdGaussian]; simp

/-- In dimension zero, `TauCeti.Probability.gueMeasure` is the Dirac mass at zero. -/
@[simp] theorem gueMeasure_zero : gueMeasure 0 = Measure.dirac 0 := by
  rw [gueMeasure_eq_map_stdGaussian]; simp

/-- In dimension zero, `TauCeti.Probability.gaussianEnsembleLaw` is the Dirac mass at zero. -/
@[simp] theorem gaussianEnsembleLaw_zero (β : ℕ) : gaussianEnsembleLaw β 0 = Measure.dirac 0 := by
  by_cases hβ : β = 1
  · subst hβ; simp [gaussianEnsembleLaw_one_eq_map_goeMeasure]
  · simp [gaussianEnsembleLaw_eq_map_gueMeasure hβ]

/-- In dimension one, reading the single entry of `goeMeasure 1` gives `N(0, 2)`. -/
@[simp] theorem map_symmetricFinOneEquiv_goeMeasure :
    (goeMeasure 1).map symmetricFinOneEquiv = gaussianReal 0 2 := by
  have hcomp : ⇑symmetricFinOneEquiv ∘ ⇑(goeMatrix 1) = (Real.sqrt 2 * ·) ∘ fun g ↦ g (0, 0) :=
    funext fun g ↦ by simp
  rw [goeMeasure_def,
    Measure.map_map symmetricFinOneEquiv.continuous.measurable (measurable_goeMatrix 1), hcomp,
    ← Measure.map_map (by fun_prop) (by fun_prop),
    (measurePreserving_eval (fun _ : Fin 1 × Fin 1 ↦ gaussianReal 0 1) (0, 0)).map_eq]
  exact gaussianReal_zero_one_map_const_mul _ (by simp)

/-- In dimension one, reading the single real entry of `gueMeasure 1` gives `N(0, 1)`. -/
@[simp] theorem map_hermitianFinOneEquiv_gueMeasure :
    (gueMeasure 1).map hermitianFinOneEquiv = gaussianReal 0 1 := by
  have hcomp : ⇑hermitianFinOneEquiv ∘ ⇑(gueMatrix 1) = fun g ↦ g (0, 0) :=
    funext fun g ↦ by simp
  rw [gueMeasure_def,
    Measure.map_map hermitianFinOneEquiv.continuous.measurable (measurable_gueMatrix 1), hcomp,
    (measurePreserving_eval (fun _ : Fin 1 × Fin 1 ↦ gaussianReal 0 1) (0, 0)).map_eq]

/-- Orthogonal conjugation `A ↦ U * A * Uᵀ` preserves `TauCeti.Probability.goeMeasure n`. -/
theorem measurePreserving_symmetricConj_goeMeasure {n : ℕ} (U : Matrix.orthogonalGroup (Fin n) ℝ) :
    MeasurePreserving (Matrix.UnitaryGroup.symmetricConj U) (goeMeasure n) (goeMeasure n) := by
  rw [goeMeasure_eq_map_stdGaussian]
  exact (Matrix.UnitaryGroup.symmetricConj U).measurePreserving_map_smul_stdGaussian _

/-- Pushing `goeMeasure` forward along orthogonal conjugation leaves it unchanged. -/
@[simp] theorem map_symmetricConj_goeMeasure {n : ℕ} (U : Matrix.orthogonalGroup (Fin n) ℝ) :
    (goeMeasure n).map (Matrix.UnitaryGroup.symmetricConj U) = goeMeasure n :=
  (measurePreserving_symmetricConj_goeMeasure U).map_eq

/-- Orthogonal conjugation preserves `HasLaw` for `TauCeti.Probability.goeMeasure`. -/
theorem _root_.ProbabilityTheory.HasLaw.symmetricConj_goeMeasure {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {n : ℕ} {H : Ω → selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)}
    (hH : HasLaw H (goeMeasure n) P) (U : Matrix.orthogonalGroup (Fin n) ℝ) :
    HasLaw (fun ω ↦ Matrix.UnitaryGroup.symmetricConj U (H ω)) (goeMeasure n) P :=
  (measurePreserving_symmetricConj_goeMeasure U).fun_comp_hasLaw hH

/-- A random symmetric matrix has law `goeMeasure` iff its orthogonal conjugate does. -/
@[simp] theorem hasLaw_symmetricConj_goeMeasure_iff {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {n : ℕ} {H : Ω → selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)}
    (U : Matrix.orthogonalGroup (Fin n) ℝ) :
    HasLaw (fun ω ↦ Matrix.UnitaryGroup.symmetricConj U (H ω)) (goeMeasure n) P ↔
      HasLaw H (goeMeasure n) P :=
  ⟨fun h ↦ by simpa [Matrix.UnitaryGroup.symmetricConj_inv] using h.symmetricConj_goeMeasure U⁻¹,
    fun h ↦ h.symmetricConj_goeMeasure U⟩

/-- Unitary conjugation `A ↦ U * A * Uᴴ` preserves `TauCeti.Probability.gueMeasure n`. -/
theorem measurePreserving_hermitianConj_gueMeasure {n : ℕ} (U : Matrix.unitaryGroup (Fin n) ℂ) :
    MeasurePreserving (Matrix.UnitaryGroup.hermitianConj U) (gueMeasure n) (gueMeasure n) := by
  rw [gueMeasure_eq_map_stdGaussian]
  exact (Matrix.UnitaryGroup.hermitianConj U).measurePreserving_map_smul_stdGaussian _

/-- Pushing `gueMeasure` forward along unitary conjugation leaves it unchanged. -/
@[simp] theorem map_hermitianConj_gueMeasure {n : ℕ} (U : Matrix.unitaryGroup (Fin n) ℂ) :
    (gueMeasure n).map (Matrix.UnitaryGroup.hermitianConj U) = gueMeasure n :=
  (measurePreserving_hermitianConj_gueMeasure U).map_eq

/-- Unitary conjugation preserves `HasLaw` for `TauCeti.Probability.gueMeasure`. -/
theorem _root_.ProbabilityTheory.HasLaw.hermitianConj_gueMeasure {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {n : ℕ} {H : Ω → selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)}
    (hH : HasLaw H (gueMeasure n) P) (U : Matrix.unitaryGroup (Fin n) ℂ) :
    HasLaw (fun ω ↦ Matrix.UnitaryGroup.hermitianConj U (H ω)) (gueMeasure n) P :=
  (measurePreserving_hermitianConj_gueMeasure U).fun_comp_hasLaw hH

/-- A random Hermitian matrix has law `gueMeasure` iff its unitary conjugate does. -/
@[simp] theorem hasLaw_hermitianConj_gueMeasure_iff {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {n : ℕ} {H : Ω → selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)}
    (U : Matrix.unitaryGroup (Fin n) ℂ) :
    HasLaw (fun ω ↦ Matrix.UnitaryGroup.hermitianConj U (H ω)) (gueMeasure n) P ↔
      HasLaw H (gueMeasure n) P :=
  ⟨fun h ↦ by simpa [Matrix.UnitaryGroup.hermitianConj_inv] using h.hermitianConj_gueMeasure U⁻¹,
    fun h ↦ h.hermitianConj_gueMeasure U⟩

/-- Ambient orthogonal conjugation preserves `TauCeti.Probability.gaussianEnsembleLaw 1 n`. -/
theorem map_mul_mul_conjTranspose_gaussianEnsembleLaw_one {n : ℕ}
    (U : Matrix.orthogonalGroup (Fin n) ℝ) :
    (gaussianEnsembleLaw 1 n).map (fun H ↦ (U : Matrix (Fin n) (Fin n) ℝ).map Complex.ofReal * H *
      ((U : Matrix (Fin n) (Fin n) ℝ).map Complex.ofReal)ᴴ) = gaussianEnsembleLaw 1 n := by
  have hconj : Measurable fun H : Matrix (Fin n) (Fin n) ℂ ↦
      (U : Matrix (Fin n) (Fin n) ℝ).map Complex.ofReal * H *
        ((U : Matrix (Fin n) (Fin n) ℝ).map Complex.ofReal)ᴴ :=
    ((continuous_const.mul continuous_id).mul continuous_const).measurable
  have hcomm (A : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)) :
      (U : Matrix (Fin n) (Fin n) ℝ).map Complex.ofReal * castSym n A *
        ((U : Matrix (Fin n) (Fin n) ℝ).map Complex.ofReal)ᴴ =
        castSym n (Matrix.UnitaryGroup.symmetricConj U A) :=
    Matrix.ext fun i j ↦ by simp [castSym, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [gaussianEnsembleLaw_one_eq_map_goeMeasure, Measure.map_map hconj (measurable_castSym n)]
  simp_rw [Function.comp_def, hcomm]
  rw [← Function.comp_def (castSym n) (Matrix.UnitaryGroup.symmetricConj U),
    ← Measure.map_map (measurable_castSym n)
      (Matrix.UnitaryGroup.symmetricConj U).continuous.measurable, map_symmetricConj_goeMeasure]

/-- Ambient unitary conjugation preserves `TauCeti.Probability.gaussianEnsembleLaw 2 n`. -/
theorem map_mul_mul_conjTranspose_gaussianEnsembleLaw_two {n : ℕ}
    (U : Matrix.unitaryGroup (Fin n) ℂ) :
    (gaussianEnsembleLaw 2 n).map
        (fun H ↦ (U : Matrix (Fin n) (Fin n) ℂ) * H * (U : Matrix (Fin n) (Fin n) ℂ)ᴴ) =
      gaussianEnsembleLaw 2 n := by
  have hconj : Measurable fun H : Matrix (Fin n) (Fin n) ℂ ↦
      (U : Matrix (Fin n) (Fin n) ℂ) * H * (U : Matrix (Fin n) (Fin n) ℂ)ᴴ :=
    ((continuous_const.mul continuous_id).mul continuous_const).measurable
  rw [gaussianEnsembleLaw_two_eq_map_gueMeasure, Measure.map_map hconj measurable_subtypeVal]
  simp_rw [Function.comp_def, ← Matrix.UnitaryGroup.coe_hermitianConj_apply]
  rw [← Function.comp_def Subtype.val (Matrix.UnitaryGroup.hermitianConj U),
    ← Measure.map_map measurable_subtypeVal
      (Matrix.UnitaryGroup.hermitianConj U).continuous.measurable, map_hermitianConj_gueMeasure]

private theorem identDistrib_mul_mul_of_map_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {n : ℕ} {μ : Measure (Matrix (Fin n) (Fin n) ℂ)} {X : Ω → Matrix (Fin n) (Fin n) ℂ}
    {c : ℝ} (A B : Matrix (Fin n) (Fin n) ℂ)
    (hmap : μ.map (fun H ↦ A * H * B) = μ)
    (hX : HasLaw X (μ.map (c • ·)) P) :
    IdentDistrib (fun ω ↦ A * X ω * B) X P P := by
  have hconj : Measurable fun H : Matrix (Fin n) (Fin n) ℂ ↦ A * H * B :=
    ((continuous_const.mul continuous_id).mul continuous_const).measurable
  exact ((((measurable_const_smul c).measurePreserving μ).of_semiconj
    ⟨hconj, hmap⟩ (fun H ↦ by simp) hconj).fun_comp_hasLaw hX).identDistrib hX

/-- **Orthogonal conjugation invariance of `gaussianEnsemble 1 n`.** With independent `N(0, v)`
upper-triangular coordinates, conjugating `gaussianEnsemble 1 n` by a real orthogonal matrix lifted
to `ℂ` preserves its distribution. -/
theorem identDistrib_conj_gaussianEnsemble_one {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {n : ℕ} {g : Fin n × Fin n → Ω → ℝ} {v : ℝ≥0}
    (hg : ∀ ij : upperTriangle n, HasLaw (g ij.val) (gaussianReal 0 v) P)
    (hindep : iIndepFun (fun (ij : upperTriangle n) ω ↦ g ij.val ω) P)
    (O : Matrix.orthogonalGroup (Fin n) ℝ) :
    IdentDistrib
      (fun ω ↦
        (O : Matrix (Fin n) (Fin n) ℝ).map Complex.ofReal *
          gaussianEnsemble 1 n (fun ij ↦ g ij ω) *
          ((O : Matrix (Fin n) (Fin n) ℝ).map Complex.ofReal)ᵀ)
      (fun ω ↦ gaussianEnsemble 1 n (fun ij ↦ g ij ω)) P P := by
  have hlaw : HasLaw (fun ω ↦ gaussianEnsemble 1 n (fun ij ↦ g ij ω))
      ((gaussianEnsembleLaw 1 n).map (Real.sqrt v • ·)) P := by
    have hsmul : castSym n ∘ (Real.sqrt v • ·) = (Real.sqrt v • ·) ∘ castSym n :=
      funext fun A ↦ Matrix.ext fun i j ↦ by simp [castSym, Complex.real_smul]
    have h := (hasLaw_map (measurable_castSym n).aemeasurable).fun_comp
      (hasLaw_goeMatrix_of_upperTriangle_smul g hindep hg)
    simp_rw [map_ofReal_coe_goeMatrix] at h
    rwa [Measure.map_map (measurable_castSym n) (measurable_const_smul _), hsmul,
      ← Measure.map_map (measurable_const_smul _) (measurable_castSym n),
      ← gaussianEnsembleLaw_one_eq_map_goeMeasure] at h
  have hconjT : ((O : Matrix (Fin n) (Fin n) ℝ).map Complex.ofReal)ᴴ =
      ((O : Matrix (Fin n) (Fin n) ℝ).map Complex.ofReal)ᵀ := by
    ext i j; simp
  exact identDistrib_mul_mul_of_map_eq _ _
    (by simpa [hconjT] using map_mul_mul_conjTranspose_gaussianEnsembleLaw_one O) hlaw

/-- **Unitary conjugation invariance of `gaussianEnsemble β n` (`β ≠ 1`, in particular GUE).**
With independent `N(0, v)` coordinates, conjugating `gaussianEnsemble β n` by a unitary matrix
`U ∈ U(n)` preserves its distribution. -/
theorem identDistrib_conj_gaussianEnsemble_of_ne_one {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {β n : ℕ} (hβ : β ≠ 1) {g : Fin n × Fin n → Ω → ℝ} {v : ℝ≥0}
    (hg : ∀ ij, HasLaw (g ij) (gaussianReal 0 v) P) (hindep : iIndepFun g P)
    (U : Matrix.unitaryGroup (Fin n) ℂ) :
    IdentDistrib
      (fun ω ↦
        (U : Matrix (Fin n) (Fin n) ℂ) *
          gaussianEnsemble β n (fun ij ↦ g ij ω) *
          (U : Matrix (Fin n) (Fin n) ℂ)ᴴ)
      (fun ω ↦ gaussianEnsemble β n (fun ij ↦ g ij ω)) P P := by
  have hlaw : HasLaw (fun ω ↦ gaussianEnsemble β n (fun ij ↦ g ij ω))
      ((gaussianEnsembleLaw 2 n).map (Real.sqrt v • ·)) P := by
    convert hasLaw_gaussianEnsemble β hg hindep using 2
    rw [gaussianEnsembleLaw_def, Measure.map_map (by fun_prop) (by fun_prop)]
    congr 1; funext x; simp [gaussianEnsemble_eq_gaussianEnsemble_two_of_ne_one hβ]
  exact identDistrib_mul_mul_of_map_eq _ _
    (map_mul_mul_conjTranspose_gaussianEnsembleLaw_two U) hlaw

/-- Under `goeMeasure n`, the upper-triangular coordinates are independent Gaussians:
`N(0, 2 / n)` on the diagonal and `N(0, 1 / n)` above it. -/
theorem map_symmetricCoordinates_goeMeasure (n : ℕ) :
    (goeMeasure n).map (symmetricCoordinates n) =
      Measure.pi fun ij : upperTriangle n ↦
        if ij.val.1 = ij.val.2 then gaussianReal 0 (2 / n) else gaussianReal 0 (1 / n) := by
  let scale : upperTriangle n → ℝ → ℝ := fun ij t ↦
    (Real.sqrt n)⁻¹ * ((if ij.val.1 = ij.val.2 then Real.sqrt 2 else 1) * t)
  have hfactor (ij : upperTriangle n) : (gaussianReal 0 1).map (scale ij) =
      if ij.val.1 = ij.val.2 then gaussianReal 0 (2 / n) else gaussianReal 0 (1 / n) := by
    simp only [scale, ← mul_assoc]
    split_ifs with hd <;> refine gaussianReal_zero_one_map_const_mul _ ?_
    · simp [mul_pow, div_eq_inv_mul]
    · simp [one_div]
  have : ∀ ij : upperTriangle n, SigmaFinite ((gaussianReal 0 1).map (scale ij)) :=
    fun ij ↦ by rw [hfactor ij]; infer_instance
  rw [goeMeasure_eq_map_pi_upperTriangle,
    Measure.map_map (symmetricCoordinates n).continuous.measurable (by fun_prop)]
  simp_rw [Function.comp_def, ContinuousLinearEquiv.apply_symm_apply]
  rw [Measure.pi_map_pi (f := scale) fun ij ↦ by fun_prop]
  exact congrArg Measure.pi (funext hfactor)

/-- Under `gueMeasure n`, `hermitianCoordinates n` has independent Gaussian coordinates:
`N(0, 1 / n)` on the diagonal and `N(0, 1 / (2 * n))` off the diagonal. -/
theorem map_hermitianCoordinates_gueMeasure (n : ℕ) :
    (gueMeasure n).map (hermitianCoordinates n) =
      Measure.pi fun ij : Fin n × Fin n ↦
        if ij.1 = ij.2 then gaussianReal 0 (1 / n) else gaussianReal 0 (1 / (2 * n)) := by
  let scale : Fin n × Fin n → ℝ → ℝ := fun ij t ↦
    (Real.sqrt n)⁻¹ * ((if ij.1 = ij.2 then 1 else (Real.sqrt 2)⁻¹) * t)
  have hfactor (ij : Fin n × Fin n) : (gaussianReal 0 1).map (scale ij) =
      if ij.1 = ij.2 then gaussianReal 0 (1 / n) else gaussianReal 0 (1 / (2 * n)) := by
    simp only [scale, ← mul_assoc]
    split_ifs with hd <;> refine gaussianReal_zero_one_map_const_mul _ ?_
    · simp [one_div]
    · simp [mul_pow, one_div]
  have : ∀ ij : Fin n × Fin n, SigmaFinite ((gaussianReal 0 1).map (scale ij)) :=
    fun ij ↦ by rw [hfactor ij]; infer_instance
  have hcomp : ⇑(hermitianCoordinates n) ∘ ⇑(gueMatrix n) = fun g ij ↦ scale ij (g ij) :=
    funext fun g ↦ funext (hermitianCoordinates_gueMatrix n g)
  rw [gueMeasure_def, Measure.map_map (hermitianCoordinates n).continuous.measurable
    (measurable_gueMatrix n), hcomp, Measure.pi_map_pi fun ij ↦ by fun_prop]
  exact congrArg Measure.pi (funext hfactor)

/-- **Characterization of the GOE by independent Gaussian entries.** A random symmetric matrix `H`
has law `goeMeasure n` iff its on-or-above-diagonal entries are mutually independent with
`H i i ~ N(0, 2 / n)` and `H i j ~ N(0, 1 / n)` for `i < j`. -/
theorem hasLaw_goeMeasure_iff {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}
    {H : Ω → selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)} :
    HasLaw H (goeMeasure n) P ↔
      iIndepFun (fun (ij : upperTriangle n) ω ↦
          (H ω : Matrix (Fin n) (Fin n) ℝ) ij.val.1 ij.val.2) P ∧
        (∀ i : Fin n, HasLaw (fun ω ↦ (H ω : Matrix (Fin n) (Fin n) ℝ) i i)
          (gaussianReal 0 (2 / n)) P) ∧
        (∀ ⦃i j : Fin n⦄, i < j →
          HasLaw (fun ω ↦ (H ω : Matrix (Fin n) (Fin n) ℝ) i j)
            (gaussianReal 0 (1 / n)) P) := by
  let μ : upperTriangle n → Measure ℝ := fun ij ↦
    if ij.val.1 = ij.val.2 then gaussianReal 0 (2 / n) else gaussianReal 0 (1 / n)
  have hm :
      MeasurePreserving (symmetricCoordinatesMeasurableEquiv n) (goeMeasure n) (Measure.pi μ) :=
    ⟨(symmetricCoordinatesMeasurableEquiv n).measurable,
      symmetricCoordinatesMeasurableEquiv_coe n ▸ map_symmetricCoordinates_goeMeasure n⟩
  have hsc : (fun ω (ij : upperTriangle n) ↦ (H ω : Matrix (Fin n) (Fin n) ℝ) ij.val.1 ij.val.2) =
      fun ω ↦ symmetricCoordinates n (H ω) :=
    funext fun ω ↦ funext fun ij ↦ (symmetricCoordinates_apply n (H ω) ij).symm
  constructor
  · intro hH; let _ := hH.isProbabilityMeasure
    have hcoord : HasLaw (fun ω (ij : upperTriangle n) ↦
        (H ω : Matrix (Fin n) (Fin n) ℝ) ij.val.1 ij.val.2) (Measure.pi μ) P :=
      hsc ▸ by simpa using hm.fun_comp_hasLaw hH
    have heach (ij : upperTriangle n) := (measurePreserving_eval μ ij).fun_comp_hasLaw hcoord
    exact ⟨(iIndepFun_iff_hasLaw_pi_pi heach).2 hcoord,
      fun i ↦ by simpa [μ] using heach ⟨(i, i), le_rfl⟩,
      fun i j hij ↦ by simpa [μ, hij.ne] using heach ⟨(i, j), hij.le⟩⟩
  · rintro ⟨hindep, hdiag, hoff⟩
    have heach (ij : upperTriangle n) :
        HasLaw (fun ω ↦ (H ω : Matrix (Fin n) (Fin n) ℝ) ij.val.1 ij.val.2) (μ ij) P := by
      rcases ij.property.eq_or_lt with h | hlt
      · obtain ⟨⟨i, j⟩, _⟩ := ij; cases h; simpa [μ] using hdiag i
      · simpa [μ, hlt.ne] using hoff hlt
    have hcoord : HasLaw (fun ω ↦ symmetricCoordinates n (H ω)) (Measure.pi μ) P :=
      hsc ▸ hindep.hasLaw_pi heach
    simpa using (hm.symm (symmetricCoordinatesMeasurableEquiv n)).fun_comp_hasLaw hcoord

/-- **Characterization of the GUE by independent Gaussian entries.** A random Hermitian matrix `H`
has law `gueMeasure n` iff `hermitianCoordinates n (H ω)` has mutually independent entries with
`(H i i).re ~ N(0, 1 / n)` and `(H i j).re, (H i j).im ~ N(0, 1 / (2 * n))` for `i < j`. -/
theorem hasLaw_gueMeasure_iff {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}
    {H : Ω → selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)} :
    HasLaw H (gueMeasure n) P ↔
      iIndepFun (fun (ij : Fin n × Fin n) ω ↦ hermitianCoordinates n (H ω) ij) P ∧
        (∀ i : Fin n, HasLaw (fun ω ↦ ((H ω : Matrix (Fin n) (Fin n) ℂ) i i).re)
          (gaussianReal 0 (1 / n)) P) ∧
        (∀ ⦃i j : Fin n⦄, i < j →
          HasLaw (fun ω ↦ ((H ω : Matrix (Fin n) (Fin n) ℂ) i j).re)
            (gaussianReal 0 (1 / (2 * n))) P ∧
          HasLaw (fun ω ↦ ((H ω : Matrix (Fin n) (Fin n) ℂ) i j).im)
            (gaussianReal 0 (1 / (2 * n))) P) := by
  let μ : Fin n × Fin n → Measure ℝ := fun ij ↦
    if ij.1 = ij.2 then gaussianReal 0 (1 / n) else gaussianReal 0 (1 / (2 * n))
  have hm :
      MeasurePreserving (hermitianCoordinatesMeasurableEquiv n) (gueMeasure n) (Measure.pi μ) :=
    ⟨(hermitianCoordinatesMeasurableEquiv n).measurable,
      hermitianCoordinatesMeasurableEquiv_coe n ▸ map_hermitianCoordinates_gueMeasure n⟩
  constructor
  · intro hH; let _ := hH.isProbabilityMeasure
    have hcoord : HasLaw (fun ω ↦ hermitianCoordinates n (H ω)) (Measure.pi μ) P := by
      simpa using hm.fun_comp_hasLaw hH
    have heach (ij : Fin n × Fin n) := (measurePreserving_eval μ ij).fun_comp_hasLaw hcoord
    exact ⟨(iIndepFun_iff_hasLaw_pi_pi heach).2 hcoord,
      fun i ↦ by simpa [μ] using heach (i, i),
      fun i j hij ↦ ⟨by simpa [μ, hij.le, hij.ne] using heach (i, j),
        by simpa [μ, hij, hij.ne'] using heach (j, i)⟩⟩
  · rintro ⟨hindep, hdiag, hoff⟩
    have heach : ∀ ij : Fin n × Fin n,
        HasLaw (fun ω ↦ hermitianCoordinates n (H ω) ij) (μ ij) P
      | (i, j) => by
        rcases lt_trichotomy i j with h | rfl | h
        · simpa [μ, h.le, h.ne] using (hoff h).1
        · simpa [μ] using hdiag i
        · simpa [μ, h, h.ne'] using (hoff h).2
    simpa using (hm.symm (hermitianCoordinatesMeasurableEquiv n)).fun_comp_hasLaw
      (hindep.hasLaw_pi heach)

end TauCeti.Probability
