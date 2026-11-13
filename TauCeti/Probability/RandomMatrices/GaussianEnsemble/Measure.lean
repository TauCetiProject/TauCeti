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

/-!
# Laws and conjugation invariance of the GOE and GUE

`TauCeti.Probability.gaussianEnsemble` builds an `n × n` matrix over `ℂ` from a real array
`g : Fin n × Fin n → ℝ`. For `β = 1` its entries have zero imaginary part and form a real symmetric
matrix `TauCeti.Probability.goeMatrix n g` in `selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)`;
for `β = 2` (and any `β ≠ 1`) they form a complex Hermitian matrix
`TauCeti.Probability.gueMatrix n g` in `selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)`.

Pushing the standard Gaussian product measure on `Fin n × Fin n → ℝ` forward along these maps gives
the Gaussian orthogonal ensemble law `TauCeti.Probability.goeMeasure n`, the Gaussian unitary
ensemble law `TauCeti.Probability.gueMeasure n`, and the ambient complex-matrix law
`TauCeti.Probability.gaussianEnsembleLaw β n`.

Viewing the real symmetric and complex Hermitian subspaces as finite-dimensional real inner product
spaces under the Frobenius trace pairing (`⟪A, B⟫ = tr(B * A)` and `⟪A, B⟫ = Re tr(B * A)`), both
ensemble laws are scalar rescalings of `ProbabilityTheory.stdGaussian`: `goeMeasure n` by
`√2 / √n`, and `gueMeasure n` by `(√n)⁻¹`. Orthogonal invariance of `goeMeasure n` and unitary
invariance of `gueMeasure n` follow at every dimension `n` from the isometric invariance of
`stdGaussian`.

## Main definitions

* `TauCeti.Probability.goeMatrix`, `TauCeti.Probability.gueMatrix` — the GOE and GUE matrix maps
  valued in the real symmetric and complex Hermitian self-adjoint subspaces.
* `TauCeti.Probability.goeMeasure`, `TauCeti.Probability.gueMeasure`,
  `TauCeti.Probability.gaussianEnsembleLaw` — the GOE, GUE, and ambient `ℂ`-matrix laws.

## Main results

* `TauCeti.Probability.im_gaussianEnsemble_one`,
  `TauCeti.Probability.im_gaussianEnsemble_two_zero_one` — the `β = 1` ensemble has real entries,
  and for `β = 2, n = 2` the upper off-diagonal imaginary part is `g (1, 0) / 2`.
* `TauCeti.Probability.goeMeasure_eq_map_stdGaussian`,
  `TauCeti.Probability.gueMeasure_eq_map_stdGaussian` — `goeMeasure n` and `gueMeasure n` as scalar
  multiples of `ProbabilityTheory.stdGaussian` on the Frobenius inner product spaces.
* `TauCeti.Probability.map_symmetricFinOneEquiv_goeMeasure`,
  `TauCeti.Probability.map_hermitianFinOneEquiv_gueMeasure` — in dimension one, `goeMeasure 1` is
  `N(0, 2)` and `gueMeasure 1` is `N(0, 1)`.
* `TauCeti.Probability.measurePreserving_symmetricConj_goeMeasure`,
  `TauCeti.Probability.measurePreserving_hermitianConj_gueMeasure` — orthogonal conjugation
  preserves `goeMeasure n` and unitary conjugation preserves `gueMeasure n`.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), §2.5.1.
-/

public section

noncomputable section

open MeasureTheory Matrix Module ProbabilityTheory
open scoped ComplexConjugate ENNReal NNReal RealInnerProductSpace

namespace TauCeti

namespace Probability

/-! ### Entry properties, continuity, and subspace-valued ensemble maps -/

/-- Every entry of the `β = 1` Gaussian ensemble has zero imaginary part. -/
@[simp]
theorem im_gaussianEnsemble_one {n : ℕ} (g : Fin n × Fin n → ℝ) (i j : Fin n) :
    (gaussianEnsemble 1 n g i j).im = 0 := by
  rcases lt_trichotomy i j with h | rfl | h
  · rw [gaussianEnsemble_apply_of_lt_of_eq_one g rfl h, ← Complex.ofReal_inv,
      ← Complex.ofReal_mul, Complex.ofReal_im]
  · rw [gaussianEnsemble_apply_self_of_eq_one g rfl i, ← Complex.ofReal_inv,
      ← Complex.ofReal_mul, Complex.ofReal_im]
  · rw [gaussianEnsemble_apply_of_gt_of_eq_one g rfl h, ← Complex.ofReal_inv,
      ← Complex.ofReal_mul, Complex.ofReal_im]

/-- All `β ≠ 1` branches of `TauCeti.Probability.gaussianEnsemble` coincide with the `β = 2`
ensemble. -/
theorem gaussianEnsemble_eq_two_of_ne_one {β n : ℕ} (hβ : β ≠ 1) (g : Fin n × Fin n → ℝ) :
    gaussianEnsemble β n g = gaussianEnsemble 2 n g := by
  ext i j
  rw [gaussianEnsemble_apply, gaussianEnsemble_apply, ite_eq_right hβ,
    ite_eq_right (by decide : (2 : ℕ) ≠ 1)]

/-- For `β = 2` and `n = 2`, the imaginary part of the `(0, 1)` entry is `g (1, 0) / 2`. -/
theorem im_gaussianEnsemble_two_zero_one (g : Fin 2 × Fin 2 → ℝ) :
    (gaussianEnsemble 2 2 g 0 1).im = g (1, 0) / 2 := by
  have h01 : (0 : Fin 2) < 1 := by decide
  rw [gaussianEnsemble_apply_of_lt_of_ne_one g (by decide) h01, Nat.cast_ofNat,
    ← Complex.ofReal_inv]
  have hexpr : (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) *
      (((g (0, 1) : ℂ) + Complex.I * g (1, 0)) / (Real.sqrt 2 : ℝ)) =
      ((g (0, 1) / (Real.sqrt 2 * Real.sqrt 2) : ℝ) : ℂ) +
        Complex.I * ((g (1, 0) / (Real.sqrt 2 * Real.sqrt 2) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hexpr, Real.mul_self_sqrt (by norm_num)]
  simp

/-- `TauCeti.Probability.gaussianEnsemble` depends continuously on the input array. -/
theorem continuous_gaussianEnsemble (β n : ℕ) : Continuous (gaussianEnsemble β n) := by
  refine continuous_matrix fun i j ↦ ?_
  have hfun : (fun g : Fin n × Fin n → ℝ ↦ gaussianEnsemble β n g i j) = fun g ↦
      ((Real.sqrt n)⁻¹ : ℂ) *
        if β = 1 then
          if i = j then ((Real.sqrt 2 * g (i, i) : ℝ) : ℂ)
          else if i < j then (g (i, j) : ℂ) else (g (j, i) : ℂ)
        else
          if i = j then (g (i, i) : ℂ)
          else if i < j then ((g (i, j) : ℂ) + Complex.I * g (j, i)) / (Real.sqrt 2 : ℝ)
          else ((g (j, i) : ℂ) - Complex.I * g (i, j)) / (Real.sqrt 2 : ℝ) :=
    funext fun g ↦ gaussianEnsemble_apply g i j
  rw [hfun]
  rcases lt_trichotomy i j with h | rfl | h
  · by_cases hβ : β = 1 <;> simp only [hβ, h, h.ne, ↓reduceIte] <;> fun_prop
  · by_cases hβ : β = 1 <;> simp only [hβ, ↓reduceIte] <;> fun_prop
  · by_cases hβ : β = 1 <;> simp only [hβ, h.ne', h.not_gt, ↓reduceIte] <;> fun_prop

/-- `TauCeti.Probability.gaussianEnsemble` is measurable in the input array. -/
@[fun_prop]
theorem measurable_gaussianEnsemble (β n : ℕ) : Measurable (gaussianEnsemble β n) :=
  (continuous_gaussianEnsemble β n).measurable

/-- The real symmetric matrix of the Gaussian orthogonal ensemble (`β = 1`), bundled into
`selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)`: diagonal entries `(√2 * g (i, i)) / √n` and
off-diagonal entries `g (min i j, max i j) / √n`. -/
def goeMatrix (n : ℕ) (g : Fin n × Fin n → ℝ) :
    selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ) :=
  (symmetricCoordinates n).symm fun ij ↦
    (Real.sqrt n)⁻¹ * ((if ij.1.1 = ij.1.2 then Real.sqrt 2 else 1) * g ij.1)

/-- Defining formula for `TauCeti.Probability.goeMatrix`. -/
theorem goeMatrix_def (n : ℕ) (g : Fin n × Fin n → ℝ) :
    goeMatrix n g =
      (symmetricCoordinates n).symm fun ij ↦
        (Real.sqrt n)⁻¹ * ((if ij.1.1 = ij.1.2 then Real.sqrt 2 else 1) * g ij.1) :=
  (rfl)

/-- Upper-triangular coordinates of `TauCeti.Probability.goeMatrix`. -/
theorem symmetricCoordinates_goeMatrix (n : ℕ) (g : Fin n × Fin n → ℝ) (ij : upperTriangle n) :
    symmetricCoordinates n (goeMatrix n g) ij =
      (Real.sqrt n)⁻¹ * ((if ij.1.1 = ij.1.2 then Real.sqrt 2 else 1) * g ij.1) :=
  (symmetricCoordinates n).apply_symm_apply _ ▸ rfl

/-- Diagonal entries of `TauCeti.Probability.goeMatrix`. -/
@[simp]
theorem coe_goeMatrix_apply_self {n : ℕ} (g : Fin n × Fin n → ℝ) (i : Fin n) :
    (goeMatrix n g : Matrix (Fin n) (Fin n) ℝ) i i =
      (Real.sqrt n)⁻¹ * (Real.sqrt 2 * g (i, i)) := by
  simp [goeMatrix]

/-- Strict upper-triangular entries (`i < j`) of `TauCeti.Probability.goeMatrix`. -/
@[simp]
theorem coe_goeMatrix_apply_of_lt {n : ℕ} (g : Fin n × Fin n → ℝ) {i j : Fin n} (h : i < j) :
    (goeMatrix n g : Matrix (Fin n) (Fin n) ℝ) i j = (Real.sqrt n)⁻¹ * g (i, j) := by
  rw [goeMatrix, coe_symmetricCoordinates_symm_apply_of_le n _ h.le]
  simp [h.ne]

/-- Strict lower-triangular entries (`j < i`) of `TauCeti.Probability.goeMatrix`. -/
@[simp]
theorem coe_goeMatrix_apply_of_gt {n : ℕ} (g : Fin n × Fin n → ℝ) {i j : Fin n} (h : j < i) :
    (goeMatrix n g : Matrix (Fin n) (Fin n) ℝ) i j = (Real.sqrt n)⁻¹ * g (j, i) := by
  rw [goeMatrix, coe_symmetricCoordinates_symm_apply_of_ge n _ h.le]
  simp [h.ne]

/-- Casting `TauCeti.Probability.goeMatrix` from `ℝ` to `ℂ` recovers `gaussianEnsemble 1 n g`. -/
theorem map_ofReal_coe_goeMatrix (n : ℕ) (g : Fin n × Fin n → ℝ) :
    (goeMatrix n g : Matrix (Fin n) (Fin n) ℝ).map Complex.ofReal = gaussianEnsemble 1 n g := by
  ext i j
  rcases lt_trichotomy i j with h | rfl | h
  · simp [h]
  · simp
  · simp [h]

/-- Each entry of `TauCeti.Probability.goeMatrix` is the real part of the corresponding entry of
`gaussianEnsemble 1 n g`. -/
theorem coe_goeMatrix_apply_eq_re (n : ℕ) (g : Fin n × Fin n → ℝ) (i j : Fin n) :
    (goeMatrix n g : Matrix (Fin n) (Fin n) ℝ) i j = (gaussianEnsemble 1 n g i j).re := by
  rw [← map_ofReal_coe_goeMatrix]
  simp

/-- `TauCeti.Probability.goeMatrix` is continuous in the input array. -/
theorem continuous_goeMatrix (n : ℕ) : Continuous (goeMatrix n) := by
  unfold goeMatrix
  fun_prop

/-- `TauCeti.Probability.goeMatrix` is measurable in the input array. -/
@[fun_prop]
theorem measurable_goeMatrix (n : ℕ) : Measurable (goeMatrix n) :=
  (continuous_goeMatrix n).measurable

/-- The complex Hermitian matrix of the Gaussian unitary ensemble (`β = 2`), bundled into
`selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)`. -/
def gueMatrix (n : ℕ) (g : Fin n × Fin n → ℝ) :
    selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ) :=
  ⟨gaussianEnsemble 2 n g,
    Matrix.isHermitian_iff_isSelfAdjoint.mp (isHermitian_gaussianEnsemble 2 n g)⟩

/-- Defining formula for `TauCeti.Probability.gueMatrix`. -/
theorem gueMatrix_def (n : ℕ) (g : Fin n × Fin n → ℝ) :
    gueMatrix n g =
      ⟨gaussianEnsemble 2 n g,
        Matrix.isHermitian_iff_isSelfAdjoint.mp (isHermitian_gaussianEnsemble 2 n g)⟩ :=
  (rfl)

/-- Underlying complex matrix of `TauCeti.Probability.gueMatrix`. -/
@[simp]
theorem coe_gueMatrix (n : ℕ) (g : Fin n × Fin n → ℝ) :
    (gueMatrix n g : Matrix (Fin n) (Fin n) ℂ) = gaussianEnsemble 2 n g :=
  (rfl)

/-- Real coordinates of `TauCeti.Probability.gueMatrix` in `TauCeti.hermitianCoordinates`. -/
theorem hermitianCoordinates_gueMatrix (n : ℕ) (g : Fin n × Fin n → ℝ) (ij : Fin n × Fin n) :
    hermitianCoordinates n (gueMatrix n g) ij =
      (Real.sqrt n)⁻¹ * ((if ij.1 = ij.2 then 1 else (Real.sqrt 2)⁻¹) * g ij) := by
  obtain ⟨i, j⟩ := ij
  rcases lt_trichotomy i j with h | rfl | h
  · rw [hermitianCoordinates_apply_of_le n _ h.le, coe_gueMatrix,
      gaussianEnsemble_apply_of_lt_of_ne_one g (by decide) h, ← Complex.ofReal_inv]
    have hexpr : (((Real.sqrt n)⁻¹ : ℝ) : ℂ) *
        (((g (i, j) : ℂ) + Complex.I * g (j, i)) / (Real.sqrt 2 : ℝ)) =
        (((Real.sqrt n)⁻¹ * ((Real.sqrt 2)⁻¹ * g (i, j)) : ℝ) : ℂ) +
          Complex.I * (((Real.sqrt n)⁻¹ * ((Real.sqrt 2)⁻¹ * g (j, i)) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hexpr]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero, h.ne, ↓reduceIte]
  · rw [hermitianCoordinates_apply_of_le n _ le_rfl, coe_gueMatrix,
      gaussianEnsemble_apply_self_of_ne_one g (by decide) i, ← Complex.ofReal_inv,
      ← Complex.ofReal_mul, Complex.ofReal_re]
    simp
  · rw [hermitianCoordinates_apply_of_gt n _ h, coe_gueMatrix,
      gaussianEnsemble_apply_of_lt_of_ne_one g (by decide) h, ← Complex.ofReal_inv]
    have hexpr : (((Real.sqrt n)⁻¹ : ℝ) : ℂ) *
        (((g (j, i) : ℂ) + Complex.I * g (i, j)) / (Real.sqrt 2 : ℝ)) =
        (((Real.sqrt n)⁻¹ * ((Real.sqrt 2)⁻¹ * g (j, i)) : ℝ) : ℂ) +
          Complex.I * (((Real.sqrt n)⁻¹ * ((Real.sqrt 2)⁻¹ * g (i, j)) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hexpr]
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, zero_mul, one_mul, zero_add, h.ne', ↓reduceIte]

/-- `TauCeti.Probability.gueMatrix` is continuous in the input array. -/
theorem continuous_gueMatrix (n : ℕ) : Continuous (gueMatrix n) :=
  continuous_induced_rng.2 (continuous_gaussianEnsemble 2 n)

/-- `TauCeti.Probability.gueMatrix` is measurable in the input array. -/
@[fun_prop]
theorem measurable_gueMatrix (n : ℕ) : Measurable (gueMatrix n) :=
  (continuous_gueMatrix n).measurable

/-- `TauCeti.Probability.goeMatrix` expands in the Frobenius orthonormal basis
`TauCeti.symmetricOrthonormalBasis` with global scale `√2 / √n`. -/
theorem goeMatrix_eq_smul_sum_orthonormalBasis (n : ℕ) (g : Fin n × Fin n → ℝ) :
    goeMatrix n g =
      (Real.sqrt 2 / Real.sqrt n) •
        ∑ ij : upperTriangle n, g ij.1 • symmetricOrthonormalBasis n ij := by
  refine (symmetricCoordinates n).injective ?_
  ext kl
  rw [symmetricCoordinates_goeMatrix, map_smul, map_sum]
  simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, symmetricOrthonormalBasis_apply,
    map_smul, symmetricBasis_apply, ContinuousLinearEquiv.apply_symm_apply, Pi.single_apply]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  by_cases hd : kl.1.1 = kl.1.2
  · simp only [hd, ↓reduceIte]
    ring
  · simp only [hd, ↓reduceIte, one_mul]
    calc (Real.sqrt n)⁻¹ * g kl.1
        = (Real.sqrt 2 * (Real.sqrt 2)⁻¹) * ((Real.sqrt n)⁻¹ * g kl.1) := by
          rw [mul_inv_cancel₀ (by positivity), one_mul]
      _ = Real.sqrt 2 / Real.sqrt n * (g kl.1 * (Real.sqrt 2)⁻¹) := by
          rw [div_eq_mul_inv]
          ring

/-- `TauCeti.Probability.gueMatrix` expands in the Frobenius orthonormal basis
`TauCeti.hermitianOrthonormalBasis` with global scale `(√n)⁻¹`. -/
theorem gueMatrix_eq_smul_sum_orthonormalBasis (n : ℕ) (g : Fin n × Fin n → ℝ) :
    gueMatrix n g =
      (Real.sqrt n)⁻¹ • ∑ ij : Fin n × Fin n, g ij • hermitianOrthonormalBasis n ij := by
  refine (hermitianCoordinates n).injective ?_
  ext kl
  rw [hermitianCoordinates_gueMatrix, map_smul, map_sum]
  simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, hermitianOrthonormalBasis_apply,
    map_smul, hermitianBasis_apply, ContinuousLinearEquiv.apply_symm_apply, Pi.single_apply]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  by_cases hd : kl.1 = kl.2 <;> simp only [hd, ↓reduceIte] <;> ring

/-! ### The GOE and GUE probability measures -/

/-- The **Gaussian orthogonal ensemble** (`β = 1`) law on `n × n` real symmetric matrices: the
pushforward of the standard Gaussian product measure on `Fin n × Fin n → ℝ` along
`TauCeti.Probability.goeMatrix`. -/
def goeMeasure (n : ℕ) : Measure (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)) :=
  (Measure.pi fun _ : Fin n × Fin n ↦ gaussianReal 0 1).map (goeMatrix n)

/-- Defining formula for `TauCeti.Probability.goeMeasure`. -/
theorem goeMeasure_def (n : ℕ) :
    goeMeasure n = (Measure.pi fun _ : Fin n × Fin n ↦ gaussianReal 0 1).map (goeMatrix n) :=
  (rfl)

/-- The **Gaussian unitary ensemble** (`β = 2`) law on `n × n` complex Hermitian matrices: the
pushforward of the standard Gaussian product measure on `Fin n × Fin n → ℝ` along
`TauCeti.Probability.gueMatrix`. -/
def gueMeasure (n : ℕ) : Measure (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) :=
  (Measure.pi fun _ : Fin n × Fin n ↦ gaussianReal 0 1).map (gueMatrix n)

/-- Defining formula for `TauCeti.Probability.gueMeasure`. -/
theorem gueMeasure_def (n : ℕ) :
    gueMeasure n = (Measure.pi fun _ : Fin n × Fin n ↦ gaussianReal 0 1).map (gueMatrix n) :=
  (rfl)

/-- The ambient complex-matrix law of `TauCeti.Probability.gaussianEnsemble β n` under independent
standard Gaussian inputs. -/
def gaussianEnsembleLaw (β n : ℕ) : Measure (Matrix (Fin n) (Fin n) ℂ) :=
  (Measure.pi fun _ : Fin n × Fin n ↦ gaussianReal 0 1).map (gaussianEnsemble β n)

/-- Defining formula for `TauCeti.Probability.gaussianEnsembleLaw`. -/
theorem gaussianEnsembleLaw_def (β n : ℕ) :
    gaussianEnsembleLaw β n =
      (Measure.pi fun _ : Fin n × Fin n ↦ gaussianReal 0 1).map (gaussianEnsemble β n) :=
  (rfl)

instance isProbabilityMeasure_goeMeasure (n : ℕ) : IsProbabilityMeasure (goeMeasure n) :=
  inferInstanceAs
    (IsProbabilityMeasure ((Measure.pi fun _ : Fin n × Fin n ↦ gaussianReal 0 1).map (goeMatrix n)))

instance isProbabilityMeasure_gueMeasure (n : ℕ) : IsProbabilityMeasure (gueMeasure n) :=
  inferInstanceAs
    (IsProbabilityMeasure ((Measure.pi fun _ : Fin n × Fin n ↦ gaussianReal 0 1).map (gueMatrix n)))

instance isProbabilityMeasure_gaussianEnsembleLaw (β n : ℕ) :
    IsProbabilityMeasure (gaussianEnsembleLaw β n) :=
  inferInstanceAs (IsProbabilityMeasure
    ((Measure.pi fun _ : Fin n × Fin n ↦ gaussianReal 0 1).map (gaussianEnsemble β n)))

/-- The ambient `β = 1` law is the cast pushforward of `TauCeti.Probability.goeMeasure`. -/
theorem gaussianEnsembleLaw_one_eq_map_goeMeasure (n : ℕ) :
    gaussianEnsembleLaw 1 n =
      (goeMeasure n).map fun A : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ) ↦
        (A : Matrix (Fin n) (Fin n) ℝ).map Complex.ofReal := by
  have hm : Measurable fun A : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ) ↦
      (A : Matrix (Fin n) (Fin n) ℝ).map Complex.ofReal :=
    (continuous_matrix fun i j ↦ Complex.continuous_ofReal.comp
      (selfAdjoint.continuous_coe_apply i j)).measurable
  rw [gaussianEnsembleLaw_def, goeMeasure_def, Measure.map_map hm (measurable_goeMatrix n)]
  exact congrArg (fun f ↦ (Measure.pi fun _ : Fin n × Fin n ↦ gaussianReal 0 1).map f)
    (funext fun g ↦ (map_ofReal_coe_goeMatrix n g).symm)

/-- For `β ≠ 1`, `TauCeti.Probability.gaussianEnsembleLaw β n` is the subtype-coercion pushforward
of `TauCeti.Probability.gueMeasure n`. -/
theorem gaussianEnsembleLaw_eq_map_gueMeasure {β : ℕ} (hβ : β ≠ 1) (n : ℕ) :
    gaussianEnsembleLaw β n = (gueMeasure n).map Subtype.val := by
  rw [gaussianEnsembleLaw_def, gueMeasure_def,
    Measure.map_map measurable_subtype_coe (measurable_gueMatrix n)]
  exact congrArg (fun f ↦ (Measure.pi fun _ : Fin n × Fin n ↦ gaussianReal 0 1).map f)
    (funext (gaussianEnsemble_eq_two_of_ne_one hβ))

/-- The ambient `β = 2` law is the subtype-coercion pushforward of
`TauCeti.Probability.gueMeasure`. -/
theorem gaussianEnsembleLaw_two_eq_map_gueMeasure (n : ℕ) :
    gaussianEnsembleLaw 2 n = (gueMeasure n).map Subtype.val :=
  gaussianEnsembleLaw_eq_map_gueMeasure (by decide) n

/-- Building `TauCeti.Probability.goeMatrix` from a family of real random variables whose
upper-triangular entries are independent standard Gaussians produces `goeMeasure n`. -/
theorem hasLaw_goeMatrix_of_upperTriangle {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {n : ℕ} (g : Fin n × Fin n → Ω → ℝ)
    (hindep : iIndepFun (fun (ij : upperTriangle n) ω ↦ g ij.1 ω) P)
    (hlaw : ∀ ij : upperTriangle n, HasLaw (g ij.1) (gaussianReal 0 1) P) :
    HasLaw (fun ω ↦ goeMatrix n (fun p ↦ g p ω)) (goeMeasure n) P := by
  have hpi : HasLaw (fun ω (ij : upperTriangle n) ↦ g ij.1 ω)
      (Measure.pi fun _ : upperTriangle n ↦ gaussianReal 0 1) P :=
    hindep.hasLaw_pi hlaw
  let f : (upperTriangle n → ℝ) → selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ) :=
    fun x ↦ (symmetricCoordinates n).symm fun ij ↦
      (Real.sqrt n)⁻¹ * ((if ij.1.1 = ij.1.2 then Real.sqrt 2 else 1) * x ij)
  have hf : Measurable f := by
    unfold f
    fun_prop
  have hgoe : goeMeasure n = (Measure.pi fun _ : upperTriangle n ↦ gaussianReal 0 1).map f := by
    have hproj := measurePreserving_pi_comp_embedding
      (fun _ : Fin n × Fin n ↦ gaussianReal 0 1)
      (Function.Embedding.subtype fun ij : Fin n × Fin n ↦ ij.1 ≤ ij.2)
    rw [← hproj.map_eq, Measure.map_map hf hproj.measurable]
    rfl
  rw [hgoe]
  exact (hasLaw_map hf.aemeasurable).fun_comp hpi

/-- Building `TauCeti.Probability.goeMatrix` from independent standard Gaussian entries produces
`goeMeasure n`. -/
theorem hasLaw_goeMatrix {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {n : ℕ} (g : Fin n × Fin n → Ω → ℝ)
    (hindep : iIndepFun g P)
    (hlaw : ∀ ij : Fin n × Fin n, HasLaw (g ij) (gaussianReal 0 1) P) :
    HasLaw (fun ω ↦ goeMatrix n (fun p ↦ g p ω)) (goeMeasure n) P :=
  (hasLaw_map (measurable_goeMatrix n).aemeasurable).fun_comp (hindep.hasLaw_pi hlaw)

/-- Building `TauCeti.Probability.gueMatrix` from independent standard Gaussian entries produces
`gueMeasure n`. -/
theorem hasLaw_gueMatrix {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {n : ℕ} (g : Fin n × Fin n → Ω → ℝ)
    (hindep : iIndepFun g P)
    (hlaw : ∀ ij : Fin n × Fin n, HasLaw (g ij) (gaussianReal 0 1) P) :
    HasLaw (fun ω ↦ gueMatrix n (fun p ↦ g p ω)) (gueMeasure n) P :=
  (hasLaw_map (measurable_gueMatrix n).aemeasurable).fun_comp (hindep.hasLaw_pi hlaw)

/-- Building `TauCeti.Probability.gaussianEnsemble` from independent standard Gaussian entries
produces `gaussianEnsembleLaw β n`. -/
theorem hasLaw_gaussianEnsemble {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {β n : ℕ} (g : Fin n × Fin n → Ω → ℝ)
    (hindep : iIndepFun g P)
    (hlaw : ∀ ij : Fin n × Fin n, HasLaw (g ij) (gaussianReal 0 1) P) :
    HasLaw (fun ω ↦ gaussianEnsemble β n (fun p ↦ g p ω)) (gaussianEnsembleLaw β n) P :=
  (hasLaw_map (measurable_gaussianEnsemble β n).aemeasurable).fun_comp (hindep.hasLaw_pi hlaw)

/-! ### Standard Gaussian representation, low dimensions, and Gaussianity -/

/-- `TauCeti.Probability.goeMeasure n` is `ProbabilityTheory.stdGaussian` on the real symmetric
subspace rescaled by `√2 / √n`. -/
theorem goeMeasure_eq_map_stdGaussian (n : ℕ) :
    goeMeasure n =
      (stdGaussian (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ))).map
        ((Real.sqrt 2 / Real.sqrt n) • ·) := by
  have hproj := measurePreserving_pi_comp_embedding
    (fun _ : Fin n × Fin n ↦ gaussianReal 0 1)
    (Function.Embedding.subtype fun ij : Fin n × Fin n ↦ ij.1 ≤ ij.2)
  rw [stdGaussian_eq_map_pi_orthonormalBasis (symmetricOrthonormalBasis n),
    ← hproj.map_eq, Measure.map_map (by fun_prop) hproj.measurable,
    Measure.map_map (by fun_prop) (by fun_prop), goeMeasure_def]
  exact congrArg (fun f ↦ (Measure.pi fun _ : Fin n × Fin n ↦ gaussianReal 0 1).map f)
    (funext fun g ↦ goeMatrix_eq_smul_sum_orthonormalBasis n g)

/-- `TauCeti.Probability.gueMeasure n` is `ProbabilityTheory.stdGaussian` on the complex Hermitian
subspace rescaled by `(√n)⁻¹`. -/
theorem gueMeasure_eq_map_stdGaussian (n : ℕ) :
    gueMeasure n =
      (stdGaussian (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ))).map
        ((Real.sqrt n)⁻¹ • ·) := by
  rw [stdGaussian_eq_map_pi_orthonormalBasis (hermitianOrthonormalBasis n),
    Measure.map_map (by fun_prop) (by fun_prop), gueMeasure_def]
  exact congrArg (fun f ↦ (Measure.pi fun _ : Fin n × Fin n ↦ gaussianReal 0 1).map f)
    (funext fun g ↦ gueMatrix_eq_smul_sum_orthonormalBasis n g)

/-- `TauCeti.Probability.goeMeasure` is a Gaussian measure on the real symmetric subspace. -/
instance isGaussian_goeMeasure (n : ℕ) : IsGaussian (goeMeasure n) := by
  have hlin : (((Real.sqrt 2 / Real.sqrt n) • ·) :
      selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ) →
        selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)) =
      ⇑((Real.sqrt 2 / Real.sqrt n) • ContinuousLinearMap.id ℝ _) := rfl
  rw [goeMeasure_eq_map_stdGaussian, hlin]
  infer_instance

/-- `TauCeti.Probability.gueMeasure` is a Gaussian measure on the complex Hermitian subspace. -/
instance isGaussian_gueMeasure (n : ℕ) : IsGaussian (gueMeasure n) := by
  have hlin : (((Real.sqrt n)⁻¹ • ·) :
      selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ) →
        selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) =
      ⇑((Real.sqrt n)⁻¹ • ContinuousLinearMap.id ℝ _) := rfl
  rw [gueMeasure_eq_map_stdGaussian, hlin]
  infer_instance

/-- In dimension zero, `TauCeti.Probability.goeMeasure` is the Dirac mass at zero. -/
@[simp]
theorem goeMeasure_zero : goeMeasure 0 = Measure.dirac 0 := by
  rw [goeMeasure_eq_map_stdGaussian]
  simp

/-- In dimension zero, `TauCeti.Probability.gueMeasure` is the Dirac mass at zero. -/
@[simp]
theorem gueMeasure_zero : gueMeasure 0 = Measure.dirac 0 := by
  rw [gueMeasure_eq_map_stdGaussian]
  simp

/-- In dimension one, reading the single entry of `TauCeti.Probability.goeMeasure 1` gives
`N(0, 2)`. -/
@[simp]
theorem map_symmetricFinOneEquiv_goeMeasure :
    (goeMeasure 1).map symmetricFinOneEquiv = gaussianReal 0 2 := by
  rw [goeMeasure_def,
    Measure.map_map symmetricFinOneEquiv.continuous.measurable (measurable_goeMatrix 1)]
  have hfun : (symmetricFinOneEquiv ∘ goeMatrix 1 : (Fin 1 × Fin 1 → ℝ) → ℝ) =
      (Real.sqrt 2 * ·) ∘ fun g ↦ g (0, 0) := by
    funext g
    simp
  rw [hfun, ← Measure.map_map (by fun_prop) (by fun_prop),
    (measurePreserving_eval (fun _ : Fin 1 × Fin 1 ↦ gaussianReal 0 1) (0, 0)).map_eq,
    gaussianReal_map_const_mul]
  simp only [mul_zero, mul_one]
  exact congrArg (gaussianReal 0) (NNReal.eq (Real.sq_sqrt (by norm_num)))

/-- In dimension one, reading the single real entry of `TauCeti.Probability.gueMeasure 1` gives
`N(0, 1)`. -/
@[simp]
theorem map_hermitianFinOneEquiv_gueMeasure :
    (gueMeasure 1).map hermitianFinOneEquiv = gaussianReal 0 1 := by
  rw [gueMeasure_def,
    Measure.map_map hermitianFinOneEquiv.continuous.measurable (measurable_gueMatrix 1)]
  have hfun : (hermitianFinOneEquiv ∘ gueMatrix 1 : (Fin 1 × Fin 1 → ℝ) → ℝ) =
      fun g ↦ g (0, 0) := by
    funext g
    simp
  rw [hfun, (measurePreserving_eval (fun _ : Fin 1 × Fin 1 ↦ gaussianReal 0 1) (0, 0)).map_eq]

/-! ### Orthogonal and unitary conjugation invariance -/

/-- Orthogonal conjugation `A ↦ U * A * Uᵀ` preserves `TauCeti.Probability.goeMeasure n`. -/
theorem measurePreserving_symmetricConj_goeMeasure {n : ℕ}
    (U : Matrix.orthogonalGroup (Fin n) ℝ) :
    MeasurePreserving (Matrix.unitaryGroup.symmetricConj U) (goeMeasure n) (goeMeasure n) where
  measurable := (Matrix.unitaryGroup.symmetricConj U).continuous.measurable
  map_eq := by
    rw [goeMeasure_eq_map_stdGaussian,
      Measure.map_map (Matrix.unitaryGroup.symmetricConj U).continuous.measurable (by fun_prop)]
    have hcomm : (Matrix.unitaryGroup.symmetricConj U : _ → _) ∘
          ((Real.sqrt 2 / Real.sqrt n) • ·) =
        ((Real.sqrt 2 / Real.sqrt n) • ·) ∘ Matrix.unitaryGroup.symmetricConj U :=
      funext fun A ↦ map_smul (Matrix.unitaryGroup.symmetricConj U) _ A
    rw [hcomm, ← Measure.map_map (by fun_prop)
      (Matrix.unitaryGroup.symmetricConj U).continuous.measurable,
      stdGaussian_map (Matrix.unitaryGroup.symmetricConj U)]

/-- Pushing `TauCeti.Probability.goeMeasure` forward along orthogonal conjugation leaves it
unchanged. -/
@[simp]
theorem map_symmetricConj_goeMeasure {n : ℕ} (U : Matrix.orthogonalGroup (Fin n) ℝ) :
    (goeMeasure n).map (Matrix.unitaryGroup.symmetricConj U) = goeMeasure n :=
  (measurePreserving_symmetricConj_goeMeasure U).map_eq

/-- Orthogonal conjugation preserves `ProbabilityTheory.HasLaw` for
`TauCeti.Probability.goeMeasure`. -/
theorem _root_.ProbabilityTheory.HasLaw.symmetricConj_goeMeasure {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}
    {H : Ω → selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)}
    (hH : HasLaw H (goeMeasure n) P) (U : Matrix.orthogonalGroup (Fin n) ℝ) :
    HasLaw (fun ω ↦ Matrix.unitaryGroup.symmetricConj U (H ω)) (goeMeasure n) P :=
  (measurePreserving_symmetricConj_goeMeasure U).fun_comp_hasLaw hH

/-- A random symmetric matrix has law `TauCeti.Probability.goeMeasure` if and only if its
orthogonal conjugate does. -/
@[simp]
theorem hasLaw_symmetricConj_goeMeasure_iff {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {n : ℕ} {H : Ω → selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)}
    (U : Matrix.orthogonalGroup (Fin n) ℝ) :
    HasLaw (fun ω ↦ Matrix.unitaryGroup.symmetricConj U (H ω)) (goeMeasure n) P ↔
      HasLaw H (goeMeasure n) P where
  mp h := by
    have h' := h.symmetricConj_goeMeasure U⁻¹
    simpa [Matrix.unitaryGroup.symmetricConj_inv] using h'
  mpr h := h.symmetricConj_goeMeasure U

/-- Unitary conjugation `A ↦ U * A * Uᴴ` preserves `TauCeti.Probability.gueMeasure n`. -/
theorem measurePreserving_hermitianConj_gueMeasure {n : ℕ}
    (U : Matrix.unitaryGroup (Fin n) ℂ) :
    MeasurePreserving (Matrix.unitaryGroup.hermitianConj U) (gueMeasure n) (gueMeasure n) where
  measurable := (Matrix.unitaryGroup.hermitianConj U).continuous.measurable
  map_eq := by
    rw [gueMeasure_eq_map_stdGaussian,
      Measure.map_map (Matrix.unitaryGroup.hermitianConj U).continuous.measurable (by fun_prop)]
    have hcomm : (Matrix.unitaryGroup.hermitianConj U : _ → _) ∘ ((Real.sqrt n)⁻¹ • ·) =
        ((Real.sqrt n)⁻¹ • ·) ∘ Matrix.unitaryGroup.hermitianConj U :=
      funext fun A ↦ map_smul (Matrix.unitaryGroup.hermitianConj U) _ A
    rw [hcomm, ← Measure.map_map (by fun_prop)
      (Matrix.unitaryGroup.hermitianConj U).continuous.measurable,
      stdGaussian_map (Matrix.unitaryGroup.hermitianConj U)]

/-- Pushing `TauCeti.Probability.gueMeasure` forward along unitary conjugation leaves it
unchanged. -/
@[simp]
theorem map_hermitianConj_gueMeasure {n : ℕ} (U : Matrix.unitaryGroup (Fin n) ℂ) :
    (gueMeasure n).map (Matrix.unitaryGroup.hermitianConj U) = gueMeasure n :=
  (measurePreserving_hermitianConj_gueMeasure U).map_eq

/-- Unitary conjugation preserves `ProbabilityTheory.HasLaw` for
`TauCeti.Probability.gueMeasure`. -/
theorem _root_.ProbabilityTheory.HasLaw.hermitianConj_gueMeasure {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}
    {H : Ω → selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)}
    (hH : HasLaw H (gueMeasure n) P) (U : Matrix.unitaryGroup (Fin n) ℂ) :
    HasLaw (fun ω ↦ Matrix.unitaryGroup.hermitianConj U (H ω)) (gueMeasure n) P :=
  (measurePreserving_hermitianConj_gueMeasure U).fun_comp_hasLaw hH

/-- A random Hermitian matrix has law `TauCeti.Probability.gueMeasure` if and only if its unitary
conjugate does. -/
@[simp]
theorem hasLaw_hermitianConj_gueMeasure_iff {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {n : ℕ} {H : Ω → selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)}
    (U : Matrix.unitaryGroup (Fin n) ℂ) :
    HasLaw (fun ω ↦ Matrix.unitaryGroup.hermitianConj U (H ω)) (gueMeasure n) P ↔
      HasLaw H (gueMeasure n) P where
  mp h := by
    have h' := h.hermitianConj_gueMeasure U⁻¹
    simpa [Matrix.unitaryGroup.hermitianConj_inv] using h'
  mpr h := h.hermitianConj_gueMeasure U

/-- Ambient orthogonal conjugation preserves `TauCeti.Probability.gaussianEnsembleLaw 1 n`. -/
theorem map_orthogonalConj_gaussianEnsembleLaw_one {n : ℕ}
    (U : Matrix.orthogonalGroup (Fin n) ℝ) :
    (gaussianEnsembleLaw 1 n).map
        (fun H ↦ (U : Matrix (Fin n) (Fin n) ℝ).map Complex.ofReal * H *
          ((U : Matrix (Fin n) (Fin n) ℝ).map Complex.ofReal)ᴴ) =
      gaussianEnsembleLaw 1 n := by
  let castSym : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ) → Matrix (Fin n) (Fin n) ℂ :=
    fun A ↦ (A : Matrix (Fin n) (Fin n) ℝ).map Complex.ofReal
  have hcast : Measurable castSym :=
    (continuous_matrix fun i j ↦ Complex.continuous_ofReal.comp
      (selfAdjoint.continuous_coe_apply i j)).measurable
  have hconj : Measurable fun H : Matrix (Fin n) (Fin n) ℂ ↦
      (U : Matrix (Fin n) (Fin n) ℝ).map Complex.ofReal * H *
        ((U : Matrix (Fin n) (Fin n) ℝ).map Complex.ofReal)ᴴ :=
    ((continuous_const.mul continuous_id).mul continuous_const).measurable
  rw [gaussianEnsembleLaw_one_eq_map_goeMeasure, Measure.map_map hconj hcast]
  have hcomm : (fun H : Matrix (Fin n) (Fin n) ℂ ↦
        (U : Matrix (Fin n) (Fin n) ℝ).map Complex.ofReal * H *
          ((U : Matrix (Fin n) (Fin n) ℝ).map Complex.ofReal)ᴴ) ∘ castSym =
      castSym ∘ Matrix.unitaryGroup.symmetricConj U := by
    funext A
    ext i j
    simp [castSym, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [hcomm, ← Measure.map_map hcast (Matrix.unitaryGroup.symmetricConj U).continuous.measurable,
    map_symmetricConj_goeMeasure]

/-- Ambient unitary conjugation preserves `TauCeti.Probability.gaussianEnsembleLaw 2 n`. -/
theorem map_unitaryConj_gaussianEnsembleLaw_two {n : ℕ}
    (U : Matrix.unitaryGroup (Fin n) ℂ) :
    (gaussianEnsembleLaw 2 n).map
        (fun H ↦ (U : Matrix (Fin n) (Fin n) ℂ) * H * (U : Matrix (Fin n) (Fin n) ℂ)ᴴ) =
      gaussianEnsembleLaw 2 n := by
  have hconj : Measurable fun H : Matrix (Fin n) (Fin n) ℂ ↦
      (U : Matrix (Fin n) (Fin n) ℂ) * H * (U : Matrix (Fin n) (Fin n) ℂ)ᴴ :=
    ((continuous_const.mul continuous_id).mul continuous_const).measurable
  rw [gaussianEnsembleLaw_two_eq_map_gueMeasure, Measure.map_map hconj measurable_subtype_coe]
  have hcomm : (fun H : Matrix (Fin n) (Fin n) ℂ ↦
        (U : Matrix (Fin n) (Fin n) ℂ) * H * (U : Matrix (Fin n) (Fin n) ℂ)ᴴ) ∘ Subtype.val =
      Subtype.val ∘ Matrix.unitaryGroup.hermitianConj U :=
    funext fun A ↦ (Matrix.unitaryGroup.coe_hermitianConj_apply U A).symm
  rw [hcomm, ← Measure.map_map measurable_subtype_coe
    (Matrix.unitaryGroup.hermitianConj U).continuous.measurable, map_hermitianConj_gueMeasure]

end Probability

end TauCeti
