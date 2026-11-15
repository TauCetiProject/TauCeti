/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.HermitianMatrix.Lebesgue
public import TauCeti.MeasureTheory.Measure.SymmetricMatrix.Orthogonal
public import TauCeti.Probability.Distributions.Gaussian.Density
public import TauCeti.Probability.RandomMatrices.GaussianEnsemble.Basic
public import Mathlib.Probability.HasLaw

/-!
# Laws, densities, and conjugation invariance of the GOE and GUE

With independent standard Gaussian coordinates `g : Fin n × Fin n → ℝ`, the `β = 1` construction
`TauCeti.Probability.gaussianEnsemble` takes values in the real symmetric subspace
`selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)` and defines the **Gaussian orthogonal
ensemble** (`TauCeti.Probability.goeMeasure n`), while the `β = 2` construction takes values in
the complex Hermitian subspace `selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)` and defines
the **Gaussian unitary ensemble** (`TauCeti.Probability.gueMeasure n`).

This file connects both ensembles to the standard Gaussian measure `ProbabilityTheory.stdGaussian`
on their respective Frobenius inner-product spaces:
* `goeMeasure n` is the pushforward of `stdGaussian` under `A ↦ √(2 / n) • A`;
* `gueMeasure n` is the pushforward of `stdGaussian` under `A ↦ (√n)⁻¹ • A`.

From this identification and the Frobenius-volume comparisons on the two self-adjoint spaces we
obtain:
1. orthogonal conjugation invariance of `goeMeasure n` and unitary conjugation invariance of
   `gueMeasure n` (`map_symmetricConj_goeMeasure`, `map_hermitianConj_gueMeasure`);
2. the exact densities `goePDF` with respect to `TauCeti.symmetricLebesgue n` and `guePDF` with
   respect to `TauCeti.hermitianLebesgue n` (as well as with respect to the Frobenius `volume`) at
   every dimension `n` (in dimension zero, the normalizing powers and trace vanish in the
   exponents so the density is `1` against the Dirac measure);
3. the coordinate Gaussian marginals and joint independence of the on-or-above-diagonal entries
   of the GOE and the diagonal real and strictly upper-triangular real and imaginary parts of the
   GUE;
4. equivalence of the independent-Gaussian entry characterization and the invariant trace-density
   characterization for both ensembles (`goe_iIndepFun_iff_withDensity` and
   `gue_iIndepFun_iff_withDensity`), together with the `MeasureTheory.HasPDF` and
   `MeasureTheory.pdf` bridges.

## Main definitions

* `TauCeti.Probability.gaussianEnsembleReal` and `TauCeti.Probability.gaussianEnsembleHermitian`:
  the `β = 1` and `β = 2` ensemble maps into the real symmetric and complex Hermitian subspaces.
* `TauCeti.Probability.goeMeasure` and `TauCeti.Probability.gueMeasure`: the GOE and GUE laws on
  the real symmetric and complex Hermitian subspaces.
* `TauCeti.Probability.goePDFReal`, `TauCeti.Probability.goePDF`,
  `TauCeti.Probability.guePDFReal`, `TauCeti.Probability.guePDF`: the invariant trace densities.

## Main results

* `TauCeti.Probability.goeMeasure_eq_map_stdGaussian` and
  `TauCeti.Probability.gueMeasure_eq_map_stdGaussian`: representation as scaled `stdGaussian`
  measures.
* `TauCeti.Probability.map_symmetricConj_goeMeasure` and
  `TauCeti.Probability.map_hermitianConj_gueMeasure`: orthogonal and unitary conjugation
  invariance.
* `TauCeti.Probability.goeMeasure_eq_withDensity_symmetricLebesgue` and
  `TauCeti.Probability.gueMeasure_eq_withDensity_hermitianLebesgue`: the exact coordinate
  Lebesgue densities, with `HasPDF` and `pdf` bridges `hasPDF_of_hasLaw_goeMeasure`,
  `pdf_eq_goePDF_of_hasLaw_goeMeasure`, `hasPDF_of_hasLaw_gueMeasure`, and
  `pdf_eq_guePDF_of_hasLaw_gueMeasure`.
* `TauCeti.Probability.hasLaw_goeMeasure_iff_iIndepFun`,
  `TauCeti.Probability.goe_iIndepFun_iff_withDensity`,
  `TauCeti.Probability.hasLaw_gueMeasure_iff_iIndepFun`, and
  `TauCeti.Probability.gue_iIndepFun_iff_withDensity`: equivalence of the entry and
  invariant-density characterizations.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), §2.5, (2.5.1), p. 52.
* T. Tao, *Topics in Random Matrix Theory*, Graduate Studies in Mathematics 132, AMS (2012), §2.6.
-/

public section

noncomputable section

open MeasureTheory Matrix ProbabilityTheory Real
open scoped ENNReal NNReal ComplexConjugate RealInnerProductSpace

namespace TauCeti.Probability

/-! ### Ensemble maps into the self-adjoint subspaces -/

section EnsembleMaps

/-- The `β = 1` Gaussian ensemble valued in the real symmetric subspace: on the diagonal
`√2 * g (i, i) / √n`, and off the diagonal `g (min i j, max i j) / √n`. Complexifying its entries
recovers `TauCeti.Probability.gaussianEnsemble 1 n g`. -/
def gaussianEnsembleReal (n : ℕ) (g : Fin n × Fin n → ℝ) :
    selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ) :=
  (symmetricCoordinates n).symm fun ij ↦
    (Real.sqrt n)⁻¹ * (if ij.1.1 = ij.1.2 then Real.sqrt 2 else 1) * g ij.1

theorem symmetricCoordinates_gaussianEnsembleReal (n : ℕ) (g : Fin n × Fin n → ℝ)
    (ij : upperTriangle n) :
    symmetricCoordinates n (gaussianEnsembleReal n g) ij =
      (Real.sqrt n)⁻¹ * (if ij.1.1 = ij.1.2 then Real.sqrt 2 else 1) * g ij.1 :=
  (symmetricCoordinates n).apply_symm_apply _ ▸ rfl

@[fun_prop]
theorem continuous_gaussianEnsembleReal (n : ℕ) :
    Continuous (gaussianEnsembleReal n) := by
  unfold gaussianEnsembleReal
  fun_prop

@[fun_prop]
theorem measurable_gaussianEnsembleReal (n : ℕ) :
    Measurable (gaussianEnsembleReal n) :=
  (continuous_gaussianEnsembleReal n).measurable

@[simp]
theorem coe_gaussianEnsembleReal_apply_self {n : ℕ} (g : Fin n × Fin n → ℝ) (i : Fin n) :
    (gaussianEnsembleReal n g : Matrix (Fin n) (Fin n) ℝ) i i =
      (Real.sqrt n)⁻¹ * (Real.sqrt 2 * g (i, i)) := by
  rw [gaussianEnsembleReal, coe_symmetricCoordinates_symm_apply_of_le n _ le_rfl]
  simp [mul_assoc]

@[simp]
theorem coe_gaussianEnsembleReal_apply_of_lt {n : ℕ} (g : Fin n × Fin n → ℝ) {i j : Fin n}
    (h : i < j) :
    (gaussianEnsembleReal n g : Matrix (Fin n) (Fin n) ℝ) i j =
      (Real.sqrt n)⁻¹ * g (i, j) := by
  rw [gaussianEnsembleReal, coe_symmetricCoordinates_symm_apply_of_le n _ h.le]
  simp [h.ne]

@[simp]
theorem coe_gaussianEnsembleReal_apply_of_gt {n : ℕ} (g : Fin n × Fin n → ℝ) {i j : Fin n}
    (h : j < i) :
    (gaussianEnsembleReal n g : Matrix (Fin n) (Fin n) ℝ) i j =
      (Real.sqrt n)⁻¹ * g (j, i) := by
  rw [gaussianEnsembleReal, coe_symmetricCoordinates_symm_apply_of_ge n _ h.le]
  simp [h.ne]

/-- Complexifying `TauCeti.Probability.gaussianEnsembleReal` gives `gaussianEnsemble 1 n g`: the
`β = 1` ensemble matrix is real. -/
@[simp]
theorem map_ofReal_coe_gaussianEnsembleReal (n : ℕ) (g : Fin n × Fin n → ℝ) :
    (gaussianEnsembleReal n g : Matrix (Fin n) (Fin n) ℝ).map Complex.ofReal =
      gaussianEnsemble 1 n g := by
  ext i j
  rw [Matrix.map_apply]
  rcases lt_trichotomy i j with h | rfl | h
  · simp [h]
  · simp
  · simp [h]

/-- In the Frobenius-orthonormal basis `TauCeti.symmetricOrthonormalBasis`, `gaussianEnsembleReal`
scales the upper-triangular coordinate vector by `√(2 / n)`. -/
theorem gaussianEnsembleReal_eq_smul_sum_symmetricOrthonormalBasis (n : ℕ)
    (g : Fin n × Fin n → ℝ) :
    gaussianEnsembleReal n g =
      Real.sqrt (2 / n) • ∑ ij : upperTriangle n, g ij.1 • symmetricOrthonormalBasis n ij := by
  apply (symmetricCoordinates n).injective
  ext ij
  rw [symmetricCoordinates_gaussianEnsembleReal, map_smul, map_sum, Pi.smul_apply,
    Finset.sum_apply]
  simp only [coe_symmetricOrthonormalBasis_apply, smul_smul, map_smul, Pi.smul_apply,
    symmetricBasis_apply, ContinuousLinearEquiv.apply_symm_apply, Pi.single_apply, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, smul_eq_mul]
  rw [Real.sqrt_div (by positivity), div_eq_mul_inv (Real.sqrt 2)]
  by_cases hd : ij.1.1 = ij.1.2
  · simp only [hd, ↓reduceIte]
    ring
  · simp only [hd, ↓reduceIte]
    have h2 : Real.sqrt 2 ≠ 0 := by positivity
    field_simp [h2]

/-- The `β = 2` Gaussian ensemble bundled into the complex Hermitian subspace. -/
def gaussianEnsembleHermitian (n : ℕ) (g : Fin n × Fin n → ℝ) :
    selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ) :=
  ⟨gaussianEnsemble 2 n g, (isHermitian_gaussianEnsemble 2 n g).isSelfAdjoint⟩

@[simp]
theorem coe_gaussianEnsembleHermitian (n : ℕ) (g : Fin n × Fin n → ℝ) :
    (gaussianEnsembleHermitian n g : Matrix (Fin n) (Fin n) ℂ) = gaussianEnsemble 2 n g :=
  (rfl)

/-- In `TauCeti.hermitianCoordinates`, `gaussianEnsembleHermitian n g` multiplies diagonal
coordinates by `(√n)⁻¹` and off-diagonal real and imaginary coordinates by `(√(2 * n))⁻¹`. -/
@[simp]
theorem hermitianCoordinates_gaussianEnsembleHermitian (n : ℕ) (g : Fin n × Fin n → ℝ)
    (ab : Fin n × Fin n) :
    hermitianCoordinates n (gaussianEnsembleHermitian n g) ab =
      (Real.sqrt n)⁻¹ * (if ab.1 = ab.2 then 1 else (Real.sqrt 2)⁻¹) * g ab := by
  obtain ⟨i, j⟩ := ab
  rcases lt_trichotomy i j with h | rfl | h
  · rw [hermitianCoordinates_apply_of_le n _ h.le, coe_gaussianEnsembleHermitian,
      gaussianEnsemble_apply_of_lt_of_ne_one g (by decide) h]
    simp only [h.ne, ↓reduceIte, div_eq_mul_inv]
    simp only [← Complex.ofReal_inv, Complex.mul_re, Complex.add_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  · rw [hermitianCoordinates_apply_self, coe_gaussianEnsembleHermitian,
      gaussianEnsemble_apply_self_of_ne_one g (by decide)]
    simp [← Complex.ofReal_inv]
  · rw [hermitianCoordinates_apply_of_gt n _ h, coe_gaussianEnsembleHermitian,
      gaussianEnsemble_apply_of_lt_of_ne_one g (by decide) h]
    simp only [h.ne', ↓reduceIte, div_eq_mul_inv]
    simp only [← Complex.ofReal_inv, Complex.mul_im, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring

@[fun_prop]
theorem continuous_gaussianEnsembleHermitian (n : ℕ) :
    Continuous (gaussianEnsembleHermitian n) := by
  have heq : gaussianEnsembleHermitian n =
      (hermitianCoordinates n).symm ∘ fun g ab ↦
        (Real.sqrt n)⁻¹ * (if ab.1 = ab.2 then 1 else (Real.sqrt 2)⁻¹) * g ab := by
    funext g
    exact ((hermitianCoordinates n).symm_apply_eq.2
      (funext fun ab ↦ (hermitianCoordinates_gaussianEnsembleHermitian n g ab).symm)).symm
  rw [heq]
  fun_prop

@[fun_prop]
theorem measurable_gaussianEnsembleHermitian (n : ℕ) :
    Measurable (gaussianEnsembleHermitian n) :=
  (continuous_gaussianEnsembleHermitian n).measurable

/-- In the Frobenius-orthonormal basis `TauCeti.hermitianOrthonormalBasis`,
`gaussianEnsembleHermitian` scales the `n²` coordinate vector by `(√n)⁻¹`. -/
theorem gaussianEnsembleHermitian_eq_smul_sum_hermitianOrthonormalBasis (n : ℕ)
    (g : Fin n × Fin n → ℝ) :
    gaussianEnsembleHermitian n g =
      (Real.sqrt n)⁻¹ • ∑ ab : Fin n × Fin n, g ab • hermitianOrthonormalBasis n ab := by
  apply (hermitianCoordinates n).injective
  ext ab
  rw [hermitianCoordinates_gaussianEnsembleHermitian, map_smul, map_sum, Pi.smul_apply,
    Finset.sum_apply]
  simp only [coe_hermitianOrthonormalBasis_apply, smul_smul, map_smul, Pi.smul_apply,
    hermitianBasis_apply, ContinuousLinearEquiv.apply_symm_apply, Pi.single_apply, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, smul_eq_mul]
  split_ifs <;> ring

/-- For the `2 × 2` GUE matrix, the `(0, 1)` entry has real part `g (0, 1) / 2` and imaginary part
`g (1, 0) / 2`. -/
theorem re_gaussianEnsemble_two_two_zero_one (g : Fin 2 × Fin 2 → ℝ) :
    (gaussianEnsemble 2 2 g 0 1).re = g (0, 1) / 2 := by
  have h := hermitianCoordinates_gaussianEnsembleHermitian 2 g (0, 1)
  rw [hermitianCoordinates_apply_of_le 2 _ (by decide), coe_gaussianEnsembleHermitian] at h
  have h01 : ((0 : Fin 2), (1 : Fin 2)).1 ≠ ((0 : Fin 2), (1 : Fin 2)).2 := by decide
  rw [h, ite_eq_right h01, Nat.cast_ofNat, ← mul_inv,
    Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring

theorem im_gaussianEnsemble_two_two_zero_one (g : Fin 2 × Fin 2 → ℝ) :
    (gaussianEnsemble 2 2 g 0 1).im = g (1, 0) / 2 := by
  have h := hermitianCoordinates_gaussianEnsembleHermitian 2 g (1, 0)
  rw [hermitianCoordinates_apply_of_gt 2 _ (by decide), coe_gaussianEnsembleHermitian] at h
  have h10 : ((1 : Fin 2), (0 : Fin 2)).1 ≠ ((1 : Fin 2), (0 : Fin 2)).2 := by decide
  rw [h, ite_eq_right h10, Nat.cast_ofNat, ← mul_inv,
    Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring

end EnsembleMaps

/-! ### The GOE and GUE probability measures -/

/-- **The Gaussian orthogonal ensemble (GOE)** on the `n × n` real symmetric subspace: the law of
`TauCeti.Probability.gaussianEnsembleReal n g` for independent standard Gaussian entries `g`. -/
def goeMeasure (n : ℕ) : Measure (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)) :=
  (Measure.pi fun _ : Fin n × Fin n ↦ gaussianReal 0 1).map (gaussianEnsembleReal n)

theorem goeMeasure_def (n : ℕ) :
    goeMeasure n =
      (Measure.pi fun _ : Fin n × Fin n ↦ gaussianReal 0 1).map (gaussianEnsembleReal n) :=
  (rfl)

/-- **The Gaussian unitary ensemble (GUE)** on the `n × n` complex Hermitian subspace: the law of
`TauCeti.Probability.gaussianEnsembleHermitian n g` for independent standard Gaussian entries
`g`. -/
def gueMeasure (n : ℕ) : Measure (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) :=
  (Measure.pi fun _ : Fin n × Fin n ↦ gaussianReal 0 1).map (gaussianEnsembleHermitian n)

theorem gueMeasure_def (n : ℕ) :
    gueMeasure n =
      (Measure.pi fun _ : Fin n × Fin n ↦ gaussianReal 0 1).map (gaussianEnsembleHermitian n) :=
  (rfl)

private theorem measurePreserving_restrict_upperTriangle (n : ℕ) :
    MeasurePreserving (fun (g : Fin n × Fin n → ℝ) (ij : upperTriangle n) ↦ g ij.1)
      (Measure.pi fun _ : Fin n × Fin n ↦ gaussianReal 0 1)
      (Measure.pi fun _ : upperTriangle n ↦ gaussianReal 0 1) := by
  simpa [Function.comp_def] using
    (measurePreserving_fst (μ := Measure.pi fun _ : upperTriangle n ↦ gaussianReal 0 1)
      (ν := Measure.pi fun _ : {ij : Fin n × Fin n // ¬ij.1 ≤ ij.2} ↦ gaussianReal 0 1)).comp
      (measurePreserving_piEquivPiSubtypeProd
        (fun _ : Fin n × Fin n ↦ (gaussianReal 0 1 : Measure ℝ)) fun ij ↦ ij.1 ≤ ij.2)

/-- The GOE law is the standard Gaussian measure on the real symmetric Frobenius inner-product
space rescaled by `√(2 / n)`. -/
theorem goeMeasure_eq_map_stdGaussian (n : ℕ) :
    goeMeasure n =
      (stdGaussian (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ))).map
        (fun A ↦ Real.sqrt (2 / n) • A) := by
  rw [stdGaussian_eq_map_pi_orthonormalBasis (symmetricOrthonormalBasis n),
    Measure.map_map (by fun_prop) (by fun_prop),
    ← (measurePreserving_restrict_upperTriangle n).map_eq,
    Measure.map_map (by fun_prop) (by fun_prop), goeMeasure_def]
  congr 1
  funext g
  exact gaussianEnsembleReal_eq_smul_sum_symmetricOrthonormalBasis n g

/-- The GUE law is the standard Gaussian measure on the complex Hermitian Frobenius inner-product
space rescaled by `(√n)⁻¹`. -/
theorem gueMeasure_eq_map_stdGaussian (n : ℕ) :
    gueMeasure n =
      (stdGaussian (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ))).map
        (fun A ↦ (Real.sqrt n)⁻¹ • A) := by
  rw [stdGaussian_eq_map_pi_orthonormalBasis (hermitianOrthonormalBasis n),
    Measure.map_map (by fun_prop) (by fun_prop), gueMeasure_def]
  congr 1
  funext g
  exact gaussianEnsembleHermitian_eq_smul_sum_hermitianOrthonormalBasis n g

instance isProbabilityMeasure_goeMeasure (n : ℕ) : IsProbabilityMeasure (goeMeasure n) :=
  (Measure.isProbabilityMeasure_map_iff (measurable_gaussianEnsembleReal n).aemeasurable).2
    inferInstance

instance isProbabilityMeasure_gueMeasure (n : ℕ) : IsProbabilityMeasure (gueMeasure n) :=
  (Measure.isProbabilityMeasure_map_iff (measurable_gaussianEnsembleHermitian n).aemeasurable).2
    inferInstance

instance isGaussian_goeMeasure (n : ℕ) : IsGaussian (goeMeasure n) := by
  rw [goeMeasure_eq_map_stdGaussian]
  change IsGaussian ((stdGaussian _).map
    (ContinuousLinearMap.lsmul ℝ ℝ (Real.sqrt (2 / n)) :
      selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ) →L[ℝ] _))
  infer_instance

instance isGaussian_gueMeasure (n : ℕ) : IsGaussian (gueMeasure n) := by
  rw [gueMeasure_eq_map_stdGaussian]
  change IsGaussian ((stdGaussian _).map
    (ContinuousLinearMap.lsmul ℝ ℝ (Real.sqrt n)⁻¹ :
      selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ) →L[ℝ] _))
  infer_instance

@[simp]
theorem goeMeasure_zero : goeMeasure 0 = Measure.dirac 0 := by
  rw [goeMeasure_eq_map_stdGaussian]
  simp [Measure.map_const]

@[simp]
theorem gueMeasure_zero : gueMeasure 0 = Measure.dirac 0 := by
  rw [gueMeasure_eq_map_stdGaussian]
  simp [Measure.map_const]

/-- Complexifying `goeMeasure n` gives the ambient `β = 1` law of `gaussianEnsemble 1 n`. -/
theorem map_ofReal_goeMeasure (n : ℕ) :
    (goeMeasure n).map
        (fun A : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ) ↦
          (A : Matrix (Fin n) (Fin n) ℝ).map Complex.ofReal) =
      (Measure.pi fun _ : Fin n × Fin n ↦ gaussianReal 0 1).map (gaussianEnsemble 1 n) := by
  have hm : Measurable fun A : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ) ↦
      (A : Matrix (Fin n) (Fin n) ℝ).map Complex.ofReal := by
    change Measurable fun A : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ) ↦
      fun i j : Fin n ↦ Complex.ofReal ((A : Matrix (Fin n) (Fin n) ℝ) i j)
    rw [measurable_pi_iff]
    intro i
    rw [measurable_pi_iff]
    intro j
    exact Complex.continuous_ofReal.measurable.comp (selfAdjoint.measurable_coe_apply i j)
  rw [goeMeasure_def, Measure.map_map hm (measurable_gaussianEnsembleReal n)]
  congr 1
  funext g
  exact map_ofReal_coe_gaussianEnsembleReal n g

/-- Coercing `gueMeasure n` to `Matrix (Fin n) (Fin n) ℂ` gives the ambient `β = 2` law of
`gaussianEnsemble 2 n`. -/
theorem map_coe_gueMeasure (n : ℕ) :
    (gueMeasure n).map Subtype.val =
      (Measure.pi fun _ : Fin n × Fin n ↦ gaussianReal 0 1).map (gaussianEnsemble 2 n) := by
  rw [gueMeasure_def,
    Measure.map_map measurable_subtype_coe (measurable_gaussianEnsembleHermitian n)]
  rfl

/-! ### Orthogonal and unitary conjugation invariance -/

/-- **Orthogonal conjugation invariance of the GOE.** Conjugating by any orthogonal matrix
`O : Matrix.orthogonalGroup (Fin n) ℝ` preserves `goeMeasure n`. -/
@[simp]
theorem map_symmetricConj_goeMeasure {n : ℕ} (O : Matrix.orthogonalGroup (Fin n) ℝ) :
    (goeMeasure n).map (Matrix.UnitaryGroup.symmetricConj O) = goeMeasure n := by
  rw [goeMeasure_eq_map_stdGaussian,
    Measure.map_map (Matrix.UnitaryGroup.symmetricConj O).continuous.measurable (by fun_prop)]
  have hcomm : (Matrix.UnitaryGroup.symmetricConj O) ∘
      (fun A : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ) ↦ Real.sqrt (2 / n) • A) =
      (fun A ↦ Real.sqrt (2 / n) • A) ∘ (Matrix.UnitaryGroup.symmetricConj O) := by
    funext A
    exact map_smul (Matrix.UnitaryGroup.symmetricConj O) _ A
  rw [hcomm, ← Measure.map_map (by fun_prop)
    (Matrix.UnitaryGroup.symmetricConj O).continuous.measurable,
    stdGaussian_map (Matrix.UnitaryGroup.symmetricConj O)]

theorem measurePreserving_symmetricConj_goeMeasure {n : ℕ}
    (O : Matrix.orthogonalGroup (Fin n) ℝ) :
    MeasurePreserving (Matrix.UnitaryGroup.symmetricConj O) (goeMeasure n) (goeMeasure n) :=
  ⟨(Matrix.UnitaryGroup.symmetricConj O).continuous.measurable, map_symmetricConj_goeMeasure O⟩

/-- **Unitary conjugation invariance of the GUE.** Conjugating by any unitary matrix
`U : Matrix.unitaryGroup (Fin n) ℂ` preserves `gueMeasure n`. -/
@[simp]
theorem map_hermitianConj_gueMeasure {n : ℕ} (U : Matrix.unitaryGroup (Fin n) ℂ) :
    (gueMeasure n).map (Matrix.UnitaryGroup.hermitianConj U) = gueMeasure n := by
  rw [gueMeasure_eq_map_stdGaussian,
    Measure.map_map (Matrix.UnitaryGroup.hermitianConj U).continuous.measurable (by fun_prop)]
  have hcomm : (Matrix.UnitaryGroup.hermitianConj U) ∘
      (fun A : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ) ↦ (Real.sqrt n)⁻¹ • A) =
      (fun A ↦ (Real.sqrt n)⁻¹ • A) ∘ (Matrix.UnitaryGroup.hermitianConj U) := by
    funext A
    exact map_smul (Matrix.UnitaryGroup.hermitianConj U) _ A
  rw [hcomm, ← Measure.map_map (by fun_prop)
    (Matrix.UnitaryGroup.hermitianConj U).continuous.measurable,
    stdGaussian_map (Matrix.UnitaryGroup.hermitianConj U)]

theorem measurePreserving_hermitianConj_gueMeasure {n : ℕ}
    (U : Matrix.unitaryGroup (Fin n) ℂ) :
    MeasurePreserving (Matrix.UnitaryGroup.hermitianConj U) (gueMeasure n) (gueMeasure n) :=
  ⟨(Matrix.UnitaryGroup.hermitianConj U).continuous.measurable, map_hermitianConj_gueMeasure U⟩

/-! ### Coordinate pushforwards, entry laws, and joint independence -/

private theorem gaussianReal_map_goeScale (n : ℕ) (ij : upperTriangle n) :
    (gaussianReal 0 1).map
      (fun x : ℝ ↦ (Real.sqrt n)⁻¹ * (if ij.1.1 = ij.1.2 then Real.sqrt 2 else 1) * x) =
      gaussianReal 0 (if ij.1.1 = ij.1.2 then (2 / n : ℝ≥0) else (1 / n : ℝ≥0)) := by
  rw [gaussianReal_map_const_mul]
  simp only [mul_zero, mul_one]
  congr 1
  apply NNReal.coe_injective
  rcases Nat.eq_zero_or_pos n with rfl | _
  · simp
  · have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    by_cases hd : ij.1.1 = ij.1.2
    · simp only [hd, ↓reduceIte, NNReal.coe_mk, NNReal.coe_div, NNReal.coe_ofNat,
        NNReal.coe_natCast, mul_pow, inv_pow, Real.sq_sqrt hn0,
        Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2)]
      ring
    · simp only [hd, ↓reduceIte, mul_one, NNReal.coe_mk, NNReal.coe_div, NNReal.coe_one,
        NNReal.coe_natCast, inv_pow, Real.sq_sqrt hn0]
      ring

/-- Under `TauCeti.symmetricCoordinates`, `goeMeasure n` is the product of centred Gaussian laws
of variance `2 / n` on the diagonal and `1 / n` strictly above it. -/
theorem map_symmetricCoordinates_goeMeasure (n : ℕ) :
    (goeMeasure n).map (symmetricCoordinates n) =
      Measure.pi fun ij : upperTriangle n ↦
        gaussianReal 0 (if ij.1.1 = ij.1.2 then (2 / n : ℝ≥0) else (1 / n : ℝ≥0)) := by
  rw [goeMeasure_def, Measure.map_map (symmetricCoordinates n).continuous.measurable
    (measurable_gaussianEnsembleReal n)]
  have hcomp : (symmetricCoordinates n ∘ gaussianEnsembleReal n) =
      (fun (x : upperTriangle n → ℝ) (ij : upperTriangle n) ↦
        (Real.sqrt n)⁻¹ * (if ij.1.1 = ij.1.2 then Real.sqrt 2 else 1) * x ij) ∘
        (fun (g : Fin n × Fin n → ℝ) (ij : upperTriangle n) ↦ g ij.1) := by
    funext g ij
    exact symmetricCoordinates_gaussianEnsembleReal n g ij
  rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop),
    (measurePreserving_restrict_upperTriangle n).map_eq]
  exact (measurePreserving_pi _ _ fun ij ↦
    ⟨by fun_prop, gaussianReal_map_goeScale n ij⟩).map_eq

/-- Each entry `(i, j)` of a GOE matrix has law `N(0, 2 / n)` on the diagonal and `N(0, 1 / n)`
off the diagonal. -/
theorem map_apply_goeMeasure {n : ℕ} (i j : Fin n) :
    (goeMeasure n).map
        (fun A : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ) ↦
          (A : Matrix (Fin n) (Fin n) ℝ) i j) =
      gaussianReal 0 (if i = j then (2 / n : ℝ≥0) else (1 / n : ℝ≥0)) := by
  rcases le_total i j with hij | hji
  · have heval := (measurePreserving_eval
      (fun kl : upperTriangle n ↦
        gaussianReal 0 (if kl.1.1 = kl.1.2 then (2 / n : ℝ≥0) else (1 / n : ℝ≥0)))
      ⟨(i, j), hij⟩).map_eq
    rw [← map_symmetricCoordinates_goeMeasure n,
      Measure.map_map (measurable_pi_apply _) (symmetricCoordinates n).continuous.measurable]
      at heval
    simpa only [Function.comp_def, symmetricCoordinates_apply] using heval
  · have hsymm : (fun A : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ) ↦
        (A : Matrix (Fin n) (Fin n) ℝ) i j) =
        fun A : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ) ↦
          (A : Matrix (Fin n) (Fin n) ℝ) j i := by
      funext A
      exact selfAdjoint.coe_apply_comm A i j
    have heval := (measurePreserving_eval
      (fun kl : upperTriangle n ↦
        gaussianReal 0 (if kl.1.1 = kl.1.2 then (2 / n : ℝ≥0) else (1 / n : ℝ≥0)))
      ⟨(j, i), hji⟩).map_eq
    rw [← map_symmetricCoordinates_goeMeasure n,
      Measure.map_map (measurable_pi_apply _) (symmetricCoordinates n).continuous.measurable]
      at heval
    rw [hsymm]
    simpa [Function.comp_def, eq_comm] using heval

/-- In dimension `1`, the single entry of `goeMeasure 1` is `N(0, 2)`. -/
theorem map_symmetricFinOneEquiv_goeMeasure :
    (goeMeasure 1).map symmetricFinOneEquiv = gaussianReal 0 2 := by
  have h : (symmetricFinOneEquiv : _ → ℝ) =
      fun A : selfAdjoint.submodule ℝ (Matrix (Fin 1) (Fin 1) ℝ) ↦
        (A : Matrix (Fin 1) (Fin 1) ℝ) 0 0 :=
    funext symmetricFinOneEquiv_apply
  rw [h, map_apply_goeMeasure]
  simp

/-- The on-or-above-diagonal entries of `goeMeasure n` are mutually independent. -/
theorem iIndepFun_symmetricCoordinates_goeMeasure (n : ℕ) :
    iIndepFun (fun (ij : upperTriangle n)
        (A : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)) ↦
      (A : Matrix (Fin n) (Fin n) ℝ) ij.1.1 ij.1.2) (goeMeasure n) := by
  refine (iIndepFun_iff_hasLaw_pi_pi fun (ij : upperTriangle n) ↦
    ⟨(selfAdjoint.measurable_coe_apply _ _).aemeasurable, map_apply_goeMeasure ij.1.1 ij.1.2⟩).2 ?_
  simp only [← symmetricCoordinates_apply]
  exact ⟨(symmetricCoordinates n).continuous.aemeasurable, map_symmetricCoordinates_goeMeasure n⟩

private theorem gaussianReal_map_gueScale (n : ℕ) (ab : Fin n × Fin n) :
    (gaussianReal 0 1).map
      (fun x : ℝ ↦ (Real.sqrt n)⁻¹ * (if ab.1 = ab.2 then 1 else (Real.sqrt 2)⁻¹) * x) =
      gaussianReal 0 (if ab.1 = ab.2 then (1 / n : ℝ≥0) else (1 / (2 * n) : ℝ≥0)) := by
  rw [gaussianReal_map_const_mul]
  simp only [mul_zero, mul_one]
  congr 1
  apply NNReal.coe_injective
  rcases Nat.eq_zero_or_pos n with rfl | _
  · simp
  · have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    by_cases hd : ab.1 = ab.2
    · simp only [hd, ↓reduceIte, mul_one, NNReal.coe_mk, NNReal.coe_div, NNReal.coe_one,
        NNReal.coe_natCast, inv_pow, Real.sq_sqrt hn0]
      ring
    · simp only [hd, ↓reduceIte, NNReal.coe_mk, NNReal.coe_div, NNReal.coe_one, NNReal.coe_mul,
        NNReal.coe_ofNat, NNReal.coe_natCast, mul_pow, inv_pow, Real.sq_sqrt hn0,
        Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2)]
      ring

/-- Under `TauCeti.hermitianCoordinates`, `gueMeasure n` is the product of centred Gaussian laws
of variance `1 / n` on the diagonal and `1 / (2 * n)` on the strictly upper-triangular real and
imaginary coordinates. -/
theorem map_hermitianCoordinates_gueMeasure (n : ℕ) :
    (gueMeasure n).map (hermitianCoordinates n) =
      Measure.pi fun ab : Fin n × Fin n ↦
        gaussianReal 0 (if ab.1 = ab.2 then (1 / n : ℝ≥0) else (1 / (2 * n) : ℝ≥0)) := by
  rw [gueMeasure_def, Measure.map_map (hermitianCoordinates n).continuous.measurable
    (measurable_gaussianEnsembleHermitian n)]
  have hcomp : (hermitianCoordinates n ∘ gaussianEnsembleHermitian n) =
      fun (g : Fin n × Fin n → ℝ) (ab : Fin n × Fin n) ↦
        (Real.sqrt n)⁻¹ * (if ab.1 = ab.2 then 1 else (Real.sqrt 2)⁻¹) * g ab := by
    funext g ab
    simp
  rw [hcomp]
  exact (measurePreserving_pi _ _ fun ab ↦
    ⟨by fun_prop, gaussianReal_map_gueScale n ab⟩).map_eq

/-- Each real coordinate `hermitianCoordinates n · ab` of `gueMeasure n` has law `N(0, 1 / n)` on
the diagonal (`ab.1 = ab.2`) and `N(0, 1 / (2 * n))` off the diagonal (`ab.1 ≠ ab.2`). -/
theorem map_hermitianCoordinates_apply_gueMeasure {n : ℕ} (ab : Fin n × Fin n) :
    (gueMeasure n).map (fun A ↦ hermitianCoordinates n A ab) =
      gaussianReal 0 (if ab.1 = ab.2 then (1 / n : ℝ≥0) else (1 / (2 * n) : ℝ≥0)) := by
  have heval := (measurePreserving_eval
    (fun cd : Fin n × Fin n ↦
      gaussianReal 0 (if cd.1 = cd.2 then (1 / n : ℝ≥0) else (1 / (2 * n) : ℝ≥0))) ab).map_eq
  rw [← map_hermitianCoordinates_gueMeasure n,
    Measure.map_map (measurable_pi_apply _) (hermitianCoordinates n).continuous.measurable] at heval
  exact heval

/-- Diagonal real parts of a GUE matrix have law `N(0, 1 / n)`. -/
theorem map_re_apply_self_gueMeasure {n : ℕ} (i : Fin n) :
    (gueMeasure n).map
        (fun A : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ) ↦
          ((A : Matrix (Fin n) (Fin n) ℂ) i i).re) =
      gaussianReal 0 (1 / n) := by
  simpa using map_hermitianCoordinates_apply_gueMeasure (i, i)

/-- Off-diagonal real parts of a GUE matrix have law `N(0, 1 / (2 * n))`. -/
theorem map_re_apply_of_ne_gueMeasure {n : ℕ} {i j : Fin n} (h : i ≠ j) :
    (gueMeasure n).map
        (fun A : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ) ↦
          ((A : Matrix (Fin n) (Fin n) ℂ) i j).re) =
      gaussianReal 0 (1 / (2 * n)) := by
  rcases lt_or_gt_of_ne h with hij | hji
  · have hfun : (fun A : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ) ↦
        ((A : Matrix (Fin n) (Fin n) ℂ) i j).re) =
        fun A ↦ hermitianCoordinates n A (i, j) := by
      funext A
      exact (hermitianCoordinates_apply_of_le n A hij.le).symm
    rw [hfun, map_hermitianCoordinates_apply_gueMeasure]
    simp [h]
  · have hfun : (fun A : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ) ↦
        ((A : Matrix (Fin n) (Fin n) ℂ) i j).re) =
        fun A ↦ hermitianCoordinates n A (j, i) := by
      funext A
      rw [hermitianCoordinates_apply_of_le n A hji.le, ← selfAdjoint.coe_apply_conj A j i,
        Complex.conj_re]
    rw [hfun, map_hermitianCoordinates_apply_gueMeasure]
    simp [h.symm]

/-- Strictly upper-triangular imaginary parts `(A i j).im` (`i < j`) of a GUE matrix have law
`N(0, 1 / (2 * n))`. -/
theorem map_im_apply_of_lt_gueMeasure {n : ℕ} {i j : Fin n} (h : i < j) :
    (gueMeasure n).map
        (fun A : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ) ↦
          ((A : Matrix (Fin n) (Fin n) ℂ) i j).im) =
      gaussianReal 0 (1 / (2 * n)) := by
  have hfun : (fun A : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ) ↦
      ((A : Matrix (Fin n) (Fin n) ℂ) i j).im) =
      fun A ↦ hermitianCoordinates n A (j, i) := by
    funext A
    exact (hermitianCoordinates_apply_of_gt n A h).symm
  rw [hfun, map_hermitianCoordinates_apply_gueMeasure]
  simp [h.ne']

/-- In dimension `1`, the single entry of `gueMeasure 1` is `N(0, 1)`. -/
theorem map_hermitianFinOneEquiv_gueMeasure :
    (gueMeasure 1).map hermitianFinOneEquiv = gaussianReal 0 1 := by
  have h : (hermitianFinOneEquiv : _ → ℝ) =
      fun A : selfAdjoint.submodule ℝ (Matrix (Fin 1) (Fin 1) ℂ) ↦
        ((A : Matrix (Fin 1) (Fin 1) ℂ) 0 0).re :=
    funext hermitianFinOneEquiv_apply
  rw [h, map_re_apply_self_gueMeasure]
  simp

/-- The `n²` real coordinates `hermitianCoordinates n` of `gueMeasure n` are mutually
independent. -/
theorem iIndepFun_hermitianCoordinates_gueMeasure (n : ℕ) :
    iIndepFun (fun (ab : Fin n × Fin n)
        (A : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) ↦
      hermitianCoordinates n A ab) (gueMeasure n) := by
  refine (iIndepFun_iff_hasLaw_pi_pi fun ab ↦
    ⟨((measurable_pi_apply ab).comp (hermitianCoordinates n).continuous.measurable).aemeasurable,
      map_hermitianCoordinates_apply_gueMeasure ab⟩).2 ?_
  exact ⟨(hermitianCoordinates n).continuous.aemeasurable, map_hermitianCoordinates_gueMeasure n⟩

/-! ### Exact trace densities on the self-adjoint spaces -/

/-- The real-valued **GOE density** on the `n × n` real symmetric subspace with respect to
`TauCeti.symmetricLebesgue n`:
`2 ^ (-n / 2) * (2 * π / n) ^ (-n * (n + 1) / 4) * exp (-n / 4 * tr (A²))` (AGZ (2.5.1), p. 52,
rescaled by `√n`). -/
def goePDFReal (n : ℕ) (A : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)) : ℝ :=
  (2 : ℝ) ^ (-(n : ℝ) / 2) * (2 * π / n) ^ (-((n : ℝ) * ((n : ℝ) + 1)) / 4) *
    Real.exp (-(n : ℝ) / 4 * ((A : Matrix (Fin n) (Fin n) ℝ) * A).trace)

/-- The defining formula of `TauCeti.Probability.goePDFReal`. -/
theorem goePDFReal_def (n : ℕ) (A : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)) :
    goePDFReal n A =
      (2 : ℝ) ^ (-(n : ℝ) / 2) * (2 * π / n) ^ (-((n : ℝ) * ((n : ℝ) + 1)) / 4) *
        Real.exp (-(n : ℝ) / 4 * ((A : Matrix (Fin n) (Fin n) ℝ) * A).trace) :=
  (rfl)

/-- The `ℝ≥0∞`-valued companion to `TauCeti.Probability.goePDFReal`. -/
def goePDF (n : ℕ) (A : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)) : ℝ≥0∞ :=
  ENNReal.ofReal (goePDFReal n A)

/-- The `ℝ≥0∞`-valued GOE density is `ENNReal.ofReal ∘ goePDFReal`. -/
theorem goePDF_def (n : ℕ) (A : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)) :
    goePDF n A = ENNReal.ofReal (goePDFReal n A) :=
  (rfl)

/-- The real-valued **GUE density** on the `n × n` complex Hermitian subspace with respect to
`TauCeti.hermitianLebesgue n`:
`2 ^ (-n / 2) * (π / n) ^ (-n² / 2) * exp (-n / 2 * Re tr (A²))`. -/
def guePDFReal (n : ℕ) (A : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) : ℝ :=
  (2 : ℝ) ^ (-(n : ℝ) / 2) * (π / n) ^ (-(n : ℝ) ^ 2 / 2) *
    Real.exp (-(n : ℝ) / 2 * ((A : Matrix (Fin n) (Fin n) ℂ) * A).trace.re)

/-- The defining formula of `TauCeti.Probability.guePDFReal`. -/
theorem guePDFReal_def (n : ℕ) (A : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) :
    guePDFReal n A =
      (2 : ℝ) ^ (-(n : ℝ) / 2) * (π / n) ^ (-(n : ℝ) ^ 2 / 2) *
        Real.exp (-(n : ℝ) / 2 * ((A : Matrix (Fin n) (Fin n) ℂ) * A).trace.re) :=
  (rfl)

/-- The `ℝ≥0∞`-valued companion to `TauCeti.Probability.guePDFReal`. -/
def guePDF (n : ℕ) (A : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) : ℝ≥0∞ :=
  ENNReal.ofReal (guePDFReal n A)

/-- The `ℝ≥0∞`-valued GUE density is `ENNReal.ofReal ∘ guePDFReal`. -/
theorem guePDF_def (n : ℕ) (A : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) :
    guePDF n A = ENNReal.ofReal (guePDFReal n A) :=
  (rfl)

theorem goePDFReal_pos (n : ℕ) (A : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)) :
    0 < goePDFReal n A := by
  unfold goePDFReal
  rcases Nat.eq_zero_or_pos n with rfl | _
  · simp
  · positivity

theorem goePDFReal_nonneg (n : ℕ) (A : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)) :
    0 ≤ goePDFReal n A :=
  (goePDFReal_pos n A).le

theorem guePDFReal_pos (n : ℕ) (A : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) :
    0 < guePDFReal n A := by
  unfold guePDFReal
  rcases Nat.eq_zero_or_pos n with rfl | _
  · simp
  · positivity

theorem guePDFReal_nonneg (n : ℕ) (A : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) :
    0 ≤ guePDFReal n A :=
  (guePDFReal_pos n A).le

@[fun_prop]
theorem continuous_goePDFReal (n : ℕ) : Continuous (goePDFReal n) := by
  have : Continuous fun A : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ) ↦
      ((A : Matrix (Fin n) (Fin n) ℝ) * A).trace := by
    simp only [← selfAdjoint.inner_eq_trace_mul]
    exact continuous_id.inner continuous_id
  unfold goePDFReal
  fun_prop

@[fun_prop]
theorem measurable_goePDFReal (n : ℕ) : Measurable (goePDFReal n) :=
  (continuous_goePDFReal n).measurable

@[fun_prop]
theorem measurable_goePDF (n : ℕ) : Measurable (goePDF n) :=
  (measurable_goePDFReal n).ennreal_ofReal

@[fun_prop]
theorem continuous_guePDFReal (n : ℕ) : Continuous (guePDFReal n) := by
  have : Continuous fun A : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ) ↦
      ((A : Matrix (Fin n) (Fin n) ℂ) * A).trace.re := by
    simp only [← selfAdjoint.norm_sq_eq_re_trace_mul_self]
    fun_prop
  unfold guePDFReal
  fun_prop

@[fun_prop]
theorem measurable_guePDFReal (n : ℕ) : Measurable (guePDFReal n) :=
  (continuous_guePDFReal n).measurable

@[fun_prop]
theorem measurable_guePDF (n : ℕ) : Measurable (guePDF n) :=
  (measurable_guePDFReal n).ennreal_ofReal

/-- `goePDFReal` is invariant under orthogonal conjugation. -/
@[simp]
theorem goePDFReal_symmetricConj {n : ℕ} (O : Matrix.orthogonalGroup (Fin n) ℝ)
    (A : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)) :
    goePDFReal n (Matrix.UnitaryGroup.symmetricConj O A) = goePDFReal n A := by
  simp only [goePDFReal, Matrix.UnitaryGroup.trace_mul_self_symmetricConj_apply]

@[simp]
theorem goePDF_symmetricConj {n : ℕ} (O : Matrix.orthogonalGroup (Fin n) ℝ)
    (A : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)) :
    goePDF n (Matrix.UnitaryGroup.symmetricConj O A) = goePDF n A := by
  simp only [goePDF, goePDFReal_symmetricConj]

/-- `guePDFReal` is invariant under unitary conjugation. -/
@[simp]
theorem guePDFReal_hermitianConj {n : ℕ} (U : Matrix.unitaryGroup (Fin n) ℂ)
    (A : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) :
    guePDFReal n (Matrix.UnitaryGroup.hermitianConj U A) = guePDFReal n A := by
  simp only [guePDFReal, Matrix.UnitaryGroup.re_trace_mul_self_hermitianConj_apply]

@[simp]
theorem guePDF_hermitianConj {n : ℕ} (U : Matrix.unitaryGroup (Fin n) ℂ)
    (A : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) :
    guePDF n (Matrix.UnitaryGroup.hermitianConj U A) = guePDF n A := by
  simp only [guePDF, guePDFReal_hermitianConj]

private theorem two_mul_finrank_symmetricMatrix (n : ℕ) :
    2 * (Module.finrank ℝ (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)) : ℝ) =
      (n : ℝ) * ((n : ℝ) + 1) := by
  rw [finrank_symmetricMatrix]
  have h2 : 2 * (n * (n + 1) / 2) = n * (n + 1) :=
    Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self n)
  exact_mod_cast h2

/-- `goeMeasure n` has density `(4 * π / n) ^ (-n * (n + 1) / 4) * exp (-n / 4 * tr (A²))` with
respect to the Frobenius `volume` on the real symmetric subspace. -/
theorem goeMeasure_eq_withDensity_volume (n : ℕ) :
    goeMeasure n =
      (volume : Measure (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ))).withDensity
        fun A ↦ ENNReal.ofReal
          ((4 * π / n) ^ (-((n : ℝ) * ((n : ℝ) + 1)) / 4) *
            Real.exp (-(n : ℝ) / 4 * ((A : Matrix (Fin n) (Fin n) ℝ) * A).trace)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hvol : (volume : Measure (selfAdjoint.submodule ℝ (Matrix (Fin 0) (Fin 0) ℝ))) =
        Measure.dirac 0 := by
      rw [volume_symmetricMatrix_eq_smul_symmetricLebesgue 0, symmetricLebesgue_zero]
      simp
    have hdens : (fun A : selfAdjoint.submodule ℝ (Matrix (Fin 0) (Fin 0) ℝ) ↦
        ENNReal.ofReal ((4 * π / (0 : ℝ)) ^ (-((0 : ℝ) * ((0 : ℝ) + 1)) / 4) *
          Real.exp (-(0 : ℝ) / 4 * ((A : Matrix (Fin 0) (Fin 0) ℝ) * A).trace))) = 1 := by
      funext A
      simp
    rw [goeMeasure_zero, hvol]
    push_cast
    rw [hdens, withDensity_one]
  · set E := selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)
    set c : ℝ := Real.sqrt (2 / n)
    have hc : 0 < c := by positivity
    let L : E ≃L[ℝ] E := ContinuousLinearEquiv.smulLeft (Units.mk0 c hc.ne')
    have hfun : (fun A : E ↦ c • A) = fun A ↦ 0 + L A := by
      funext A
      simp [L, Units.smul_def]
    have hdet : LinearMap.det (L : E →ₗ[ℝ] E) = c ^ Module.finrank ℝ E := by
      have hL : (L : E →ₗ[ℝ] E) = c • LinearMap.id := by
        ext A
        simp [L, Units.smul_def]
      rw [hL, LinearMap.det_smul, LinearMap.det_id, mul_one]
    rw [goeMeasure_eq_map_stdGaussian, stdGaussian_eq_withDensity_norm E, hfun,
      Measure.map_affine_withDensity volume L 0, hdet]
    refine withDensity_congr_ae (.of_forall fun A ↦ ?_)
    dsimp only
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have hsymm : L.symm (A - 0) = c⁻¹ • A :=
      L.symm_apply_eq.2 (by simp [L, Units.smul_def, smul_smul, inv_mul_cancel₀ hc.ne'])
    have hnorm : ‖c⁻¹ • A‖ ^ 2 = (n : ℝ) / 2 * ((A : Matrix (Fin n) (Fin n) ℝ) * A).trace := by
      rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, inv_pow,
        Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 / n), inv_div,
        ← real_inner_self_eq_norm_sq, selfAdjoint.inner_eq_trace_mul]
    have hcd : |(c ^ Module.finrank ℝ E)⁻¹| *
        (2 * π) ^ (-(Module.finrank ℝ E : ℝ) / 2) =
        (4 * π / n) ^ (-((n : ℝ) * ((n : ℝ) + 1)) / 4) := by
      dsimp only [c, E]
      rw [abs_of_pos (by positivity), ← inv_pow, Real.sqrt_eq_rpow,
        ← Real.rpow_neg (by positivity : (0 : ℝ) ≤ 2 / n),
        ← Real.rpow_natCast _ (Module.finrank ℝ _),
        ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 2 / n)]
      have hexp1 : -(1 / 2 : ℝ) *
          (Module.finrank ℝ (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)) : ℝ) =
          -((n : ℝ) * ((n : ℝ) + 1)) / 4 := by
        linarith [two_mul_finrank_symmetricMatrix n]
      have hexp2 :
          -(Module.finrank ℝ (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)) : ℝ) / 2 =
          -((n : ℝ) * ((n : ℝ) + 1)) / 4 := by
        linarith [two_mul_finrank_symmetricMatrix n]
      rw [hexp1, hexp2,
        ← Real.mul_rpow (by positivity : (0 : ℝ) ≤ 2 / n) (by positivity : (0 : ℝ) ≤ 2 * π)]
      congr 1
      ring
    rw [hsymm, hnorm, ← mul_assoc, hcd]
    congr 2
    ring

/-- **Density of the GOE on the real symmetric subspace** (AGZ (2.5.1), p. 52). `goeMeasure n` is
`TauCeti.symmetricLebesgue n` weighted by `TauCeti.Probability.goePDF n`. -/
theorem goeMeasure_eq_withDensity_symmetricLebesgue (n : ℕ) :
    goeMeasure n = (symmetricLebesgue n).withDensity (goePDF n) := by
  rw [goeMeasure_eq_withDensity_volume n, volume_symmetricMatrix_eq_smul_symmetricLebesgue n,
    withDensity_smul_measure, ← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
  refine withDensity_congr_ae (.of_forall fun A ↦ ?_)
  simp only [Pi.smul_apply, smul_eq_mul, goePDF, goePDFReal]
  have hrpow : Real.rpow 2 (((n : ℝ) * ((n : ℝ) - 1)) / 4) =
      (2 : ℝ) ^ (((n : ℝ) * ((n : ℝ) - 1)) / 4) := rfl
  rw [hrpow, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have hsplit : (4 * π / (n : ℝ)) ^ (-((n : ℝ) * ((n : ℝ) + 1)) / 4) =
      (2 : ℝ) ^ (-((n : ℝ) * ((n : ℝ) + 1)) / 4) *
        (2 * π / n) ^ (-((n : ℝ) * ((n : ℝ) + 1)) / 4) := by
    have h4 : 4 * π / (n : ℝ) = 2 * (2 * π / n) := by ring
    rw [h4, Real.mul_rpow (by norm_num) (by positivity)]
  rw [hsplit, ← mul_assoc, ← mul_assoc, ← Real.rpow_add two_pos]
  congr 2
  congr 1
  ring

/-- The Radon–Nikodym derivative of `goeMeasure n` with respect to `symmetricLebesgue n` is
`goePDF n`. -/
theorem rnDeriv_goeMeasure_symmetricLebesgue (n : ℕ) :
    (goeMeasure n).rnDeriv (symmetricLebesgue n) =ᵐ[symmetricLebesgue n] goePDF n := by
  rw [goeMeasure_eq_withDensity_symmetricLebesgue n]
  exact Measure.rnDeriv_withDensity _ (measurable_goePDF n)

/-- A random real symmetric matrix with law `goeMeasure n` has a density with respect to
`TauCeti.symmetricLebesgue n`. -/
theorem hasPDF_of_hasLaw_goeMeasure {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}
    {H : Ω → selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)}
    (hH : HasLaw H (goeMeasure n) P) : HasPDF H P (symmetricLebesgue n) :=
  hasPDF_of_hasLaw_withDensity (measurable_goePDF n).aemeasurable
    (by rwa [← goeMeasure_eq_withDensity_symmetricLebesgue n])

/-- The density of a GOE random matrix with respect to `TauCeti.symmetricLebesgue n` is
`TauCeti.Probability.goePDF n`. -/
theorem pdf_eq_goePDF_of_hasLaw_goeMeasure {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}
    {H : Ω → selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)}
    (hH : HasLaw H (goeMeasure n) P) :
    pdf H P (symmetricLebesgue n) =ᵐ[symmetricLebesgue n] goePDF n :=
  pdf_eq_of_hasLaw_withDensity (measurable_goePDF n).aemeasurable
    (by rwa [← goeMeasure_eq_withDensity_symmetricLebesgue n])

/-- `gueMeasure n` has density `(2 * π / n) ^ (-n² / 2) * exp (-n / 2 * Re tr (A²))` with respect
to the Frobenius `volume` on the complex Hermitian subspace. -/
theorem gueMeasure_eq_withDensity_volume (n : ℕ) :
    gueMeasure n =
      (volume : Measure (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ))).withDensity
        fun A ↦ ENNReal.ofReal
          ((2 * π / n) ^ (-(n : ℝ) ^ 2 / 2) *
            Real.exp (-(n : ℝ) / 2 * ((A : Matrix (Fin n) (Fin n) ℂ) * A).trace.re)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hvol : (volume : Measure (selfAdjoint.submodule ℝ (Matrix (Fin 0) (Fin 0) ℂ))) =
        Measure.dirac 0 := by
      rw [volume_hermitianMatrix_eq_smul_hermitianLebesgue 0, hermitianLebesgue_zero]
      simp
    have hdens : (fun A : selfAdjoint.submodule ℝ (Matrix (Fin 0) (Fin 0) ℂ) ↦
        ENNReal.ofReal ((2 * π / (0 : ℝ)) ^ (-(0 : ℝ) ^ 2 / 2) *
          Real.exp (-(0 : ℝ) / 2 * ((A : Matrix (Fin 0) (Fin 0) ℂ) * A).trace.re))) = 1 := by
      funext A
      simp
    rw [gueMeasure_zero, hvol]
    push_cast
    rw [hdens, withDensity_one]
  · set E := selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)
    set c : ℝ := (Real.sqrt n)⁻¹
    have hc : 0 < c := by positivity
    let L : E ≃L[ℝ] E := ContinuousLinearEquiv.smulLeft (Units.mk0 c hc.ne')
    have hfun : (fun A : E ↦ c • A) = fun A ↦ 0 + L A := by
      funext A
      simp [L, Units.smul_def]
    have hdet : LinearMap.det (L : E →ₗ[ℝ] E) = c ^ Module.finrank ℝ E := by
      have hL : (L : E →ₗ[ℝ] E) = c • LinearMap.id := by
        ext A
        simp [L, Units.smul_def]
      rw [hL, LinearMap.det_smul, LinearMap.det_id, mul_one]
    rw [gueMeasure_eq_map_stdGaussian, stdGaussian_eq_withDensity_norm E, hfun,
      Measure.map_affine_withDensity volume L 0, hdet]
    refine withDensity_congr_ae (.of_forall fun A ↦ ?_)
    dsimp only
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have hsymm : L.symm (A - 0) = c⁻¹ • A :=
      L.symm_apply_eq.2 (by simp [L, Units.smul_def, smul_smul, inv_mul_cancel₀ hc.ne'])
    have hnorm : ‖c⁻¹ • A‖ ^ 2 = (n : ℝ) * ((A : Matrix (Fin n) (Fin n) ℂ) * A).trace.re := by
      rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, inv_inv,
        Real.sq_sqrt (Nat.cast_nonneg n), selfAdjoint.norm_sq_eq_re_trace_mul_self]
    have hcd : |(c ^ Module.finrank ℝ E)⁻¹| *
        (2 * π) ^ (-(Module.finrank ℝ E : ℝ) / 2) =
        (2 * π / n) ^ (-(n : ℝ) ^ 2 / 2) := by
      dsimp only [c, E]
      have hn0 : (0 : ℝ) < n := Nat.cast_pos.2 hn
      rw [abs_of_pos (by positivity), ← inv_pow, inv_inv, Real.sqrt_eq_rpow,
        ← Real.rpow_natCast _ (Module.finrank ℝ _),
        ← Real.rpow_mul hn0.le, finrank_hermitianMatrix]
      push_cast
      have hexp : (1 / 2 : ℝ) * (n : ℝ) ^ 2 = -(-(n : ℝ) ^ 2 / 2) := by ring
      rw [hexp, Real.rpow_neg hn0.le, ← Real.inv_rpow hn0.le,
        ← Real.mul_rpow (inv_nonneg.2 hn0.le) (by positivity)]
      congr 1
      ring
    rw [hsymm, hnorm, ← mul_assoc, hcd]
    congr 2
    ring

/-- **Density of the GUE on the complex Hermitian subspace.** `gueMeasure n` is
`TauCeti.hermitianLebesgue n` weighted by `TauCeti.Probability.guePDF n`. -/
theorem gueMeasure_eq_withDensity_hermitianLebesgue (n : ℕ) :
    gueMeasure n = (hermitianLebesgue n).withDensity (guePDF n) := by
  rw [gueMeasure_eq_withDensity_volume n, volume_hermitianMatrix_eq_smul_hermitianLebesgue n,
    withDensity_smul_measure, ← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
  refine withDensity_congr_ae (.of_forall fun A ↦ ?_)
  simp only [Pi.smul_apply, smul_eq_mul, guePDF, guePDFReal]
  have hrpow : Real.rpow 2 (((n : ℝ) * ((n : ℝ) - 1)) / 2) =
      (2 : ℝ) ^ (((n : ℝ) * ((n : ℝ) - 1)) / 2) := rfl
  rw [hrpow, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have hsplit : (2 * π / (n : ℝ)) ^ (-(n : ℝ) ^ 2 / 2) =
      (2 : ℝ) ^ (-(n : ℝ) ^ 2 / 2) * (π / n) ^ (-(n : ℝ) ^ 2 / 2) := by
    have h2 : 2 * π / (n : ℝ) = 2 * (π / n) := by ring
    rw [h2, Real.mul_rpow (by norm_num) (by positivity)]
  rw [hsplit, ← mul_assoc, ← mul_assoc, ← Real.rpow_add two_pos]
  congr 2
  congr 1
  ring

/-- The Radon–Nikodym derivative of `gueMeasure n` with respect to `hermitianLebesgue n` is
`guePDF n`. -/
theorem rnDeriv_gueMeasure_hermitianLebesgue (n : ℕ) :
    (gueMeasure n).rnDeriv (hermitianLebesgue n) =ᵐ[hermitianLebesgue n] guePDF n := by
  rw [gueMeasure_eq_withDensity_hermitianLebesgue n]
  exact Measure.rnDeriv_withDensity _ (measurable_guePDF n)

/-- A random complex Hermitian matrix with law `gueMeasure n` has a density with respect to
`TauCeti.hermitianLebesgue n`. -/
theorem hasPDF_of_hasLaw_gueMeasure {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}
    {H : Ω → selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)}
    (hH : HasLaw H (gueMeasure n) P) : HasPDF H P (hermitianLebesgue n) :=
  hasPDF_of_hasLaw_withDensity (measurable_guePDF n).aemeasurable
    (by rwa [← gueMeasure_eq_withDensity_hermitianLebesgue n])

/-- The density of a GUE random matrix with respect to `TauCeti.hermitianLebesgue n` is
`TauCeti.Probability.guePDF n`. -/
theorem pdf_eq_guePDF_of_hasLaw_gueMeasure {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}
    {H : Ω → selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)}
    (hH : HasLaw H (gueMeasure n) P) :
    pdf H P (hermitianLebesgue n) =ᵐ[hermitianLebesgue n] guePDF n :=
  pdf_eq_of_hasLaw_withDensity (measurable_guePDF n).aemeasurable
    (by rwa [← gueMeasure_eq_withDensity_hermitianLebesgue n])

/-! ### Equivalence of the entry and invariant-density characterizations -/

section Characterizations

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **Independent-Gaussian entry characterization of the GOE.** A random real symmetric matrix `H`
on a probability space `(Ω, P)` has law `goeMeasure n` if and only if its on-or-above-diagonal
entries are mutually independent centred Gaussians of variance `2 / n` on the diagonal and `1 / n`
above the diagonal. -/
theorem hasLaw_goeMeasure_iff_iIndepFun [IsProbabilityMeasure P] {n : ℕ}
    {H : Ω → selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)} :
    HasLaw H (goeMeasure n) P ↔
      iIndepFun (fun (ij : upperTriangle n) ω ↦ (H ω : Matrix (Fin n) (Fin n) ℝ) ij.1.1 ij.1.2) P ∧
        (∀ i : Fin n,
          HasLaw (fun ω ↦ (H ω : Matrix (Fin n) (Fin n) ℝ) i i) (gaussianReal 0 (2 / n)) P) ∧
        (∀ i j : Fin n, i < j →
          HasLaw (fun ω ↦ (H ω : Matrix (Fin n) (Fin n) ℝ) i j) (gaussianReal 0 (1 / n)) P) := by
  constructor
  · intro hH
    have hdiag : ∀ i : Fin n,
        HasLaw (fun ω ↦ (H ω : Matrix (Fin n) (Fin n) ℝ) i i) (gaussianReal 0 (2 / n)) P :=
      fun i ↦ HasLaw.comp ⟨(selfAdjoint.measurable_coe_apply i i).aemeasurable,
        by simpa using map_apply_goeMeasure i i⟩ hH
    have hoff : ∀ i j : Fin n, i < j →
        HasLaw (fun ω ↦ (H ω : Matrix (Fin n) (Fin n) ℝ) i j) (gaussianReal 0 (1 / n)) P :=
      fun i j hij ↦ HasLaw.comp ⟨(selfAdjoint.measurable_coe_apply i j).aemeasurable,
        by simpa [hij.ne] using map_apply_goeMeasure i j⟩ hH
    have hcoord : ∀ ij : upperTriangle n,
        HasLaw (fun ω ↦ (H ω : Matrix (Fin n) (Fin n) ℝ) ij.1.1 ij.1.2)
          (gaussianReal 0 (if ij.1.1 = ij.1.2 then (2 / n : ℝ≥0) else (1 / n : ℝ≥0))) P := by
      rintro ⟨⟨i, j⟩, hij⟩
      change i ≤ j at hij
      rcases hij.eq_or_lt with rfl | hlt
      · simpa using hdiag i
      · simpa [hlt.ne] using hoff i j hlt
    refine ⟨(iIndepFun_iff_hasLaw_pi_pi hcoord).2 ?_, hdiag, hoff⟩
    simp only [← symmetricCoordinates_apply, ← map_symmetricCoordinates_goeMeasure n]
    exact HasLaw.comp ⟨(symmetricCoordinates n).continuous.aemeasurable, rfl⟩ hH
  · rintro ⟨hind, hdiag, hoff⟩
    have hcoord : ∀ ij : upperTriangle n,
        HasLaw (fun ω ↦ (H ω : Matrix (Fin n) (Fin n) ℝ) ij.1.1 ij.1.2)
          (gaussianReal 0 (if ij.1.1 = ij.1.2 then (2 / n : ℝ≥0) else (1 / n : ℝ≥0))) P := by
      rintro ⟨⟨i, j⟩, hij⟩
      change i ≤ j at hij
      rcases hij.eq_or_lt with rfl | hlt
      · simpa using hdiag i
      · simpa [hlt.ne] using hoff i j hlt
    have hpi : HasLaw (fun ω ↦ symmetricCoordinates n (H ω))
        ((goeMeasure n).map (symmetricCoordinates n)) P := by
      have heq : (fun ω ↦ symmetricCoordinates n (H ω)) =
          fun ω (ij : upperTriangle n) ↦ (H ω : Matrix (Fin n) (Fin n) ℝ) ij.1.1 ij.1.2 := by
        ext ω ij
        exact symmetricCoordinates_apply n (H ω) ij
      rw [map_symmetricCoordinates_goeMeasure, heq]
      exact hind.hasLaw_pi hcoord
    have hinv : HasLaw (symmetricCoordinates n).symm (goeMeasure n)
        ((goeMeasure n).map (symmetricCoordinates n)) :=
      ⟨(symmetricCoordinates n).symm.continuous.aemeasurable, by
        rw [Measure.map_map (symmetricCoordinates n).symm.continuous.measurable
          (symmetricCoordinates n).continuous.measurable]
        simp⟩
    simpa [Function.comp_def] using hinv.comp hpi

/-- **Invariant-density characterization of the GOE.** `H` has law `goeMeasure n` if and only if
`H` is `P`-almost-everywhere measurable and `P.map H` is `symmetricLebesgue n` weighted by
`goePDF n`. -/
theorem hasLaw_goeMeasure_iff_withDensity {n : ℕ}
    {H : Ω → selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)} :
    HasLaw H (goeMeasure n) P ↔
      AEMeasurable H P ∧ P.map H = (symmetricLebesgue n).withDensity (goePDF n) := by
  rw [goeMeasure_eq_withDensity_symmetricLebesgue n]
  exact ⟨fun h ↦ ⟨h.aemeasurable, h.map_eq⟩, fun ⟨hm, heq⟩ ↦ ⟨hm, heq⟩⟩

/-- **Equivalence of the entry and invariant-density characterizations of the GOE**
(AGZ (2.5.1), p. 52). On a probability space `(Ω, P)`, the independent-Gaussian entry conditions on
a real symmetric random matrix `H` hold if and only if `H` is `P`-almost-everywhere measurable with
law `(symmetricLebesgue n).withDensity (goePDF n)`. -/
theorem goe_iIndepFun_iff_withDensity [IsProbabilityMeasure P] {n : ℕ}
    {H : Ω → selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)} :
    (iIndepFun (fun (ij : upperTriangle n) ω ↦ (H ω : Matrix (Fin n) (Fin n) ℝ) ij.1.1 ij.1.2) P ∧
      (∀ i : Fin n,
        HasLaw (fun ω ↦ (H ω : Matrix (Fin n) (Fin n) ℝ) i i) (gaussianReal 0 (2 / n)) P) ∧
      (∀ i j : Fin n, i < j →
        HasLaw (fun ω ↦ (H ω : Matrix (Fin n) (Fin n) ℝ) i j) (gaussianReal 0 (1 / n)) P)) ↔
      (AEMeasurable H P ∧ P.map H = (symmetricLebesgue n).withDensity (goePDF n)) := by
  rw [← hasLaw_goeMeasure_iff_iIndepFun, hasLaw_goeMeasure_iff_withDensity]

/-- **Independent-Gaussian coordinate characterization of the GUE.** A random complex Hermitian
matrix `H` on a probability space `(Ω, P)` has law `gueMeasure n` if and only if its `n²` real
coordinates `hermitianCoordinates n ∘ H` are mutually independent with diagonal real parts
`N(0, 1 / n)` and strictly upper-triangular real and imaginary parts `N(0, 1 / (2 * n))`. -/
theorem hasLaw_gueMeasure_iff_iIndepFun [IsProbabilityMeasure P] {n : ℕ}
    {H : Ω → selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)} :
    HasLaw H (gueMeasure n) P ↔
      iIndepFun (fun (ab : Fin n × Fin n) ω ↦ hermitianCoordinates n (H ω) ab) P ∧
        (∀ i : Fin n,
          HasLaw (fun ω ↦ ((H ω : Matrix (Fin n) (Fin n) ℂ) i i).re)
            (gaussianReal 0 (1 / n)) P) ∧
        (∀ i j : Fin n, i < j →
          HasLaw (fun ω ↦ ((H ω : Matrix (Fin n) (Fin n) ℂ) i j).re)
            (gaussianReal 0 (1 / (2 * n))) P ∧
          HasLaw (fun ω ↦ ((H ω : Matrix (Fin n) (Fin n) ℂ) i j).im)
            (gaussianReal 0 (1 / (2 * n))) P) := by
  constructor
  · intro hH
    have hdiag : ∀ i : Fin n,
        HasLaw (fun ω ↦ ((H ω : Matrix (Fin n) (Fin n) ℂ) i i).re)
          (gaussianReal 0 (1 / n)) P := fun i ↦ by
      have hlaw : HasLaw
          (fun A : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ) ↦
            ((A : Matrix (Fin n) (Fin n) ℂ) i i).re)
          (gaussianReal 0 (1 / n)) (gueMeasure n) :=
        ⟨(Complex.continuous_re.measurable.comp
          (selfAdjoint.measurable_coe_apply_complex i i)).aemeasurable,
          map_re_apply_self_gueMeasure i⟩
      exact hlaw.comp hH
    have hoff : ∀ i j : Fin n, i < j →
        HasLaw (fun ω ↦ ((H ω : Matrix (Fin n) (Fin n) ℂ) i j).re)
          (gaussianReal 0 (1 / (2 * n))) P ∧
        HasLaw (fun ω ↦ ((H ω : Matrix (Fin n) (Fin n) ℂ) i j).im)
          (gaussianReal 0 (1 / (2 * n))) P := fun i j hij ↦ by
      have hre : HasLaw
          (fun A : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ) ↦
            ((A : Matrix (Fin n) (Fin n) ℂ) i j).re)
          (gaussianReal 0 (1 / (2 * n))) (gueMeasure n) :=
        ⟨(Complex.continuous_re.measurable.comp
          (selfAdjoint.measurable_coe_apply_complex i j)).aemeasurable,
          map_re_apply_of_ne_gueMeasure hij.ne⟩
      have him : HasLaw
          (fun A : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ) ↦
            ((A : Matrix (Fin n) (Fin n) ℂ) i j).im)
          (gaussianReal 0 (1 / (2 * n))) (gueMeasure n) :=
        ⟨(Complex.continuous_im.measurable.comp
          (selfAdjoint.measurable_coe_apply_complex i j)).aemeasurable,
          map_im_apply_of_lt_gueMeasure hij⟩
      exact ⟨hre.comp hH, him.comp hH⟩
    have hcoord : ∀ ab : Fin n × Fin n,
        HasLaw (fun ω ↦ hermitianCoordinates n (H ω) ab)
          (gaussianReal 0 (if ab.1 = ab.2 then (1 / n : ℝ≥0) else (1 / (2 * n) : ℝ≥0))) P := by
      rintro ⟨i, j⟩
      rcases lt_trichotomy i j with hij | rfl | hji
      · simpa [hermitianCoordinates_apply_of_le n _ hij.le, hij.ne] using (hoff i j hij).1
      · simpa using hdiag i
      · simpa [hermitianCoordinates_apply_of_gt n _ hji, hji.ne'] using (hoff j i hji).2
    refine ⟨(iIndepFun_iff_hasLaw_pi_pi hcoord).2 ?_, hdiag, hoff⟩
    rw [← map_hermitianCoordinates_gueMeasure n]
    exact HasLaw.comp ⟨(hermitianCoordinates n).continuous.aemeasurable, rfl⟩ hH
  · rintro ⟨hind, hdiag, hoff⟩
    have hcoord : ∀ ab : Fin n × Fin n,
        HasLaw (fun ω ↦ hermitianCoordinates n (H ω) ab)
          (gaussianReal 0 (if ab.1 = ab.2 then (1 / n : ℝ≥0) else (1 / (2 * n) : ℝ≥0))) P := by
      rintro ⟨i, j⟩
      rcases lt_trichotomy i j with hij | rfl | hji
      · simpa [hermitianCoordinates_apply_of_le n _ hij.le, hij.ne] using (hoff i j hij).1
      · simpa using hdiag i
      · simpa [hermitianCoordinates_apply_of_gt n _ hji, hji.ne'] using (hoff j i hji).2
    have hpi : HasLaw (fun ω ↦ hermitianCoordinates n (H ω))
        ((gueMeasure n).map (hermitianCoordinates n)) P := by
      rw [map_hermitianCoordinates_gueMeasure]
      exact hind.hasLaw_pi hcoord
    have hinv : HasLaw (hermitianCoordinates n).symm (gueMeasure n)
        ((gueMeasure n).map (hermitianCoordinates n)) :=
      ⟨(hermitianCoordinates n).symm.continuous.aemeasurable, by
        rw [Measure.map_map (hermitianCoordinates n).symm.continuous.measurable
          (hermitianCoordinates n).continuous.measurable]
        simp⟩
    simpa [Function.comp_def] using hinv.comp hpi

/-- **Invariant-density characterization of the GUE.** `H` has law `gueMeasure n` if and only if
`H` is `P`-almost-everywhere measurable and `P.map H` is `hermitianLebesgue n` weighted by
`guePDF n`. -/
theorem hasLaw_gueMeasure_iff_withDensity {n : ℕ}
    {H : Ω → selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)} :
    HasLaw H (gueMeasure n) P ↔
      AEMeasurable H P ∧ P.map H = (hermitianLebesgue n).withDensity (guePDF n) := by
  rw [gueMeasure_eq_withDensity_hermitianLebesgue n]
  exact ⟨fun h ↦ ⟨h.aemeasurable, h.map_eq⟩, fun ⟨hm, heq⟩ ↦ ⟨hm, heq⟩⟩

/-- **Equivalence of the entry and invariant-density characterizations of the GUE.** On a
probability space `(Ω, P)`, the independent-Gaussian real and imaginary coordinate conditions on a
complex Hermitian random matrix `H` hold if and only if `H` is `P`-almost-everywhere measurable with
law `(hermitianLebesgue n).withDensity (guePDF n)`. -/
theorem gue_iIndepFun_iff_withDensity [IsProbabilityMeasure P] {n : ℕ}
    {H : Ω → selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)} :
    (iIndepFun (fun (ab : Fin n × Fin n) ω ↦ hermitianCoordinates n (H ω) ab) P ∧
      (∀ i : Fin n,
        HasLaw (fun ω ↦ ((H ω : Matrix (Fin n) (Fin n) ℂ) i i).re)
          (gaussianReal 0 (1 / n)) P) ∧
      (∀ i j : Fin n, i < j →
        HasLaw (fun ω ↦ ((H ω : Matrix (Fin n) (Fin n) ℂ) i j).re)
          (gaussianReal 0 (1 / (2 * n))) P ∧
        HasLaw (fun ω ↦ ((H ω : Matrix (Fin n) (Fin n) ℂ) i j).im)
          (gaussianReal 0 (1 / (2 * n))) P)) ↔
      (AEMeasurable H P ∧ P.map H = (hermitianLebesgue n).withDensity (guePDF n)) := by
  rw [← hasLaw_gueMeasure_iff_iIndepFun, hasLaw_gueMeasure_iff_withDensity]

end Characterizations

end TauCeti.Probability
