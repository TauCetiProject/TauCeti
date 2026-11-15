/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.HermitianMatrix.Lebesgue
public import TauCeti.MeasureTheory.Measure.SymmetricMatrix.Orthogonal
public import TauCeti.Probability.RandomMatrices.GaussianEnsemble.Basic
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.HasLaw

/-!
# Probability laws, conjugation invariance, and coordinate marginals of the GOE and GUE

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

From this identification we deduce orthogonal conjugation invariance of `goeMeasure n`, unitary
conjugation invariance of `gueMeasure n`, and the Gaussian coordinate marginals and joint
independence of the independent real parameters of both ensembles. Exact trace densities and the
equivalence between the independent-entry and invariant-density characterizations are developed in
`TauCeti.Probability.RandomMatrices.GaussianEnsemble.Density`.

## Main definitions

* `TauCeti.Probability.gaussianEnsembleReal` and `TauCeti.Probability.gaussianEnsembleHermitian`:
  the `β = 1` and `β = 2` ensemble maps into the real symmetric and complex Hermitian subspaces.
* `TauCeti.Probability.goeMeasure` and `TauCeti.Probability.gueMeasure`: the GOE and GUE laws on
  the real symmetric and complex Hermitian subspaces.

## Main results

* `TauCeti.Probability.goeMeasure_eq_map_stdGaussian` and
  `TauCeti.Probability.gueMeasure_eq_map_stdGaussian`: representation as scaled `stdGaussian`
  measures.
* `TauCeti.Probability.map_symmetricConj_goeMeasure` and
  `TauCeti.Probability.map_hermitianConj_gueMeasure`: orthogonal and unitary conjugation
  invariance.
* `TauCeti.Probability.map_symmetricCoordinates_goeMeasure`,
  `TauCeti.Probability.iIndepFun_symmetricCoordinates_goeMeasure`,
  `TauCeti.Probability.map_hermitianCoordinates_gueMeasure`, and
  `TauCeti.Probability.iIndepFun_hermitianCoordinates_gueMeasure`: product-Gaussian coordinate laws
  and joint independence.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), §2.5, p. 52.
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
theorem continuous_gaussianEnsembleReal (n : ℕ) : Continuous (gaussianEnsembleReal n) := by
  unfold gaussianEnsembleReal; fun_prop

@[fun_prop]
theorem measurable_gaussianEnsembleReal (n : ℕ) : Measurable (gaussianEnsembleReal n) :=
  (continuous_gaussianEnsembleReal n).measurable

@[simp]
theorem coe_gaussianEnsembleReal_apply_self {n : ℕ} (g : Fin n × Fin n → ℝ) (i : Fin n) :
    (gaussianEnsembleReal n g : Matrix (Fin n) (Fin n) ℝ) i i =
      (Real.sqrt n)⁻¹ * (Real.sqrt 2 * g (i, i)) := by
  rw [gaussianEnsembleReal, coe_symmetricCoordinates_symm_apply_of_le n _ le_rfl]; simp [mul_assoc]

@[simp]
theorem coe_gaussianEnsembleReal_apply_of_lt {n : ℕ} (g : Fin n × Fin n → ℝ) {i j : Fin n}
    (h : i < j) :
    (gaussianEnsembleReal n g : Matrix (Fin n) (Fin n) ℝ) i j =
      (Real.sqrt n)⁻¹ * g (i, j) := by
  rw [gaussianEnsembleReal, coe_symmetricCoordinates_symm_apply_of_le n _ h.le]; simp [h.ne]

@[simp]
theorem coe_gaussianEnsembleReal_apply_of_gt {n : ℕ} (g : Fin n × Fin n → ℝ) {i j : Fin n}
    (h : j < i) :
    (gaussianEnsembleReal n g : Matrix (Fin n) (Fin n) ℝ) i j =
      (Real.sqrt n)⁻¹ * g (j, i) := by
  rw [gaussianEnsembleReal, coe_symmetricCoordinates_symm_apply_of_ge n _ h.le]; simp [h.ne]

/-- Complexifying `TauCeti.Probability.gaussianEnsembleReal` gives `gaussianEnsemble 1 n g`: the
`β = 1` ensemble matrix is real. -/
@[simp]
theorem map_ofReal_coe_gaussianEnsembleReal (n : ℕ) (g : Fin n × Fin n → ℝ) :
    (gaussianEnsembleReal n g : Matrix (Fin n) (Fin n) ℝ).map Complex.ofReal =
      gaussianEnsemble 1 n g := by
  ext i j
  rcases lt_trichotomy i j with h | rfl | h
  · simp [Matrix.map_apply, h]
  · simp [Matrix.map_apply]
  · simp [Matrix.map_apply, h]

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
  · simp only [hd, ↓reduceIte]; ring
  · simp only [hd, ↓reduceIte]; field_simp [show Real.sqrt 2 ≠ 0 by positivity]

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
    simp only [h.ne, ↓reduceIte, div_eq_mul_inv, ← Complex.ofReal_inv, Complex.mul_re,
      Complex.add_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  · rw [hermitianCoordinates_apply_self, coe_gaussianEnsembleHermitian,
      gaussianEnsemble_apply_self_of_ne_one g (by decide)]
    simp [← Complex.ofReal_inv]
  · rw [hermitianCoordinates_apply_of_gt n _ h, coe_gaussianEnsembleHermitian,
      gaussianEnsemble_apply_of_lt_of_ne_one g (by decide) h]
    simp only [h.ne', ↓reduceIte, div_eq_mul_inv, ← Complex.ofReal_inv, Complex.mul_im,
      Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring

@[fun_prop]
theorem continuous_gaussianEnsembleHermitian (n : ℕ) :
    Continuous (gaussianEnsembleHermitian n) := by
  have heq : gaussianEnsembleHermitian n =
      (hermitianCoordinates n).symm ∘ fun g ab ↦
        (Real.sqrt n)⁻¹ * (if ab.1 = ab.2 then 1 else (Real.sqrt 2)⁻¹) * g ab :=
    funext fun g ↦ ((hermitianCoordinates n).symm_apply_eq.2
      (funext fun ab ↦ (hermitianCoordinates_gaussianEnsembleHermitian n g ab).symm)).symm
  rw [heq]; fun_prop

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
  rw [hermitianCoordinates_apply_of_le 2 _ (by decide), coe_gaussianEnsembleHermitian,
    ite_eq_right (by decide), Nat.cast_ofNat, ← mul_inv,
    Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)] at h
  linarith

theorem im_gaussianEnsemble_two_two_zero_one (g : Fin 2 × Fin 2 → ℝ) :
    (gaussianEnsemble 2 2 g 0 1).im = g (1, 0) / 2 := by
  have h := hermitianCoordinates_gaussianEnsembleHermitian 2 g (1, 0)
  rw [hermitianCoordinates_apply_of_gt 2 _ (by decide), coe_gaussianEnsembleHermitian,
    ite_eq_right (by decide), Nat.cast_ofNat, ← mul_inv,
    Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)] at h
  linarith

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
  congr 1; funext g
  exact gaussianEnsembleReal_eq_smul_sum_symmetricOrthonormalBasis n g

/-- The GUE law is the standard Gaussian measure on the complex Hermitian Frobenius inner-product
space rescaled by `(√n)⁻¹`. -/
theorem gueMeasure_eq_map_stdGaussian (n : ℕ) :
    gueMeasure n =
      (stdGaussian (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ))).map
        (fun A ↦ (Real.sqrt n)⁻¹ • A) := by
  rw [stdGaussian_eq_map_pi_orthonormalBasis (hermitianOrthonormalBasis n),
    Measure.map_map (by fun_prop) (by fun_prop), gueMeasure_def]
  congr 1; funext g
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
  rw [goeMeasure_eq_map_stdGaussian]; simp [Measure.map_const]

@[simp]
theorem gueMeasure_zero : gueMeasure 0 = Measure.dirac 0 := by
  rw [gueMeasure_eq_map_stdGaussian]; simp [Measure.map_const]

/-- Complexifying `goeMeasure n` gives the ambient `β = 1` law of `gaussianEnsemble 1 n`. -/
theorem map_ofReal_goeMeasure (n : ℕ) :
    (goeMeasure n).map
        (fun A : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ) ↦
          (A : Matrix (Fin n) (Fin n) ℝ).map Complex.ofReal) =
      (Measure.pi fun _ : Fin n × Fin n ↦ gaussianReal 0 1).map (gaussianEnsemble 1 n) := by
  have hm : Measurable fun A : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ) ↦
      (A : Matrix (Fin n) (Fin n) ℝ).map Complex.ofReal :=
    measurable_pi_iff.2 fun i ↦ measurable_pi_iff.2 fun j ↦
      Complex.continuous_ofReal.measurable.comp (selfAdjoint.measurable_coe_apply i j)
  rw [goeMeasure_def, Measure.map_map hm (measurable_gaussianEnsembleReal n)]
  congr 1; funext g
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

private theorem map_linearIsometryEquiv_map_smul_stdGaussian {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : E ≃ₗᵢ[ℝ] E) (c : ℝ) :
    ((stdGaussian E).map (fun A ↦ c • A)).map f = (stdGaussian E).map (fun A ↦ c • A) := by
  rw [Measure.map_map f.continuous.measurable (by fun_prop),
    show f ∘ (fun A : E ↦ c • A) = (fun A ↦ c • A) ∘ f from funext (map_smul f c),
    ← Measure.map_map (by fun_prop) f.continuous.measurable, stdGaussian_map f]

/-- **Orthogonal conjugation invariance of the GOE.** Conjugating by any orthogonal matrix
`O : Matrix.orthogonalGroup (Fin n) ℝ` preserves `goeMeasure n`. -/
@[simp]
theorem map_symmetricConj_goeMeasure {n : ℕ} (O : Matrix.orthogonalGroup (Fin n) ℝ) :
    (goeMeasure n).map (Matrix.UnitaryGroup.symmetricConj O) = goeMeasure n := by
  rw [goeMeasure_eq_map_stdGaussian]
  exact map_linearIsometryEquiv_map_smul_stdGaussian (Matrix.UnitaryGroup.symmetricConj O) _

theorem measurePreserving_symmetricConj_goeMeasure {n : ℕ}
    (O : Matrix.orthogonalGroup (Fin n) ℝ) :
    MeasurePreserving (Matrix.UnitaryGroup.symmetricConj O) (goeMeasure n) (goeMeasure n) :=
  ⟨(Matrix.UnitaryGroup.symmetricConj O).continuous.measurable, map_symmetricConj_goeMeasure O⟩

/-- **Unitary conjugation invariance of the GUE.** Conjugating by any unitary matrix
`U : Matrix.unitaryGroup (Fin n) ℂ` preserves `gueMeasure n`. -/
@[simp]
theorem map_hermitianConj_gueMeasure {n : ℕ} (U : Matrix.unitaryGroup (Fin n) ℂ) :
    (gueMeasure n).map (Matrix.UnitaryGroup.hermitianConj U) = gueMeasure n := by
  rw [gueMeasure_eq_map_stdGaussian]
  exact map_linearIsometryEquiv_map_smul_stdGaussian (Matrix.UnitaryGroup.hermitianConj U) _

theorem measurePreserving_hermitianConj_gueMeasure {n : ℕ}
    (U : Matrix.unitaryGroup (Fin n) ℂ) :
    MeasurePreserving (Matrix.UnitaryGroup.hermitianConj U) (gueMeasure n) (gueMeasure n) :=
  ⟨(Matrix.UnitaryGroup.hermitianConj U).continuous.measurable, map_hermitianConj_gueMeasure U⟩

/-! ### Coordinate pushforwards, entry laws, and joint independence -/

private theorem gaussianReal_map_scale {c : ℝ} {v : ℝ≥0} (hv : c ^ 2 = v) :
    (gaussianReal 0 1).map (fun x : ℝ ↦ c * x) = gaussianReal 0 v := by
  rw [gaussianReal_map_const_mul]
  simp only [mul_zero, mul_one]
  exact congrArg _ (NNReal.coe_injective hv)

private theorem gaussianReal_map_goeScale (n : ℕ) (ij : upperTriangle n) :
    (gaussianReal 0 1).map
      (fun x : ℝ ↦ (Real.sqrt n)⁻¹ * (if ij.1.1 = ij.1.2 then Real.sqrt 2 else 1) * x) =
      gaussianReal 0 (if ij.1.1 = ij.1.2 then (2 / n : ℝ≥0) else (1 / n : ℝ≥0)) := by
  refine gaussianReal_map_scale ?_
  rcases Nat.eq_zero_or_pos n with rfl | _
  · simp
  · by_cases hd : ij.1.1 = ij.1.2 <;>
      simp [hd, mul_pow, inv_pow, Real.sq_sqrt (Nat.cast_nonneg n), div_eq_inv_mul, mul_comm]

/-- Under `TauCeti.symmetricCoordinates`, `goeMeasure n` is the product of centred Gaussian laws
of variance `2 / n` on the diagonal and `1 / n` strictly above it. -/
theorem map_symmetricCoordinates_goeMeasure (n : ℕ) :
    (goeMeasure n).map (symmetricCoordinates n) =
      Measure.pi fun ij : upperTriangle n ↦
        gaussianReal 0 (if ij.1.1 = ij.1.2 then (2 / n : ℝ≥0) else (1 / n : ℝ≥0)) := by
  rw [goeMeasure_def, Measure.map_map (symmetricCoordinates n).continuous.measurable
    (measurable_gaussianEnsembleReal n),
    show symmetricCoordinates n ∘ gaussianEnsembleReal n =
      (fun (x : upperTriangle n → ℝ) ij ↦
        (Real.sqrt n)⁻¹ * (if ij.1.1 = ij.1.2 then Real.sqrt 2 else 1) * x ij) ∘
        fun (g : Fin n × Fin n → ℝ) ij ↦ g ij.1 from
      funext₂ (symmetricCoordinates_gaussianEnsembleReal n),
    ← Measure.map_map (by fun_prop) (by fun_prop),
    (measurePreserving_restrict_upperTriangle n).map_eq]
  exact (measurePreserving_pi _ _ fun ij ↦ ⟨by fun_prop, gaussianReal_map_goeScale n ij⟩).map_eq

/-- Each entry `(i, j)` of a GOE matrix has law `N(0, 2 / n)` on the diagonal and `N(0, 1 / n)`
off the diagonal. -/
theorem map_apply_goeMeasure {n : ℕ} (i j : Fin n) :
    (goeMeasure n).map
        (fun A : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ) ↦
          (A : Matrix (Fin n) (Fin n) ℝ) i j) =
      gaussianReal 0 (if i = j then (2 / n : ℝ≥0) else (1 / n : ℝ≥0)) := by
  have hle {a b : Fin n} (hab : a ≤ b) :
      (goeMeasure n).map (fun A : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ) ↦
        (A : Matrix (Fin n) (Fin n) ℝ) a b) =
        gaussianReal 0 (if a = b then (2 / n : ℝ≥0) else (1 / n : ℝ≥0)) := by
    have heval := (measurePreserving_eval (fun kl : upperTriangle n ↦
      gaussianReal 0 (if kl.1.1 = kl.1.2 then (2 / n : ℝ≥0) else (1 / n : ℝ≥0)))
      ⟨(a, b), hab⟩).map_eq
    rw [← map_symmetricCoordinates_goeMeasure n,
      Measure.map_map (measurable_pi_apply _) (symmetricCoordinates n).continuous.measurable]
      at heval
    simpa [Function.comp_def] using heval
  rcases le_total i j with hij | hji
  · exact hle hij
  · simpa [funext fun A : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ) ↦
      selfAdjoint.coe_apply_comm A i j, eq_comm] using hle hji

/-- In dimension `1`, the single entry of `goeMeasure 1` is `N(0, 2)`. -/
theorem map_symmetricFinOneEquiv_goeMeasure :
    (goeMeasure 1).map symmetricFinOneEquiv = gaussianReal 0 2 := by
  simpa [funext symmetricFinOneEquiv_apply] using map_apply_goeMeasure (0 : Fin 1) 0

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
  refine gaussianReal_map_scale ?_
  rcases Nat.eq_zero_or_pos n with rfl | _
  · simp
  · by_cases hd : ab.1 = ab.2 <;>
      simp [hd, mul_pow, inv_pow, Real.sq_sqrt (Nat.cast_nonneg n), mul_comm]

/-- Under `TauCeti.hermitianCoordinates`, `gueMeasure n` is the product of centred Gaussian laws
of variance `1 / n` on the diagonal and `1 / (2 * n)` on the strictly upper-triangular real and
imaginary coordinates. -/
theorem map_hermitianCoordinates_gueMeasure (n : ℕ) :
    (gueMeasure n).map (hermitianCoordinates n) =
      Measure.pi fun ab : Fin n × Fin n ↦
        gaussianReal 0 (if ab.1 = ab.2 then (1 / n : ℝ≥0) else (1 / (2 * n) : ℝ≥0)) := by
  rw [gueMeasure_def, Measure.map_map (hermitianCoordinates n).continuous.measurable
    (measurable_gaussianEnsembleHermitian n),
    show hermitianCoordinates n ∘ gaussianEnsembleHermitian n =
      fun (g : Fin n × Fin n → ℝ) ab ↦
        (Real.sqrt n)⁻¹ * (if ab.1 = ab.2 then 1 else (Real.sqrt 2)⁻¹) * g ab from
      funext₂ (hermitianCoordinates_gaussianEnsembleHermitian n)]
  exact (measurePreserving_pi _ _ fun ab ↦ ⟨by fun_prop, gaussianReal_map_gueScale n ab⟩).map_eq

/-- Each real coordinate `hermitianCoordinates n · ab` of `gueMeasure n` has law `N(0, 1 / n)` on
the diagonal (`ab.1 = ab.2`) and `N(0, 1 / (2 * n))` off the diagonal (`ab.1 ≠ ab.2`). -/
theorem map_hermitianCoordinates_apply_gueMeasure {n : ℕ} (ab : Fin n × Fin n) :
    (gueMeasure n).map (fun A ↦ hermitianCoordinates n A ab) =
      gaussianReal 0 (if ab.1 = ab.2 then (1 / n : ℝ≥0) else (1 / (2 * n) : ℝ≥0)) := by
  have heval := (measurePreserving_eval (fun cd : Fin n × Fin n ↦
    gaussianReal 0 (if cd.1 = cd.2 then (1 / n : ℝ≥0) else (1 / (2 * n) : ℝ≥0))) ab).map_eq
  rwa [← map_hermitianCoordinates_gueMeasure n,
    Measure.map_map (measurable_pi_apply _) (hermitianCoordinates n).continuous.measurable] at heval

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
  · simpa [funext fun A ↦ (hermitianCoordinates_apply_of_le n A hij.le).symm, h] using
      map_hermitianCoordinates_apply_gueMeasure (i, j)
  · have hfun : (fun A : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ) ↦
        ((A : Matrix (Fin n) (Fin n) ℂ) i j).re) = fun A ↦ hermitianCoordinates n A (j, i) :=
      funext fun A ↦ by
        rw [hermitianCoordinates_apply_of_le n A hji.le, ← selfAdjoint.coe_apply_conj A j i,
          Complex.conj_re]
    simpa [hfun, h.symm] using map_hermitianCoordinates_apply_gueMeasure (j, i)

/-- Strictly upper-triangular imaginary parts `(A i j).im` (`i < j`) of a GUE matrix have law
`N(0, 1 / (2 * n))`. -/
theorem map_im_apply_of_lt_gueMeasure {n : ℕ} {i j : Fin n} (h : i < j) :
    (gueMeasure n).map
        (fun A : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ) ↦
          ((A : Matrix (Fin n) (Fin n) ℂ) i j).im) =
      gaussianReal 0 (1 / (2 * n)) := by
  simpa [funext fun A ↦ (hermitianCoordinates_apply_of_gt n A h).symm, h.ne'] using
    map_hermitianCoordinates_apply_gueMeasure (j, i)

/-- In dimension `1`, the single entry of `gueMeasure 1` is `N(0, 1)`. -/
theorem map_hermitianFinOneEquiv_gueMeasure :
    (gueMeasure 1).map hermitianFinOneEquiv = gaussianReal 0 1 := by
  simpa [funext hermitianFinOneEquiv_apply] using map_re_apply_self_gueMeasure (0 : Fin 1)

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

end TauCeti.Probability
