/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.RandomMatrices.Ginibre.Basic
public import TauCeti.MeasureTheory.Measure.Lebesgue.Matrix

/-!
# The complex Ginibre density

The complex Ginibre law has planar product density
`π^(-m*n) exp(-∑ i j, ‖X i j‖²)`. The dimensions here are arbitrary natural numbers: when
one dimension is zero, the matrix space has one point and the density is one.

The vectorization bridges in `Ginibre.Basic` identify the law with the centered
identity-covariance proper complex Gaussian. Here this gives the explicit density and its
normalization, absolute continuity for the rank results, and `HasPDF` and `pdf` identities for
random matrices with the prescribed law.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*,
  Cambridge University Press, 2010, §4.1.1.
* T. Tao, *Topics in Random Matrix Theory*, AMS, 2012, §2.6.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Matrix
open scoped ComplexOrder ENNReal

namespace TauCeti.Probability

/-- The real-valued complex Ginibre density relative to product planar Lebesgue measure. -/
def ginibreComplexPDFReal (m n : ℕ) (X : Matrix (Fin m) (Fin n) ℂ) : ℝ :=
  Real.exp (-(∑ i, ∑ j, ‖X i j‖ ^ 2)) / Real.pi ^ (m * n)

/-- The entrywise formula for the real-valued complex Ginibre density. -/
theorem ginibreComplexPDFReal_def (m n : ℕ) (X : Matrix (Fin m) (Fin n) ℂ) :
    ginibreComplexPDFReal m n X =
      Real.exp (-(∑ i, ∑ j, ‖X i j‖ ^ 2)) / Real.pi ^ (m * n) := (rfl)

/-- The complex Ginibre density relative to product planar Lebesgue measure on the entries. -/
def ginibreComplexPDF (m n : ℕ) (X : Matrix (Fin m) (Fin n) ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (ginibreComplexPDFReal m n X)

/-- The extended density is the nonnegative lift of the real-valued density. -/
theorem ginibreComplexPDF_eq_ofReal (m n : ℕ) (X : Matrix (Fin m) (Fin n) ℂ) :
    ginibreComplexPDF m n X = ENNReal.ofReal (ginibreComplexPDFReal m n X) := (rfl)

/-- The real-valued density is one when the row dimension is zero. -/
@[simp]
theorem ginibreComplexPDFReal_zero_left (n : ℕ) (X : Matrix (Fin 0) (Fin n) ℂ) :
    ginibreComplexPDFReal 0 n X = 1 := by
  simp [ginibreComplexPDFReal_def]

/-- The real-valued density is one when the column dimension is zero. -/
@[simp]
theorem ginibreComplexPDFReal_zero_right (m : ℕ) (X : Matrix (Fin m) (Fin 0) ℂ) :
    ginibreComplexPDFReal m 0 X = 1 := by
  simp [ginibreComplexPDFReal_def]

/-- The extended density is one when the row dimension is zero. -/
@[simp]
theorem ginibreComplexPDF_zero_left (n : ℕ) (X : Matrix (Fin 0) (Fin n) ℂ) :
    ginibreComplexPDF 0 n X = 1 := by
  simp [ginibreComplexPDF_eq_ofReal]

/-- The extended density is one when the column dimension is zero. -/
@[simp]
theorem ginibreComplexPDF_zero_right (m : ℕ) (X : Matrix (Fin m) (Fin 0) ℂ) :
    ginibreComplexPDF m 0 X = 1 := by
  simp [ginibreComplexPDF_eq_ofReal]

/-- The real-valued complex Ginibre density is strictly positive. -/
theorem ginibreComplexPDFReal_pos (m n : ℕ) (X : Matrix (Fin m) (Fin n) ℂ) :
    0 < ginibreComplexPDFReal m n X := by
  rw [ginibreComplexPDFReal_def]
  positivity

/-- Applying `ENNReal.toReal` to the extended density recovers the real-valued density. -/
@[simp]
theorem toReal_ginibreComplexPDF (m n : ℕ) (X : Matrix (Fin m) (Fin n) ℂ) :
    (ginibreComplexPDF m n X).toReal = ginibreComplexPDFReal m n X := by
  rw [ginibreComplexPDF_eq_ofReal, ENNReal.toReal_ofReal (ginibreComplexPDFReal_pos m n X).le]

/-- The real-valued Ginibre density is measurable. -/
@[fun_prop]
theorem measurable_ginibreComplexPDFReal (m n : ℕ) :
    Measurable (ginibreComplexPDFReal m n) := by
  unfold ginibreComplexPDFReal
  fun_prop

/-- The real-valued Ginibre density depends only on the real trace of `X * Xᴴ`. -/
theorem ginibreComplexPDFReal_eq_exp_neg_trace (m n : ℕ) (X : Matrix (Fin m) (Fin n) ℂ) :
    ginibreComplexPDFReal m n X =
      Real.exp (-(X * Xᴴ).trace.re) / Real.pi ^ (m * n) := by
  rw [ginibreComplexPDFReal_def]
  have h := Matrix.re_trace_mul_conjTranspose_self X
  simp only [RCLike.re_to_complex] at h
  rw [h]

/-- The extended Ginibre density depends only on the real trace of `X * Xᴴ`. -/
theorem ginibreComplexPDF_eq_exp_neg_trace (m n : ℕ) (X : Matrix (Fin m) (Fin n) ℂ) :
    ginibreComplexPDF m n X =
      ENNReal.ofReal (Real.exp (-(X * Xᴴ).trace.re) / Real.pi ^ (m * n)) := by
  rw [ginibreComplexPDF_eq_ofReal, ginibreComplexPDFReal_eq_exp_neg_trace]

/-- The entrywise formula for the complex Ginibre density. -/
theorem ginibreComplexPDF_def (m n : ℕ) (X : Matrix (Fin m) (Fin n) ℂ) :
    ginibreComplexPDF m n X =
      ENNReal.ofReal (Real.exp (-(∑ i, ∑ j, ‖X i j‖ ^ 2)) / Real.pi ^ (m * n)) := (rfl)

/-- The complex Ginibre density is strictly positive at every matrix. -/
theorem ginibreComplexPDF_pos (m n : ℕ) (X : Matrix (Fin m) (Fin n) ℂ) :
    0 < ginibreComplexPDF m n X := by
  rw [ginibreComplexPDF_def, ENNReal.ofReal_pos]
  positivity

/-- The complex Ginibre density is finite at every matrix. -/
@[simp]
theorem ginibreComplexPDF_ne_top (m n : ℕ) (X : Matrix (Fin m) (Fin n) ℂ) :
    ginibreComplexPDF m n X ≠ ⊤ := by
  rw [ginibreComplexPDF_def]
  exact ENNReal.ofReal_ne_top

/-- The Ginibre density is measurable. -/
@[fun_prop]
theorem measurable_ginibreComplexPDF (m n : ℕ) : Measurable (ginibreComplexPDF m n) := by
  unfold ginibreComplexPDF
  exact (measurable_ginibreComplexPDFReal m n).ennreal_ofReal

/-- The complex Ginibre law has density `π^(-m*n) exp(-∑ i j, ‖X i j‖²)`. -/
theorem ginibreComplex_eq_withDensity (m n : ℕ) :
    ginibreComplex m n = volume.withDensity (ginibreComplexPDF m n) := by
  let e := (MeasurableEquiv.curry (Fin m) (Fin n) ℂ).trans
    (Matrix.ofMeasurableEquiv (Fin m) (Fin n) ℂ)
  have he : MeasurePreserving e volume volume :=
    (Matrix.volume_preserving_ofMeasurableEquiv (Fin m) (Fin n) ℂ).comp
      (TauCeti.measurePreserving_curry (fun _ : Fin m ↦ fun _ : Fin n ↦ (volume : Measure ℂ)))
  have he_fun : (fun z : Fin m × Fin n → ℂ ↦ Matrix.of fun i j ↦ z (i, j)) = e := by
    simp only [e, MeasurableEquiv.coe_trans, Matrix.coe_ofMeasurableEquiv,
      MeasurableEquiv.coe_curry, Function.comp_def]
    funext z
    congr 1
  rw [ginibreComplex_eq_map_properComplexGaussianMeasure,
    properComplexGaussianMeasure_eq_withDensity _ Matrix.PosDef.one, he_fun,
    e.map_withDensity, he.map_eq]
  congr 1
  funext X
  simp [properComplexGaussianPDF_one, ginibreComplexPDF_def, e,
    MeasurableEquiv.coe_curry_symm, Fintype.sum_prod_type]

/-- The complex Ginibre density has total integral one, including when one dimension is zero. -/
theorem lintegral_ginibreComplexPDF_eq_one (m n : ℕ) :
    ∫⁻ X, ginibreComplexPDF m n X = 1 := by
  rw [← setLIntegral_univ, ← withDensity_apply _ MeasurableSet.univ,
    ← ginibreComplex_eq_withDensity]
  exact measure_univ

/-- The real-valued Ginibre density has integral one, including when one dimension is zero. -/
theorem integral_ginibreComplexPDFReal_eq_one (m n : ℕ) :
    ∫ X, ginibreComplexPDFReal m n X = 1 := by
  simp_rw [← toReal_ginibreComplexPDF]
  rw [integral_toReal (measurable_ginibreComplexPDF m n).aemeasurable
      (ae_of_all _ fun X ↦ (ginibreComplexPDF_ne_top m n X).lt_top),
    lintegral_ginibreComplexPDF_eq_one, ENNReal.toReal_one]

/-- The real-valued Ginibre density is integrable. -/
theorem integrable_ginibreComplexPDFReal (m n : ℕ) :
    Integrable (ginibreComplexPDFReal m n) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_ginibreComplexPDFReal_eq_one]
  exact one_ne_zero

/-- The Ginibre law is absolutely continuous with respect to product planar volume. -/
theorem ginibreComplex_absolutelyContinuous (m n : ℕ) : ginibreComplex m n ≪ volume := by
  rw [ginibreComplex_eq_withDensity]
  exact withDensity_absolutelyContinuous _ _

/-- The Radon–Nikodym derivative of the complex Ginibre law is its matrix density. -/
theorem rnDeriv_ginibreComplex (m n : ℕ) :
    (ginibreComplex m n).rnDeriv volume =ᵐ[volume] ginibreComplexPDF m n := by
  rw [ginibreComplex_eq_withDensity]
  exact Measure.rnDeriv_withDensity _ (measurable_ginibreComplexPDF m n)

end TauCeti.Probability

namespace ProbabilityTheory

open TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {m n : ℕ}
  {X : Ω → Matrix (Fin m) (Fin n) ℂ}

/-- A complex Ginibre random matrix has a density with respect to matrix volume. -/
theorem HasLaw.hasPDF_ginibreComplex (hX : HasLaw X (ginibreComplex m n) P) : HasPDF X P :=
  TauCeti.Probability.hasPDF_of_hasLaw_withDensity
    (measurable_ginibreComplexPDF m n).aemeasurable
    (by rwa [← ginibreComplex_eq_withDensity])

/-- The density of a complex Ginibre random matrix is its explicit matrix density. -/
theorem HasLaw.pdf_eq_ginibreComplexPDF (hX : HasLaw X (ginibreComplex m n) P) :
    pdf X P =ᵐ[volume] ginibreComplexPDF m n :=
  TauCeti.Probability.pdf_eq_of_hasLaw_withDensity
    (measurable_ginibreComplexPDF m n).aemeasurable
    (by rwa [← ginibreComplex_eq_withDensity])

end ProbabilityTheory
