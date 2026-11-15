/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.RandomMatrices.Ginibre.Basic
public import TauCeti.Probability.Distributions.Gaussian.ProperComplex.Product
public import TauCeti.MeasureTheory.Measure.Lebesgue.Matrix

/-!
# The complex Ginibre density and independent-entry characterization

The complex Ginibre law has planar product density
`π^(-m*n) exp(-∑ i j, ‖X i j‖²)`. The dimensions here are arbitrary natural numbers: when
one dimension is zero, the matrix space has one point and the density is one.

Vectorization identifies the law with the identity-covariance proper complex Gaussian.
The independent-entry characterization applies on arbitrary sample spaces and lets statements
about the canonical matrix law transfer to random matrices specified by their entries.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*,
  Cambridge University Press, 2010, §2.5.
* T. Tao, *Topics in Random Matrix Theory*, AMS, 2012, §2.6.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Matrix
open scoped ComplexOrder ENNReal

namespace TauCeti.Probability

/-- The complex Ginibre density relative to product planar Lebesgue measure on the entries. -/
def ginibreComplexPDF (m n : ℕ) (X : Matrix (Fin m) (Fin n) ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-(∑ i, ∑ j, ‖X i j‖ ^ 2)) / Real.pi ^ (m * n))

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
  fun_prop

/-- Column-stacking a complex Ginibre matrix gives independent standard proper complex
Gaussian coordinates. -/
theorem map_vec_ginibreComplex (m n : ℕ) :
    (ginibreComplex m n).map Matrix.vec =
      properComplexGaussianMeasure (0 : Fin n × Fin m → ℂ) 1 := by
  rw [ginibreComplex_def, Measure.map_map measurable_matrix_vec (by fun_prop),
    properComplexGaussianMeasure_one_eq_pi]
  exact (measurePreserving_piCongrLeft
    (fun _ : Fin m × Fin n ↦ properComplexGaussianScalar) (Equiv.prodComm _ _)).symm.map_eq

/-- Reshaping the identity-covariance complex Gaussian vector gives the complex Ginibre law. -/
theorem ginibreComplex_eq_map_properComplexGaussianMeasure (m n : ℕ) :
    ginibreComplex m n =
      (properComplexGaussianMeasure (0 : Fin m × Fin n → ℂ) 1).map
        (fun z ↦ Matrix.of fun i j ↦ z (i, j)) := by
  rw [properComplexGaussianMeasure_one_eq_pi, ginibreComplex_def]

/-- The complex Ginibre law has density `π^(-m*n) exp(-∑ i j, ‖X i j‖²)`. -/
theorem ginibreComplex_eq_withDensity (m n : ℕ) :
    ginibreComplex m n = volume.withDensity (ginibreComplexPDF m n) := by
  let e := (MeasurableEquiv.curry (Fin m) (Fin n) ℂ).trans
    (Matrix.ofMeasurableEquiv (Fin m) (Fin n) ℂ)
  have hc := (measurePreserving_piCurry
    (fun _ : Fin m ↦ fun _ : Fin n ↦ (volume : Measure ℂ))).comp
      ((measurePreserving_piCongrLeft
        (fun _ : Fin m × Fin n ↦ (volume : Measure ℂ))
        (Equiv.sigmaEquivProd (Fin m) (Fin n))).symm)
  have he : MeasurePreserving e volume volume := by
    convert (Matrix.volume_preserving_ofMeasurableEquiv (Fin m) (Fin n) ℂ).comp hc using 1
    ext z i j
    rfl
  rw [ginibreComplex_eq_map_properComplexGaussianMeasure,
    properComplexGaussianMeasure_eq_withDensity _ Matrix.PosDef.one]
  have h := e.map_withDensity volume (properComplexGaussianPDF (0 : Fin m × Fin n → ℂ) 1)
  rw [he.map_eq] at h
  convert h using 1
  · rfl
  · congr 1
    funext X
    simp [properComplexGaussianPDF_one, ginibreComplexPDF, e,
      MeasurableEquiv.curry, Fintype.sum_prod_type]

/-- The complex Ginibre density has total integral one, including empty matrix spaces. -/
theorem lintegral_ginibreComplexPDF (m n : ℕ) :
    ∫⁻ X, ginibreComplexPDF m n X = 1 := by
  rw [← setLIntegral_univ, ← withDensity_apply _ MeasurableSet.univ,
    ← ginibreComplex_eq_withDensity]
  exact measure_univ

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

/-- A matrix has the complex Ginibre law exactly when all its entries are independent
standard proper complex Gaussians. No prior measurability of the whole matrix is required. -/
theorem hasLaw_ginibreComplex_iff :
    HasLaw X (ginibreComplex m n) P ↔
      iIndepFun (fun p : Fin m × Fin n ↦ fun ω ↦ X ω p.1 p.2) P ∧
        ∀ i j, HasLaw (fun ω ↦ X ω i j) properComplexGaussianScalar P := by
  constructor
  · intro hX
    have : IsProbabilityMeasure P := hX.isProbabilityMeasure_iff.mpr inferInstance
    refine ⟨?_, fun i j ↦ ?_⟩
    · have hentry := fun i j ↦ (HasLaw.mk (Matrix.measurable_apply.aemeasurable)
        (map_apply_ginibreComplex m n i j)).comp hX
      apply (iIndepFun_iff_hasLaw_pi_pi
        (fun (p : Fin m × Fin n) ↦ hentry p.1 p.2)).mpr
      have hread : HasLaw
          (fun A : Matrix (Fin m) (Fin n) ℂ ↦ fun p : Fin m × Fin n ↦ A p.1 p.2)
          (Measure.pi fun _ : Fin m × Fin n ↦ properComplexGaussianScalar)
          (ginibreComplex m n) := by
        refine ⟨(Measurable.of_eval (fun _ ↦ Matrix.measurable_apply)).aemeasurable, ?_⟩
        rw [ginibreComplex_def, Measure.map_map (by fun_prop) (by fun_prop)]
        exact Measure.map_id
      exact hread.comp hX
    · exact (HasLaw.mk (Matrix.measurable_apply.aemeasurable)
        (map_apply_ginibreComplex m n i j)).comp hX
  · rintro ⟨hind, hlaw⟩
    have hflat := hind.hasLaw_pi (fun (p : Fin m × Fin n) ↦ hlaw p.1 p.2)
    exact (HasLaw.mk
      (((Matrix.ofMeasurableEquiv (Fin m) (Fin n) ℂ).measurable.comp measurable_curry).aemeasurable)
      (ginibreComplex_def m n).symm).comp hflat

/-- A complex Ginibre random matrix has the explicit matrix density. -/
theorem HasLaw.hasPDF_ginibreComplex (hX : HasLaw X (ginibreComplex m n) P) : HasPDF X P :=
  TauCeti.Probability.hasPDF_of_hasLaw_withDensity
    (measurable_ginibreComplexPDF m n).aemeasurable
    (by rwa [← ginibreComplex_eq_withDensity])

end ProbabilityTheory
