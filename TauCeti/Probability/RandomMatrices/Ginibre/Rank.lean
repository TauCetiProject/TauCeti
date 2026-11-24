/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.RandomMatrices.Ginibre.Density
public import TauCeti.Analysis.Matrix.SpectralMeasure.Basic
public import TauCeti.MeasureTheory.Measure.Matrix
public import TauCeti.Probability.HasLaw

/-!
# Exact rank of complex Gaussian Gram matrices

A complex Ginibre matrix is absolutely continuous with respect to product planar volume.
Consequently an `m × n` Ginibre matrix and its Gram matrix both have rank `min m n` almost
surely. The Gram matrix is almost surely positive definite exactly in the regime `m ≤ n`;
when `n < m` and `m > 0`, its spectral measure almost surely has the deterministic atom
`(m - n) / m` at zero. These statements include
zero sample size and distinguish the number of samples from the matrix dimension.

The argument uses the almost-sure maximal rank theorem for absolutely continuous matrix laws,
followed by the deterministic equality `rank (X * Xᴴ) = rank X`.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*,
  Cambridge University Press, 2010, §4.1.1.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Matrix
open scoped ComplexOrder ENNReal

namespace TauCeti.Probability

/-- A rectangular complex Ginibre matrix almost surely has the largest rank its dimensions
permit. -/
theorem ae_rank_eq_min_ginibreComplex (m n : ℕ) :
    ∀ᵐ X ∂ginibreComplex m n, X.rank = min m n := by
  simpa only [Fintype.card_fin] using
    Measure.ae_rank_eq_min_matrix (ginibreComplex m n) (ginibreComplex_absolutelyContinuous m n)

/-- A standard complex Gaussian Gram matrix has rank `min m n` almost surely. -/
theorem ae_rank_eq_min_gaussianGramComplex (m n : ℕ) :
    ∀ᵐ A ∂gaussianGramComplex m n, A.rank = min m n := by
  rw [gaussianGramComplex_def, ae_map_iff (by fun_prop)
    (Matrix.measurableSet_setOfPred_rank_eq _)]
  filter_upwards [ae_rank_eq_min_ginibreComplex m n] with X hX
  rwa [Matrix.rank_self_mul_conjTranspose]

/-- Positive definiteness of a standard complex Gaussian Gram matrix holds almost surely
exactly when there are at least as many samples as rows. -/
theorem ae_posDef_iff_le_gaussianGramComplex (m n : ℕ) :
    ∀ᵐ A ∂gaussianGramComplex m n, A.PosDef ↔ m ≤ n := by
  filter_upwards [ae_rank_eq_min_gaussianGramComplex m n, ae_posSemidef_gaussianGramComplex m n]
    with A hr hA
  rw [hA.posDef_iff_isUnit, ← Matrix.mulVec_surjective_iff_isUnit,
    Matrix.mulVec_surjective_iff_rank_eq_card, Fintype.card_fin, hr]
  exact min_eq_left_iff

/-- A complex Gaussian Gram determinant almost surely vanishes exactly below the full-rank
threshold, including zero dimensions and zero samples. -/
theorem ae_det_eq_zero_iff_lt_gaussianGramComplex (m n : ℕ) :
    ∀ᵐ A ∂gaussianGramComplex m n, A.det = 0 ↔ n < m := by
  filter_upwards [ae_posDef_iff_le_gaussianGramComplex m n,
    ae_posSemidef_gaussianGramComplex m n] with A h hA
  simpa only [hA.posDef_iff_det_ne_zero, ne_eq, not_not, not_le] using not_congr h

/-- The spectral measure of a complex Gaussian Gram matrix almost surely has the zero atom
forced by its dimension `m > 0` and sample size `n`. The witness also records that the matrix
is Hermitian. -/
theorem ae_spectralMeasure_apply_singleton_zero_gaussianGramComplex (m n : ℕ) [NeZero m] :
    ∀ᵐ A ∂gaussianGramComplex m n, ∃ hA : A.IsHermitian,
      (A.spectralMeasure hA : Measure ℝ) {0} = (m : ℝ≥0∞)⁻¹ * (m - n : ℕ) := by
  filter_upwards [ae_rank_eq_min_gaussianGramComplex m n,
    ae_posSemidef_gaussianGramComplex m n] with A hr hA
  refine ⟨hA.isHermitian, ?_⟩
  rw [Matrix.spectralMeasure_apply_singleton_zero, Fintype.card_fin, hr, tsub_min]

/-- The spectral measure of the Gram matrix of a complex Ginibre matrix has the exact
zero atom forced by its rectangular shape almost surely. The spectral probability measure
requires `m > 0`. -/
theorem ae_spectralMeasure_mul_conjTranspose_self_apply_singleton_zero_ginibreComplex
    (m n : ℕ) [NeZero m] :
    ∀ᵐ X ∂ginibreComplex m n,
      ((X * Xᴴ).spectralMeasure (isHermitian_mul_conjTranspose_self X) : Measure ℝ) {0} =
        (m : ℝ≥0∞)⁻¹ * (m - n : ℕ) := by
  filter_upwards [ae_rank_eq_min_ginibreComplex m n] with X hX
  rw [Matrix.spectralMeasure_apply_singleton_zero, Fintype.card_fin,
    Matrix.rank_self_mul_conjTranspose, hX, tsub_min]

end TauCeti.Probability

namespace ProbabilityTheory

open TauCeti TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {m n : ℕ}

/-- A complex Ginibre random matrix has maximal rank almost surely, on any probability space. -/
theorem HasLaw.ae_rank_eq_min_ginibreComplex {X : Ω → Matrix (Fin m) (Fin n) ℂ}
    (hX : HasLaw X (ginibreComplex m n) P) :
    ∀ᵐ ω ∂P, (X ω).rank = min m n :=
  hX.ae (TauCeti.Probability.ae_rank_eq_min_ginibreComplex m n)

/-- A random matrix with the complex Gaussian Gram law has rank `min m n` almost surely. -/
theorem HasLaw.ae_rank_eq_min_gaussianGramComplex {A : Ω → Matrix (Fin m) (Fin m) ℂ}
    (hA : HasLaw A (gaussianGramComplex m n) P) :
    ∀ᵐ ω ∂P, (A ω).rank = min m n :=
  hA.ae (TauCeti.Probability.ae_rank_eq_min_gaussianGramComplex m n)

/-- A complex Gaussian Gram random matrix is positive definite almost surely exactly when
there are at least as many samples as rows. -/
theorem HasLaw.ae_posDef_iff_le_gaussianGramComplex {A : Ω → Matrix (Fin m) (Fin m) ℂ}
    (hA : HasLaw A (gaussianGramComplex m n) P) :
    ∀ᵐ ω ∂P, (A ω).PosDef ↔ m ≤ n :=
  hA.ae (TauCeti.Probability.ae_posDef_iff_le_gaussianGramComplex m n)

/-- A complex Gaussian Gram random determinant almost surely vanishes exactly when the
sample size is smaller than the row dimension. -/
theorem HasLaw.ae_det_eq_zero_iff_lt_gaussianGramComplex {A : Ω → Matrix (Fin m) (Fin m) ℂ}
    (hA : HasLaw A (gaussianGramComplex m n) P) :
    ∀ᵐ ω ∂P, (A ω).det = 0 ↔ n < m :=
  hA.ae (TauCeti.Probability.ae_det_eq_zero_iff_lt_gaussianGramComplex m n)

/-- A complex Gaussian Gram random matrix almost surely has the prescribed spectral atom at
zero, for dimension `m > 0` and sample size `n`, on any probability space. -/
theorem HasLaw.ae_spectralMeasure_apply_singleton_zero_gaussianGramComplex [NeZero m]
    {A : Ω → Matrix (Fin m) (Fin m) ℂ} (hA : HasLaw A (gaussianGramComplex m n) P) :
    ∀ᵐ ω ∂P, ∃ h : (A ω).IsHermitian,
      ((A ω).spectralMeasure h : Measure ℝ) {0} = (m : ℝ≥0∞)⁻¹ * (m - n : ℕ) :=
  hA.ae (TauCeti.Probability.ae_spectralMeasure_apply_singleton_zero_gaussianGramComplex m n)

/-- The Gram matrix of a complex Ginibre random matrix almost surely has the exact zero
spectral atom determined by its shape, with positive row dimension. -/
theorem HasLaw.ae_spectralMeasure_mul_conjTranspose_self_apply_singleton_zero_ginibreComplex
    [NeZero m] {X : Ω → Matrix (Fin m) (Fin n) ℂ}
    (hX : HasLaw X (ginibreComplex m n) P) :
    ∀ᵐ ω ∂P,
      ((X ω * (X ω)ᴴ).spectralMeasure (isHermitian_mul_conjTranspose_self (X ω)) :
        Measure ℝ) {0} = (m : ℝ≥0∞)⁻¹ * (m - n : ℕ) :=
  hX.ae <|
    Probability.ae_spectralMeasure_mul_conjTranspose_self_apply_singleton_zero_ginibreComplex m n

end ProbabilityTheory
