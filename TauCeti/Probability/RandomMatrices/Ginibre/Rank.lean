/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.RandomMatrices.Ginibre.Density
public import TauCeti.Analysis.Matrix.SpectralMeasure.Basic
public import TauCeti.MeasureTheory.Measure.Matrix

/-!
# Exact rank of complex Gaussian Gram matrices

A complex Ginibre matrix is absolutely continuous with respect to product planar volume.
Consequently an `m × n` Ginibre matrix and its Gram matrix both have rank `min m n` almost
surely. The Gram matrix is positive definite exactly in the regime `m ≤ n`; when `n < m` its
spectral measure has the deterministic atom `(m - n) / m` at zero. These statements include
zero sample size and distinguish the number of samples from the matrix dimension.

The argument uses the almost-sure maximal rank theorem for absolutely continuous matrix laws,
followed by the deterministic equality `rank (X * Xᴴ) = rank X`.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*,
  Cambridge University Press, 2010, §2.5.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Matrix
open scoped ComplexOrder ENNReal

namespace TauCeti.Probability

/-- A rectangular complex Ginibre matrix has the largest rank its dimensions permit. -/
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
theorem ae_posDef_iff_gaussianGramComplex (m n : ℕ) :
    ∀ᵐ A ∂gaussianGramComplex m n, A.PosDef ↔ m ≤ n := by
  filter_upwards [ae_rank_eq_min_gaussianGramComplex m n, ae_posSemidef_gaussianGramComplex m n]
    with A hr hA
  rw [hA.posDef_iff_isUnit, ← Matrix.mulVec_surjective_iff_isUnit,
    Matrix.mulVec_surjective_iff_rank_eq_card, Fintype.card_fin, hr]
  exact min_eq_left_iff

/-- Below the full-rank threshold the complex Gaussian Gram determinant vanishes almost surely. -/
theorem ae_det_eq_zero_gaussianGramComplex {m n : ℕ} (hn : n < m) :
    ∀ᵐ A ∂gaussianGramComplex m n, A.det = 0 := by
  filter_upwards [ae_posDef_iff_gaussianGramComplex m n,
    ae_posSemidef_gaussianGramComplex m n] with A h hA
  simpa [hA.posDef_iff_det_ne_zero, hn.not_ge] using h

/-- The spectral measure of the Gram matrix of a complex Ginibre matrix has the exact
zero atom forced by its rectangular shape. The spectral probability measure requires `m > 0`. -/
theorem ae_spectralMeasure_gram_singleton_zero (m n : ℕ) [NeZero m] :
    ∀ᵐ X ∂ginibreComplex m n,
      ((X * Xᴴ).spectralMeasure (isHermitian_mul_conjTranspose_self X) : Measure ℝ) {0} =
        (m : ℝ≥0∞)⁻¹ * (m - n : ℕ) := by
  filter_upwards [ae_rank_eq_min_ginibreComplex m n] with X hX
  rw [Matrix.spectralMeasure_apply_singleton_zero, Fintype.card_fin,
    Matrix.rank_self_mul_conjTranspose, hX, tsub_min]

end TauCeti.Probability

namespace ProbabilityTheory

open TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {m n : ℕ}

/-- A complex Ginibre random matrix has maximal rank, for any realization of its joint law. -/
theorem HasLaw.ae_rank_eq_min_ginibreComplex {X : Ω → Matrix (Fin m) (Fin n) ℂ}
    (hX : HasLaw X (ginibreComplex m n) P) :
    ∀ᵐ ω ∂P, (X ω).rank = min m n := by
  have h := TauCeti.Probability.ae_rank_eq_min_ginibreComplex m n
  rw [← hX.map_eq] at h
  exact ae_of_ae_map hX.aemeasurable h

/-- A random matrix with the complex Gaussian Gram law has deterministic rank `min m n`. -/
theorem HasLaw.ae_rank_eq_min_gaussianGramComplex {A : Ω → Matrix (Fin m) (Fin m) ℂ}
    (hA : HasLaw A (gaussianGramComplex m n) P) :
    ∀ᵐ ω ∂P, (A ω).rank = min m n := by
  have h := TauCeti.Probability.ae_rank_eq_min_gaussianGramComplex m n
  rw [← hA.map_eq] at h
  exact ae_of_ae_map hA.aemeasurable h

end ProbabilityTheory
