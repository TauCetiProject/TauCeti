/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Probability.Distributions.LKJ.Basic

import TauCeti.Analysis.Matrix.PosSemidef.Basic
import TauCeti.MeasureTheory.Measure.WithDensity
import TauCeti.MeasureTheory.Measure.SymmetricMatrix.Integrable
import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-!
# Permutation and sign symmetry of the LKJ law

Relabelling the indices of a correlation matrix, `R ↦ P R Pᵀ` for a permutation matrix `P`, and
flipping the signs of some coordinate axes, `R ↦ D R D` for a diagonal matrix `D` with entries
`±1`, preserve both the reference measure `TauCeti.correlationLebesgue p` and the LKJ density
`det R ^ (η - 1) / lkjNormalizer p η`: such a congruence keeps the determinant and positive
definiteness. Hence every LKJ law is invariant under these two symmetry groups.

Sign symmetry determines the mean. Flipping the sign of axis `i` negates every off-diagonal entry
in row `i`, so these entries have mean zero, while the diagonal entries are almost surely one.
Every entry is bounded by one in absolute value, so the LKJ matrix is integrable, and for `η > 0`
its mean is the identity matrix.

## Main results

* `TauCeti.Probability.lkjPDF_symmetricCongruenceLinearMap`: congruence by a matrix of
  determinant `±1` preserves the LKJ density.
* `TauCeti.Probability.map_symmetricCongruenceLinearMap_permMatrix_lkjMeasure`: permutation
  invariance.
* `TauCeti.Probability.map_symmetricCongruenceLinearMap_diagonal_lkjMeasure`: sign invariance.
* `TauCeti.Probability.integrable_id_lkjMeasure` and `TauCeti.Probability.integral_id_lkjMeasure`:
  the LKJ matrix is integrable with mean the identity.

## References

* D. Lewandowski, D. Kurowicka, H. Joe, *Generating random correlation matrices based on vines
  and extended onion method*, J. Multivariate Anal. 100 (2009), 1989–2001.
-/

public section

noncomputable section

open MeasureTheory

open scoped Matrix

namespace TauCeti.Probability

variable {p : ℕ} {η : ℝ}

/-! ### Invariance of the density and of the law -/

/-- Congruence by a square matrix of determinant `±1` preserves the real-valued LKJ density: it
preserves both the determinant and positive definiteness. -/
theorem lkjPDFReal_symmetricCongruenceLinearMap {M : Matrix (Fin p) (Fin p) ℝ}
    (hM : M.det ^ 2 = 1) (R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
    lkjPDFReal p η (Matrix.symmetricCongruenceLinearMap M R) = lkjPDFReal p η R := by
  have hU : IsUnit M := (Matrix.isUnit_iff_isUnit_det M).2 <| Ne.isUnit fun h ↦ by simp [h] at hM
  have hT : Mᵀ = star M := by
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
  have hpos : (Matrix.symmetricCongruenceLinearMap M R : Matrix (Fin p) (Fin p) ℝ).PosDef ↔
      (R : Matrix (Fin p) (Fin p) ℝ).PosDef := by
    rw [Matrix.coe_symmetricCongruenceLinearMap_apply, hT]
    exact Matrix.IsUnit.posDef_star_right_conjugate_iff hU
  by_cases hR : (R : Matrix (Fin p) (Fin p) ℝ).PosDef
  · rw [lkjPDFReal_of_posDef p η (hpos.2 hR), lkjPDFReal_of_posDef p η hR,
      Matrix.det_coe_symmetricCongruenceLinearMap_apply, hM, one_mul]
  · rw [lkjPDFReal_of_not_posDef p η (hpos.not.2 hR), lkjPDFReal_of_not_posDef p η hR]

/-- Congruence by a square matrix of determinant `±1` preserves the LKJ density. -/
theorem lkjPDF_symmetricCongruenceLinearMap {M : Matrix (Fin p) (Fin p) ℝ}
    (hM : M.det ^ 2 = 1) (R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
    lkjPDF p η (Matrix.symmetricCongruenceLinearMap M R) = lkjPDF p η R := by
  rw [lkjPDF_def, lkjPDFReal_symmetricCongruenceLinearMap hM, lkjPDF_def]

/-- Congruence by a square matrix of determinant `±1` that preserves the reference measure also
preserves every LKJ law. -/
private theorem map_symmetricCongruenceLinearMap_lkjMeasure {M : Matrix (Fin p) (Fin p) ℝ}
    (hM : M.det ^ 2 = 1)
    (hμ : (correlationLebesgue p).map (Matrix.symmetricCongruenceLinearMap M) =
      correlationLebesgue p) :
    (lkjMeasure p η).map (Matrix.symmetricCongruenceLinearMap M) = lkjMeasure p η := by
  by_cases hη : 0 < η
  · rw [lkjMeasure_of_pos hη]
    refine Measure.map_withDensity_eq_withDensity (jac := 1)
      (LinearMap.continuous_of_finiteDimensional _).measurable measurable_const
      (measurable_lkjPDF p η) (by rwa [withDensity_one]) (ae_of_all _ fun R ↦ ?_)
    rw [Pi.one_apply, one_mul, lkjPDF_symmetricCongruenceLinearMap hM]
  · simp [lkjMeasure_of_nonpos (not_lt.mp hη)]

variable (p η) in
/-- **Permutation invariance of the LKJ law.** Relabelling the indices, `R ↦ P R Pᵀ` for a
permutation matrix `P`, preserves the LKJ law. -/
theorem map_symmetricCongruenceLinearMap_permMatrix_lkjMeasure (σ : Equiv.Perm (Fin p)) :
    (lkjMeasure p η).map (Matrix.symmetricCongruenceLinearMap (σ.permMatrix ℝ)) =
      lkjMeasure p η := by
  refine map_symmetricCongruenceLinearMap_lkjMeasure ?_
    (map_symmetricCongruenceLinearMap_permMatrix_correlationLebesgue p σ)
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [Matrix.det_permutation, h]

variable (p η) in
/-- **Sign invariance of the LKJ law.** Flipping the signs of coordinate axes, `R ↦ D R D` for a
diagonal matrix `D` with entries `±1`, preserves the LKJ law. -/
theorem map_symmetricCongruenceLinearMap_diagonal_lkjMeasure {s : Fin p → ℝ}
    (hs : ∀ i, |s i| = 1) :
    (lkjMeasure p η).map (Matrix.symmetricCongruenceLinearMap (Matrix.diagonal s)) =
      lkjMeasure p η := by
  refine map_symmetricCongruenceLinearMap_lkjMeasure ?_
    (map_symmetricCongruenceLinearMap_diagonal_correlationLebesgue p hs)
  rw [Matrix.det_diagonal, ← Finset.prod_pow]
  exact Finset.prod_eq_one fun i _ ↦ by rw [← sq_abs, hs i, one_pow]

/-! ### The mean -/

/-- Every entry of an LKJ matrix is integrable: it lies in `[-1, 1]` almost surely. -/
private theorem integrable_coe_apply_lkjMeasure (i j : Fin p) :
    Integrable (fun R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
      (R : Matrix (Fin p) (Fin p) ℝ) i j) (lkjMeasure p η) := by
  by_cases hη : 0 < η
  · have := isProbabilityMeasure_lkjMeasure (p := p) hη
    refine Integrable.of_bound (selfAdjoint.measurable_coe_apply i j).aestronglyMeasurable 1 ?_
    filter_upwards [ae_posDef_lkjMeasure p η, ae_diag_eq_one_lkjMeasure p η] with R hR hdiag
    have hsq : ((R : Matrix (Fin p) (Fin p) ℝ) i j) ^ 2 ≤ 1 := by
      simpa [RCLike.normSq_apply, sq, hdiag] using hR.posSemidef.normSq_le i j
    rw [Real.norm_eq_abs]
    exact (sq_le_one_iff_abs_le_one _).1 hsq
  · simp [lkjMeasure_of_nonpos (not_lt.mp hη)]

/-- An off-diagonal entry of an LKJ matrix has mean zero: flipping the sign of axis `i` preserves
the law and negates the entry. -/
private theorem integral_coe_apply_lkjMeasure_of_ne {i j : Fin p} (hij : i ≠ j) :
    ∫ R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ),
        (R : Matrix (Fin p) (Fin p) ℝ) i j ∂lkjMeasure p η = 0 := by
  set s : Fin p → ℝ := fun k ↦ if k = i then -1 else 1
  have hs : ∀ k, |s k| = 1 := fun k ↦ by by_cases hk : k = i <;> simp [s, hk]
  have h := integral_map (μ := lkjMeasure p η)
    (φ := Matrix.symmetricCongruenceLinearMap (Matrix.diagonal s))
    (f := fun R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
      (R : Matrix (Fin p) (Fin p) ℝ) i j)
    (LinearMap.continuous_of_finiteDimensional _).measurable.aemeasurable
    (selfAdjoint.measurable_coe_apply i j).aestronglyMeasurable
  rw [map_symmetricCongruenceLinearMap_diagonal_lkjMeasure p η hs] at h
  simp only [Matrix.coe_symmetricCongruenceLinearMap_apply, Matrix.diagonal_transpose,
    Matrix.mul_diagonal, Matrix.diagonal_mul, s, hij.symm, ↓reduceIte, neg_one_mul, mul_one,
    integral_neg] at h
  linarith

/-- The entrywise mean of an LKJ matrix is the identity matrix. -/
private theorem integral_coe_apply_lkjMeasure (hη : 0 < η) (i j : Fin p) :
    ∫ R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ),
        (R : Matrix (Fin p) (Fin p) ℝ) i j ∂lkjMeasure p η =
      (1 : Matrix (Fin p) (Fin p) ℝ) i j := by
  rcases eq_or_ne i j with rfl | hij
  · have := isProbabilityMeasure_lkjMeasure (p := p) hη
    rw [Matrix.one_apply_eq, integral_congr_ae ((ae_diag_eq_one_lkjMeasure p η).mono
      fun R hR ↦ hR i), integral_const, probReal_univ, one_smul]
  · rw [Matrix.one_apply_ne hij]
    exact integral_coe_apply_lkjMeasure_of_ne hij

variable (p η) in
/-- An LKJ matrix is integrable. -/
theorem integrable_id_lkjMeasure :
    Integrable (fun R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦ R)
      (lkjMeasure p η) :=
  integrable_iff_integrable_coe_apply.2 integrable_coe_apply_lkjMeasure

/-- **The mean of an LKJ law** of positive shape is the identity matrix. -/
theorem integral_id_lkjMeasure (hη : 0 < η) :
    ∫ R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ), R ∂lkjMeasure p η =
      (⟨1, IsSelfAdjoint.one _⟩ : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) := by
  have hcoords : Integrable (fun R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
      symmetricCoordinates p R) (lkjMeasure p η) :=
    (symmetricCoordinates p).toContinuousLinearMap.integrable_comp (integrable_id_lkjMeasure p η)
  apply (symmetricCoordinates p).injective
  funext ij
  rw [← (symmetricCoordinates p).integral_comp_comm, eval_integral fun ij ↦ hcoords.eval ij]
  simp only [symmetricCoordinates_apply]
  exact integral_coe_apply_lkjMeasure hη ij.1.1 ij.1.2

end TauCeti.Probability
