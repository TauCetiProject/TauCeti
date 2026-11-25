/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.SingularValues.Least
public import TauCeti.Analysis.InnerProductSpace.SingularValues.Planar

/-!
# Checks for the minimal stretch

Worked examples for `LinearMap.minimalStretch` on a real inner product plane with an orthonormal
basis `e`, writing `toLin e e M` for the operator with matrix `M` in that basis:

* `diag(3, 1/2)` has minimal stretch `1/2` and operator norm `3`; the minimal stretch is the
  singular value at the last index `1`, while index `0` gives the norm and index `2` gives `0`;
* the shear `[[1, 1], [0, 1]]` has minimal stretch `(√5 - 1) / 2`, although its columns both have
  norm at least `1`;
* the zero map and the orthogonal projection `diag(1, 0)` have minimal stretch `0`, the projection
  with operator norm `1`;
* in dimension one, `ℓ(a • id) = ‖a • id‖ = |a|`;
* the perturbation bound for `diag(3, 1/2)` and `diag(3, 3/4)`, and scaling by `-2`.
-/

public section

open Module Matrix

namespace LinearMap.MinimalStretchChecks

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  (e : OrthonormalBasis (Fin 2) ℝ E)

/-- The minimal stretch of `diag(3, 1/2)` is `1/2`. -/
example : (toLin e.toBasis e.toBasis (diagonal ![3, 1 / 2])).minimalStretch = 1 / 2 := by
  rw [minimalStretch_def, finrank_eq_card_basis e.toBasis,
    singularValues_toLin_diagonal_fin_two e (by norm_num)]
  norm_num

/-- The operator norm of `diag(3, 1/2)` is `3`. -/
example : ‖toContinuousLinearMap (toLin e.toBasis e.toBasis (diagonal ![(3 : ℝ), 1 / 2]))‖ = 3 := by
  rw [norm_toContinuousLinearMap_eq_singularValues_zero,
    singularValues_toLin_diagonal_fin_two e (by norm_num)]
  norm_num

/-- The index is the last one: for `diag(3, 1/2)` the singular values at indices `0, 1, 2` are
`3, 1/2, 0`. -/
example : (toLin e.toBasis e.toBasis (diagonal ![(3 : ℝ), 1 / 2])).singularValues 0 = 3 ∧
    (toLin e.toBasis e.toBasis (diagonal ![(3 : ℝ), 1 / 2])).singularValues 1 = 1 / 2 ∧
    (toLin e.toBasis e.toBasis (diagonal ![(3 : ℝ), 1 / 2])).singularValues 2 = 0 := by
  rw [singularValues_toLin_diagonal_fin_two e (by norm_num)]
  norm_num

/-- The gram operator of the shear `[[1, 1], [0, 1]]` has trace `3` and determinant `1`. -/
theorem shear_gram :
    trace ℝ E (adjoint (toLin e.toBasis e.toBasis !![1, 1; 0, 1]) ∘ₗ
        toLin e.toBasis e.toBasis !![1, 1; 0, 1]) = 3 ∧
      (adjoint (toLin e.toBasis e.toBasis !![(1 : ℝ), 1; 0, 1]) ∘ₗ
        toLin e.toBasis e.toBasis !![1, 1; 0, 1]).det = 1 := by
  rw [← toLin_conjTranspose e e, ← toLin_mul]
  refine ⟨?_, ?_⟩
  · rw [trace_toLin_eq]
    simp [Matrix.trace, Fin.sum_univ_two, Matrix.mul_apply]
    norm_num
  · rw [det_toLin, Matrix.det_fin_two]
    simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- The minimal stretch of the shear `[[1, 1], [0, 1]]` is `(√5 - 1) / 2`. -/
example : (toLin e.toBasis e.toBasis !![(1 : ℝ), 1; 0, 1]).minimalStretch = (√5 - 1) / 2 := by
  have hE : finrank ℝ E = 2 := by rw [finrank_eq_card_basis e.toBasis, Fintype.card_fin]
  have h :=
    (toLin e.toBasis e.toBasis !![(1 : ℝ), 1; 0, 1]).sq_singularValues_one_of_finrank_eq_two hE
  obtain ⟨htr, hdet⟩ := shear_gram e
  rw [htr, hdet] at h
  rw [minimalStretch_def, hE]
  have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h5' : (1 : ℝ) < √5 := by
    rw [show (1 : ℝ) = √1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  refine (pow_left_inj₀ (singularValues_nonneg _ _) (by linarith) two_ne_zero).mp ?_
  simp only [RCLike.re_to_real] at h
  rw [show (2 - 1 : ℕ) = 1 from rfl, h, show (3 : ℝ) ^ 2 - 4 * 1 = 5 by norm_num]
  ring_nf
  rw [h5]
  ring

/-- The shear `[[1, 1], [0, 1]]` has operator norm `(√5 + 1) / 2`. -/
example : ‖toContinuousLinearMap (toLin e.toBasis e.toBasis !![(1 : ℝ), 1; 0, 1])‖ =
    (√5 + 1) / 2 := by
  have hE : finrank ℝ E = 2 := by rw [finrank_eq_card_basis e.toBasis, Fintype.card_fin]
  have h :=
    (toLin e.toBasis e.toBasis !![(1 : ℝ), 1; 0, 1]).sq_singularValues_zero_of_finrank_eq_two hE
  obtain ⟨htr, hdet⟩ := shear_gram e
  rw [htr, hdet] at h
  rw [norm_toContinuousLinearMap_eq_singularValues_zero]
  have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h5' : (0 : ℝ) ≤ √5 := Real.sqrt_nonneg 5
  refine (pow_left_inj₀ (singularValues_nonneg _ _) (by linarith) two_ne_zero).mp ?_
  simp only [RCLike.re_to_real] at h
  rw [h, show (3 : ℝ) ^ 2 - 4 * 1 = 5 by norm_num]
  ring_nf
  rw [h5]
  ring

/-- The zero map has minimal stretch `0`. -/
example : (0 : E →ₗ[ℝ] E).minimalStretch = 0 :=
  minimalStretch_zero

/-- The orthogonal projection `diag(1, 0)` has minimal stretch `0` and operator norm `1`. -/
example : (toLin e.toBasis e.toBasis (diagonal ![(1 : ℝ), 0])).minimalStretch = 0 ∧
    ‖toContinuousLinearMap (toLin e.toBasis e.toBasis (diagonal ![(1 : ℝ), 0]))‖ = 1 := by
  rw [minimalStretch_def, finrank_eq_card_basis e.toBasis,
    norm_toContinuousLinearMap_eq_singularValues_zero,
    singularValues_toLin_diagonal_fin_two e (by norm_num)]
  norm_num

/-- Perturbation: `|ℓ(diag(3, 1/2)) - ℓ(diag(3, 3/4))| = 1/4`, which is the norm `1/4` of the
difference `diag(0, -1/4)`. -/
example : |(toLin e.toBasis e.toBasis (diagonal ![(3 : ℝ), 1 / 2])).minimalStretch -
      (toLin e.toBasis e.toBasis (diagonal ![(3 : ℝ), 3 / 4])).minimalStretch| = 1 / 4 := by
  rw [minimalStretch_def, minimalStretch_def, finrank_eq_card_basis e.toBasis,
    singularValues_toLin_diagonal_fin_two e (by norm_num),
    singularValues_toLin_diagonal_fin_two e (by norm_num)]
  norm_num

/-- Scaling `diag(3, 1/2)` by `-2` gives minimal stretch `1 = |-2| · 1/2`. -/
example :
    ((-2 : ℝ) • toLin e.toBasis e.toBasis (diagonal ![(3 : ℝ), 1 / 2])).minimalStretch = 1 := by
  rw [minimalStretch_smul, minimalStretch_def, finrank_eq_card_basis e.toBasis,
    singularValues_toLin_diagonal_fin_two e (by norm_num)]
  norm_num

/-- In dimension one, `ℓ(a • id) = |a|`. -/
example {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
    (hL : finrank ℝ L = 1) (a : ℝ) : (a • (LinearMap.id : L →ₗ[ℝ] L)).minimalStretch = |a| := by
  have : Nontrivial L := Module.nontrivial_of_finrank_eq_succ hL
  rw [minimalStretch_smul, minimalStretch_id, Real.norm_eq_abs, mul_one]

end LinearMap.MinimalStretchChecks
