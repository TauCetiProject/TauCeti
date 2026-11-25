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
  norm at least `1`, and operator norm `(√5 + 1) / 2`;
* the zero map and the orthogonal projection `diag(1, 0)` have minimal stretch `0`, the projection
  with operator norm `1`;
* in dimension one, `ℓ(a • id) = ‖a • id‖ = |a|`;
* the perturbation bound `|ℓ(A) - ℓ(B)| ≤ ‖A - B‖` is attained, with value `1/4`, for
  `A = diag(3, 1/2)` and `B = diag(3, 3/4)`; and scaling by `-2`.
-/

public section

open Module Matrix LinearMap

namespace TauCeti.MinimalStretchChecks

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

/-- The shear `[[1, 1], [0, 1]]` has minimal stretch `(√5 - 1) / 2` and operator norm
`(√5 + 1) / 2`: its squared singular values are `(3 ± √5) / 2`
(`Matrix.sq_singularValues_toLin_shear_fin_two` at `t = 1`). -/
example : (toLin e.toBasis e.toBasis !![(1 : ℝ), 1; 0, 1]).minimalStretch = (√5 - 1) / 2 ∧
    ‖toContinuousLinearMap (toLin e.toBasis e.toBasis !![(1 : ℝ), 1; 0, 1])‖ = (√5 + 1) / 2 := by
  have hE : finrank ℝ E = 2 := by rw [finrank_eq_card_basis e.toBasis, Fintype.card_fin]
  obtain ⟨h0, h1⟩ := sq_singularValues_toLin_shear_fin_two e 1
  norm_num at h0 h1
  have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h5' : (1 : ℝ) ≤ √5 := Real.one_le_sqrt.mpr (by norm_num)
  simp only [minimalStretch_def, hE, Nat.reduceSub,
    norm_toContinuousLinearMap_eq_singularValues_zero]
  refine ⟨(pow_left_inj₀ (singularValues_nonneg _ _) (by linarith) two_ne_zero).mp ?_,
    (pow_left_inj₀ (singularValues_nonneg _ _) (by positivity) two_ne_zero).mp ?_⟩
  · rw [h1]
    linear_combination (-1 / 4 : ℝ) * h5
  · rw [h0]
    linear_combination (-1 / 4 : ℝ) * h5

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

/-- Perturbation: the bound `|ℓ(A) - ℓ(B)| ≤ ‖A - B‖` of `lipschitzWith_minimalStretch` is
attained for `A = diag(3, 1/2)` and `B = diag(3, 3/4)`, both sides being `1/4`. -/
example : |(toLin e.toBasis e.toBasis (diagonal ![(3 : ℝ), 1 / 2])).minimalStretch -
      (toLin e.toBasis e.toBasis (diagonal ![(3 : ℝ), 3 / 4])).minimalStretch| = 1 / 4 ∧
    ‖toContinuousLinearMap (toLin e.toBasis e.toBasis (diagonal ![(3 : ℝ), 1 / 2]) -
      toLin e.toBasis e.toBasis (diagonal ![(3 : ℝ), 3 / 4]))‖ = 1 / 4 := by
  refine ⟨?_, ?_⟩
  · rw [minimalStretch_def, minimalStretch_def, finrank_eq_card_basis e.toBasis,
      singularValues_toLin_diagonal_fin_two e (by norm_num),
      singularValues_toLin_diagonal_fin_two e (by norm_num)]
    norm_num
  · set d : Fin 2 → ℝ := fun i ↦ ![(3 : ℝ), 1 / 2] i - ![3, 3 / 4] i
    have hanti : Antitone fun k ↦ ‖d (Equiv.swap (0 : Fin 2) 1 k)‖ := by
      intro i j
      fin_cases i <;> fin_cases j <;> norm_num [d]
    rw [← map_sub, diagonal_sub, norm_toContinuousLinearMap_eq_singularValues_zero]
    exact (singularValues_toLin_diagonal e d (Equiv.swap (0 : Fin 2) 1) hanti 0).trans
      (by norm_num [d])

/-- Scaling `diag(3, 1/2)` by `-2` gives minimal stretch `1 = |-2| · 1/2`. -/
example :
    ((-2 : ℝ) • toLin e.toBasis e.toBasis (diagonal ![(3 : ℝ), 1 / 2])).minimalStretch = 1 := by
  rw [minimalStretch_smul, minimalStretch_def, finrank_eq_card_basis e.toBasis,
    singularValues_toLin_diagonal_fin_two e (by norm_num)]
  norm_num

/-- In dimension one, `ℓ(a • id) = ‖a • id‖ = |a|`. -/
example {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
    (hL : finrank ℝ L = 1) (a : ℝ) :
    (a • (LinearMap.id : L →ₗ[ℝ] L)).minimalStretch = |a| ∧
      ‖toContinuousLinearMap (a • (LinearMap.id : L →ₗ[ℝ] L))‖ = |a| := by
  have : Nontrivial L := Module.nontrivial_of_finrank_eq_succ hL
  refine ⟨?_, ?_⟩
  · rw [minimalStretch_smul, minimalStretch_id, Real.norm_eq_abs, mul_one]
  · have hid : toContinuousLinearMap (LinearMap.id : L →ₗ[ℝ] L) = ContinuousLinearMap.id ℝ L := by
      ext; rfl
    rw [map_smul, norm_smul, hid, ContinuousLinearMap.norm_id, Real.norm_eq_abs, mul_one]

end TauCeti.MinimalStretchChecks
