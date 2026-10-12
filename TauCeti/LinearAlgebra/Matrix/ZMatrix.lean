/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.QuadraticForm
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Nonnegative vectors on which a symmetric Z-matrix is nonpositive

A real square matrix is a *Z-matrix* when its off-diagonal entries are nonpositive. The generalized
Cartan matrix `2I - A` of a (multi)graph with adjacency matrix `A` is the basic example. This file
proves that a symmetric Z-matrix `M` whose quadratic form is not positive definite has a nonzero
vector `δ` with nonnegative entries and `M δ ≤ 0` entrywise.

For `M = 2I - A` the condition `M δ ≤ 0` reads `2 δᵢ ≤ ∑ⱼ Aᵢⱼ δⱼ` at every vertex. A positive
definite `M` admits no such `δ`, since `δᵀ M δ ≤ 0`, so for a symmetric Z-matrix the existence of
`δ` is equivalent to the failure of positive definiteness. Such a vector is the input to growth
arguments for algebras attached to a graph whose form `2I - A` is not positive definite.

## Main results

* `Matrix.exists_nonneg_mulVec_nonpos_of_dotProduct_mulVec_nonpos`: a symmetric real Z-matrix
  with a nonzero vector `x` satisfying `xᵀ M x ≤ 0` has a nonzero nonnegative `δ` with `M δ ≤ 0`.
* `Matrix.exists_nonneg_mulVec_nonpos_of_not_posDef`: the same for a symmetric real Z-matrix that
  is not positive definite.

## References

* V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., Chapter 4, Theorem 4.3, where the
  finite, affine and indefinite types of a generalized Cartan matrix are separated by the signs of
  `M δ` for nonnegative vectors `δ`.
-/

public section

namespace Matrix

open Finset

variable {n : Type*} [Fintype n]

/-- **A symmetric Z-matrix with a nonpositive value of its form is nonpositive on a nonnegative
vector.**
Let `M` be a symmetric real matrix with nonpositive off-diagonal entries, and suppose that
`xᵀ M x ≤ 0` for some nonzero `x`. Then some nonzero vector `δ` with nonnegative entries satisfies
`M δ ≤ 0` entrywise. -/
theorem exists_nonneg_mulVec_nonpos_of_dotProduct_mulVec_nonpos {M : Matrix n n ℝ}
    (hM : M.IsSymm) (hM0 : ∀ i j, i ≠ j → M i j ≤ 0) {x : n → ℝ} (hx : x ≠ 0)
    (hxM : x ⬝ᵥ M *ᵥ x ≤ 0) :
    ∃ δ : n → ℝ, 0 ≤ δ ∧ δ ≠ 0 ∧ M *ᵥ δ ≤ 0 := by
  classical
  -- The entrywise absolute value of `x` has a form at most that of `x`.
  have habs : (fun i ↦ |x i|) ⬝ᵥ M *ᵥ (fun i ↦ |x i|) ≤ 0 := by
    refine le_trans ?_ hxM
    simp only [dotProduct, mulVec, mul_sum]
    refine sum_le_sum fun i _ ↦ sum_le_sum fun j _ ↦ ?_
    rcases eq_or_ne i j with rfl | hij
    · have h := abs_mul_abs_self (x i)
      linear_combination M i i * h
    · have h : x i * x j ≤ |x i| * |x j| := by
        rw [← abs_mul]
        exact le_abs_self _
      nlinarith [hM0 i j hij]
  -- Normalizing it gives a point of the standard simplex with nonpositive form.
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hx
  set s := ∑ i, |x i|
  have hs : 0 < s :=
    lt_of_lt_of_le (abs_pos.mpr hi₀) (single_le_sum (fun i _ ↦ abs_nonneg (x i)) (mem_univ i₀))
  set y₀ : n → ℝ := s⁻¹ • fun i ↦ |x i|
  set K : Set (n → ℝ) := {z | 0 ≤ z ∧ ∑ k, z k = 1}
  have hy₀ : y₀ ∈ K := by
    refine ⟨fun i ↦ ?_, ?_⟩
    · simp only [y₀, Pi.zero_apply, Pi.smul_apply, smul_eq_mul]
      positivity
    simp only [y₀, Pi.smul_apply, smul_eq_mul, ← mul_sum]
    exact inv_mul_cancel₀ hs.ne'
  have hqy₀ : y₀ ⬝ᵥ M *ᵥ y₀ ≤ 0 := by
    simp only [y₀, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
    exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr hs.le)
      (mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr hs.le) habs)
  -- The form attains its minimum on the compact standard simplex.
  have hK : IsCompact K := by
    refine (isCompact_Icc (a := 0) (b := 1)).of_isClosed_subset ?_ fun z hz ↦
      ⟨hz.1, fun k ↦ (single_le_sum (fun l _ ↦ hz.1 l) (mem_univ k)).trans_eq hz.2⟩
    exact (isClosed_le continuous_const continuous_id).inter
      (isClosed_eq (continuous_finsetSum _ fun i _ ↦ continuous_apply i) continuous_const)
  have hcont : Continuous fun z : n → ℝ ↦ z ⬝ᵥ M *ᵥ z :=
    continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_id)
  obtain ⟨y, hy, hmin⟩ := hK.exists_isMinOn ⟨y₀, hy₀⟩ hcont.continuousOn
  refine ⟨y, hy.1, fun h ↦ by simpa [h] using hy.2, fun i ↦ ?_⟩
  have hyi : 0 ≤ y i := hy.1 i
  rcases hyi.lt_or_eq with hi | hi
  · calc (M *ᵥ y) i = ∑ j, y j * (M *ᵥ y) i := by rw [← sum_mul, hy.2, one_mul]
      _ ≤ ∑ j, y j * (M *ᵥ y) j := sum_le_sum fun j _ ↦
          mul_le_mul_of_nonneg_left
            (TauCeti.Matrix.mulVec_apply_le_of_isMinOn hM hy hmin hi j) (hy.1 j)
      _ = y ⬝ᵥ M *ᵥ y := rfl
      _ ≤ y₀ ⬝ᵥ M *ᵥ y₀ := isMinOn_iff.mp hmin _ hy₀
      _ ≤ 0 := hqy₀
  · simp only [mulVec, dotProduct, Pi.zero_apply]
    refine sum_nonpos fun j _ ↦ ?_
    rcases eq_or_ne i j with rfl | hij
    · rw [← hi, mul_zero]
    · exact mul_nonpos_of_nonpos_of_nonneg (hM0 i j hij) (hy.1 j)

/-- **A symmetric Z-matrix that is not positive definite is nonpositive on a nonnegative
vector.**
If a symmetric real matrix `M` with nonpositive off-diagonal entries is not positive definite, then
some nonzero vector `δ` with nonnegative entries satisfies `M δ ≤ 0` entrywise. -/
theorem exists_nonneg_mulVec_nonpos_of_not_posDef {M : Matrix n n ℝ} (hM : M.IsSymm)
    (hM0 : ∀ i j, i ≠ j → M i j ≤ 0) (h : ¬ M.PosDef) :
    ∃ δ : n → ℝ, 0 ≤ δ ∧ δ ≠ 0 ∧ M *ᵥ δ ≤ 0 := by
  rw [posDef_iff_dotProduct_mulVec] at h
  push Not at h
  obtain ⟨x, hx, hxM⟩ := h (isHermitian_iff_isSymm.mpr hM)
  exact exists_nonneg_mulVec_nonpos_of_dotProduct_mulVec_nonpos hM hM0 hx (by simpa using hxM)

end Matrix
