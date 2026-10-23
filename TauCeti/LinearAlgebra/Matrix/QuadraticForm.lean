/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Symmetric real matrix quadratic forms on the standard simplex

This file records the expansion of a symmetric matrix quadratic form along a line and the
first-order inequality at a minimizer on the standard simplex.

## Main results

* `TauCeti.Matrix.dotProduct_mulVec_add_smul`: expands the quadratic form along a line.
* `TauCeti.Matrix.mulVec_apply_le_of_isMinOn`: at a simplex minimizer, a coordinate of `M y` in the
  support of `y` is no larger than any other coordinate of `M y`.
-/

public section

namespace TauCeti.Matrix

open scoped _root_.Matrix
open _root_.Matrix
open Finset

variable {n : Type*} [Fintype n]

/-- The quadratic form of a symmetric matrix along the line through `y` in the direction `d`. -/
lemma dotProduct_mulVec_add_smul {M : Matrix n n ℝ} (hM : M.IsSymm) (y d : n → ℝ)
    (t : ℝ) :
    (y + t • d) ⬝ᵥ M *ᵥ (y + t • d) =
      y ⬝ᵥ M *ᵥ y + 2 * t * (d ⬝ᵥ M *ᵥ y) + t ^ 2 * (d ⬝ᵥ M *ᵥ d) := by
  have h : y ⬝ᵥ M *ᵥ d = d ⬝ᵥ M *ᵥ y := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hM.eq, dotProduct_comm]
  simp only [mulVec_add, mulVec_smul, add_dotProduct, dotProduct_add, smul_dotProduct,
    dotProduct_smul, smul_eq_mul, h]
  ring

/-- At a minimizer `y` of the quadratic form of a symmetric matrix on the standard simplex, the
entry `(M y)ᵢ` at a coordinate in the support of `y` is the smallest entry of `M y`. -/
lemma mulVec_apply_le_of_isMinOn {M : Matrix n n ℝ} (hM : M.IsSymm) {y : n → ℝ}
    (hy : 0 ≤ y ∧ ∑ k, y k = 1)
    (hmin : IsMinOn (fun z ↦ z ⬝ᵥ M *ᵥ z) {z | 0 ≤ z ∧ ∑ k, z k = 1} y)
    {i : n} (hi : 0 < y i) (j : n) :
    (M *ᵥ y) i ≤ (M *ᵥ y) j := by
  classical
  -- Move mass `t` from the coordinate `i` to the coordinate `j`.
  set d : n → ℝ := Pi.single j 1 - Pi.single i 1
  have hd : d ⬝ᵥ M *ᵥ y = (M *ᵥ y) j - (M *ᵥ y) i := by
    simp [d, sub_dotProduct]
  have hmem (t : ℝ) (ht : 0 ≤ t) (hti : t ≤ y i) :
      0 ≤ y + t • d ∧ ∑ k, (y + t • d) k = 1 := by
    refine ⟨fun k ↦ ?_, ?_⟩
    · have hk : 0 ≤ y k := hy.1 k
      simp only [d, Pi.zero_apply, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
        Pi.single_apply]
      split_ifs with hkj hki <;> subst_vars <;> linarith
    · simp only [d, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, sum_add_distrib,
        ← mul_sum, sum_sub_distrib, sum_pi_single', mem_univ, ite_true, sub_self, mul_zero,
        add_zero, hy.2]
  have hkey (t : ℝ) (ht : 0 < t) (hti : t ≤ y i) :
      0 ≤ 2 * ((M *ᵥ y) j - (M *ᵥ y) i) + t * (d ⬝ᵥ M *ᵥ d) := by
    have h := isMinOn_iff.mp hmin _ (hmem t ht.le hti)
    simp only [dotProduct_mulVec_add_smul hM, hd] at h
    have h' : 0 ≤ t * (2 * ((M *ᵥ y) j - (M *ᵥ y) i) + t * (d ⬝ᵥ M *ᵥ d)) := by
      nlinarith
    exact (mul_nonneg_iff_of_pos_left ht).mp h'
  by_contra hlt
  push Not at hlt
  -- A small enough step strictly lowers the form.
  set a := (M *ᵥ y) j - (M *ᵥ y) i
  set c := d ⬝ᵥ M *ᵥ d
  have ha : 0 < -a := by simp only [a]; linarith
  set t := min (y i) (-a / (|c| + 1))
  have ht : 0 < t := lt_min hi (div_pos ha (by positivity))
  have htc : t * c < -a :=
    calc t * c ≤ t * |c| := mul_le_mul_of_nonneg_left (le_abs_self c) ht.le
      _ ≤ -a / (|c| + 1) * |c| := mul_le_mul_of_nonneg_right (min_le_right _ _) (abs_nonneg c)
      _ < -a := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith [abs_nonneg c]
  linarith [hkey t ht (min_le_left _ _)]

end TauCeti.Matrix
