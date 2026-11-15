/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Symmetric matrix quadratic forms on the standard simplex

This file records the expansion of a symmetric matrix quadratic form along a line and the
first-order inequality at a minimizer on the standard simplex.

## Main results

* `Matrix.IsSymm.dotProduct_mulVec_add_smul`: over a commutative semiring, expands the quadratic
  form of a symmetric matrix along a line.
* `Matrix.IsSymm.mulVec_apply_le_of_isMinOn`: over a linearly ordered field, at a simplex
  minimizer, a coordinate of `M y` in the support of `y` is no larger than any other coordinate
  of `M y`.
-/

public section

namespace Matrix.IsSymm

open Finset

variable {n R : Type*} [Fintype n]

/-- The quadratic form of a symmetric matrix along the line through `y` in the direction `d`. -/
lemma dotProduct_mulVec_add_smul [CommSemiring R] {M : Matrix n n R} (hM : M.IsSymm)
    (y d : n → R) (t : R) :
    (y + t • d) ⬝ᵥ M *ᵥ (y + t • d) =
      y ⬝ᵥ M *ᵥ y + 2 * t * (d ⬝ᵥ M *ᵥ y) + t ^ 2 * (d ⬝ᵥ M *ᵥ d) := by
  simp only [mulVec_add, mulVec_smul, add_dotProduct, dotProduct_add, smul_dotProduct,
    dotProduct_smul, smul_eq_mul, hM.dotProduct_mulVec_comm (x := y) (y := d)]
  ring

/-- At a minimizer `y` of the quadratic form of a symmetric matrix on the standard simplex, the
entry `(M y)ᵢ` at a coordinate in the support of `y` is the smallest entry of `M y`. -/
lemma mulVec_apply_le_of_isMinOn [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    {M : Matrix n n R} (hM : M.IsSymm) {y : n → R} (hy : 0 ≤ y ∧ ∑ k, y k = 1)
    (hmin : IsMinOn (fun z ↦ z ⬝ᵥ M *ᵥ z) {z | 0 ≤ z ∧ ∑ k, z k = 1} y)
    {i : n} (hi : 0 < y i) (j : n) :
    (M *ᵥ y) i ≤ (M *ᵥ y) j := by
  classical
  -- Move mass `t` from the coordinate `i` to the coordinate `j`.
  set d : n → R := Pi.single j 1 - Pi.single i 1
  have hd : d ⬝ᵥ M *ᵥ y = (M *ᵥ y) j - (M *ᵥ y) i := by
    simp [d, sub_dotProduct]
  have hmem (t : R) (ht : 0 ≤ t) (hti : t ≤ y i) :
      0 ≤ y + t • d ∧ ∑ k, (y + t • d) k = 1 := by
    refine ⟨fun k ↦ ?_, ?_⟩
    · have hk : 0 ≤ y k := hy.1 k
      simp only [d, Pi.zero_apply, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
        Pi.single_apply]
      split_ifs with hkj hki <;> subst_vars <;> linarith
    · simp [d, sum_add_distrib, ← mul_sum, hy.2]
  -- By minimality, the change `2 t a + t² c` of the form along the step is nonnegative.
  set a := (M *ᵥ y) j - (M *ᵥ y) i
  set c := d ⬝ᵥ M *ᵥ d
  have hkey (t : R) (ht : 0 < t) (hti : t ≤ y i) : 0 ≤ 2 * a + t * c := by
    have h := isMinOn_iff.mp hmin _ (hmem t ht.le hti)
    simp only [hM.dotProduct_mulVec_add_smul, hd] at h
    exact (mul_nonneg_iff_of_pos_left ht).mp (by linarith)
  -- If `a < 0`, a small enough step strictly lowers the form.
  by_contra! hlt
  have ha : 0 < -a := by linarith
  set t := min (y i) (-a / (|c| + 1))
  have ht : 0 < t := lt_min hi (div_pos ha (by positivity))
  have htc : t * (|c| + 1) ≤ -a := (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  nlinarith [hkey t ht (min_le_left _ _), le_abs_self c]

end Matrix.IsSymm
