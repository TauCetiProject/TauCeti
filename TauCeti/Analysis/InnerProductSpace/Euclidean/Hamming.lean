/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.InformationTheory.Hamming
import Mathlib.Tactic.NormNum

/-!
# Euclidean and Hamming distances on binary vectors

Each differing coordinate contributes one to the squared Euclidean distance between two
binary vectors. Scaling both vectors multiplies this contribution by the square of the scalar.
-/

public section

namespace TauCeti

variable {ι : Type*} [Fintype ι]

/-- Squared Euclidean distance agrees with Hamming distance between real binary vectors. -/
theorem norm_toLp_sub_sq_eq_hammingDist_of_binary {x y : ι → ℝ}
    (hx : ∀ i, x i = 0 ∨ x i = 1) (hy : ∀ i, y i = 0 ∨ y i = 1) :
    ‖WithLp.toLp 2 x - WithLp.toLp 2 y‖ ^ 2 = (hammingDist x y : ℝ) := by
  rw [EuclideanSpace.real_norm_sq_eq, hammingDist, Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [PiLp.sub_apply]
  rcases hx i with h | h <;> rcases hy i with h' | h' <;> norm_num [h, h']

/-- The squared Euclidean distance between two binary vectors scaled by `a` is
`a ^ 2` times their Hamming distance before scaling. -/
theorem norm_smul_toLp_sub_sq_eq_mul_hammingDist_of_binary {a : ℝ} {x y : ι → ℝ}
    (hx : ∀ i, x i = 0 ∨ x i = 1) (hy : ∀ i, y i = 0 ∨ y i = 1) :
    ‖a • WithLp.toLp 2 x - a • WithLp.toLp 2 y‖ ^ 2 = a ^ 2 * (hammingDist x y : ℝ) := by
  rw [← smul_sub, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    norm_toLp_sub_sq_eq_hammingDist_of_binary hx hy]

end TauCeti
