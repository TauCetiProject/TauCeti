/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Otis Chodosh, The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Tactic.Ring

/-!
# A norm identity for symmetric operators in dimension two

For a symmetric endomorphism of a two-dimensional real inner product space, its squared
Hilbert–Schmidt norm times `‖v‖²` is
`2 ‖A v‖² - 2 ⟪A v, v⟫ tr A + (tr A)² ‖v‖²`.

The Hilbert–Schmidt norm is expressed as the double sum of squared matrix coefficients in an
arbitrary orthonormal basis. The identity holds for every vector, including zero.

Adapted from Otis Chodosh's formalization in
`ForTauCeti/Analysis/InnerProductSpace/Symmetric/TwoDimensional.lean` in
[ColdingMinicozziTheory](https://github.com/riccardobrasca/ColdingMinicozziTheory)
(commit `4c7bbc449a836e5e574058ccf0ac3f5110a99bd4`).
-/

public section

open scoped InnerProductSpace

namespace LinearMap.IsSymmetric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {A : E →ₗ[ℝ] E}

/-- A symmetric operator in dimension two satisfies this identity relating its squared
Hilbert–Schmidt norm, trace, and value on an arbitrary vector. -/
theorem sum_sq_inner_apply_mul_norm_sq_eq (hA : A.IsSymmetric)
    (b : OrthonormalBasis (Fin 2) ℝ E) (v : E) :
    (∑ i, ∑ j, ⟪A (b i), b j⟫_ℝ ^ 2) * ‖v‖ ^ 2 =
      2 * ‖A v‖ ^ 2 - 2 * ⟪A v, v⟫_ℝ * LinearMap.trace ℝ E A +
        (LinearMap.trace ℝ E A) ^ 2 * ‖v‖ ^ 2 := by
  have hsym : ⟪A (b 1), b 0⟫_ℝ = ⟪A (b 0), b 1⟫_ℝ :=
    (hA (b 1) (b 0)).trans (real_inner_comm (b 1) (A (b 0))).symm
  have hAv (i : Fin 2) : ⟪A v, b i⟫_ℝ =
      ⟪b 0, v⟫_ℝ * ⟪A (b 0), b i⟫_ℝ +
        ⟪b 1, v⟫_ℝ * ⟪A (b 1), b i⟫_ℝ := by
    have h := congrArg (fun w ↦ inner ℝ (A w) (b i)) (b.sum_repr' v)
    simpa only [Fin.sum_univ_two, map_add, map_smul, inner_add_left,
      real_inner_smul_left] using h.symm
  simp_rw [← b.sum_sq_inner_left v, ← b.sum_sq_inner_left (A v)]
  rw [← b.sum_inner_mul_inner (A v) v]
  simp only [LinearMap.trace_eq_sum_inner A b, Fin.sum_univ_two, hAv,
    real_inner_comm v (b 0), real_inner_comm v (b 1),
    real_inner_comm (b 0) (A (b 0)), real_inner_comm (b 1) (A (b 1)), hsym]
  ring

end LinearMap.IsSymmetric
