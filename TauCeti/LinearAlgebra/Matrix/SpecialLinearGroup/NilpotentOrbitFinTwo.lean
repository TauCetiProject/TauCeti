/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import TauCeti.LinearAlgebra.Matrix.Trace.FinTwo

/-!
# The nilpotent conjugation orbits of `SL(2, ℝ)`

A `2 × 2` matrix `Y` has trace zero and determinant zero exactly when it is nilpotent, and then its
off-diagonal entries satisfy `Y₀₁ Y₁₀ = -Y₀₀²`, so they have opposite signs. Hence the punctured
nilpotent cone `{Y | tr Y = 0, det Y = 0, Y ≠ 0}` of `2 × 2` matrices over a linearly ordered
commutative ring such as `ℝ` is the disjoint union of the half with `Y₀₁ ≥ 0 ≥ Y₁₀` and the half
with `Y₀₁ ≤ 0 ≤ Y₁₀` (`Matrix.setOf_trace_eq_zero_det_eq_zero_ne_zero_eq_union` and
`Matrix.disjoint_setOf_trace_eq_zero_det_eq_zero_ne_zero`, in
`TauCeti.LinearAlgebra.Matrix.Trace.FinTwo`).

Conjugating `E = [[0, 1], [0, 0]]` (`Matrix.single 0 1 1`) by `g = [[a, b], [c, d]]` in
`SL(2, R)`, over any commutative ring `R`, gives `g E g⁻¹ = [[-a c, a²], [-c², a c]]`. So over `ℝ`
the conjugation orbit of `E` is the first half and the orbit of `-E` is the second half.

## Main results

* `Matrix.SpecialLinearGroup.coe_mul_single_mul_coe_inv`: `g E g⁻¹ = [[-a c, a²], [-c², a c]]` in
  `SL(2, R)` over any commutative ring `R`.
* `Matrix.SpecialLinearGroup.range_coe_mul_single_mul_coe_inv`: the conjugation orbit of `E` in
  `SL(2, ℝ)` is the half of the punctured nilpotent cone with `Y₀₁ ≥ 0 ≥ Y₁₀`.
* `Matrix.SpecialLinearGroup.range_coe_mul_neg_single_mul_coe_inv`: the conjugation orbit of `-E`
  is the half with `Y₀₁ ≤ 0 ≤ Y₁₀`.

## References

* A. A. Kirillov, *Lectures on the Orbit Method*, Graduate Studies in Mathematics 64, AMS, 2004,
  Section 1.2.
-/

public section

open scoped MatrixGroups

namespace Matrix

namespace SpecialLinearGroup

/-- Conjugating `E = [[0, 1], [0, 0]]` by `g = [[a, b], [c, d]]` in `SL(2, R)`, over any
commutative ring `R`, gives `[[-a c, a²], [-c², a c]]`. -/
theorem coe_mul_single_mul_coe_inv {R : Type*} [CommRing R] (g : SL(2, R)) :
    (g : Matrix (Fin 2) (Fin 2) R) * single 0 1 1 * ((g⁻¹ : SL(2, R)) : Matrix (Fin 2) (Fin 2) R) =
      !![-(g 0 0 * g 1 0), g 0 0 ^ 2; -(g 1 0 ^ 2), g 0 0 * g 1 0] := by
  rw [SL2_inv_expl]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, single_apply] <;> ring

/-- Every nonzero trace-zero matrix of determinant zero with `Y₀₁ ≥ 0 ≥ Y₁₀` is conjugate to
`E = [[0, 1], [0, 0]]` in `SL(2, ℝ)`, written with the formula of `coe_mul_single_mul_coe_inv`. -/
private theorem exists_eq_of_trace_eq_zero_of_det_eq_zero {Y : Matrix (Fin 2) (Fin 2) ℝ}
    (htr : Y.trace = 0) (hdet : Y.det = 0) (hne : Y ≠ 0) (hy : 0 ≤ Y 0 1) (hz : Y 1 0 ≤ 0) :
    ∃ g : SL(2, ℝ), !![-(g 0 0 * g 1 0), g 0 0 ^ 2; -(g 1 0 ^ 2), g 0 0 * g 1 0] = Y := by
  have h11 : Y 1 1 = -Y 0 0 := by
    rw [trace_fin_two] at htr
    linear_combination htr
  have hx : Y 0 0 ^ 2 = Y 0 1 * -Y 1 0 := by
    linear_combination mul_eq_neg_sq_of_trace_eq_zero_of_det_eq_zero_fin_two htr hdet
  have hpos : 0 < Y 0 1 - Y 1 0 := by
    by_contra! hle
    have h01 : Y 0 1 = 0 := by linarith
    have h10 : Y 1 0 = 0 := by linarith
    have hdiag : Y.IsDiag := by simp [IsDiag, Pairwise, Fin.forall_fin_two, h01, h10]
    exact hne (eq_zero_of_isDiag_of_trace_eq_zero_of_det_eq_zero_fin_two hdiag htr hdet)
  -- Solve `a² = Y₀₁`, `c² = -Y₁₀`, `a c = -Y₀₀`, then complete `(a, c)` to an element of
  -- `SL(2, ℝ)`.
  have habs : √(Y 0 1) * √(-Y 1 0) = |Y 0 0| := by
    rw [← Real.sqrt_mul hy, ← hx, Real.sqrt_sq_eq_abs]
  obtain ⟨c, hc, hac⟩ : ∃ c : ℝ, c ^ 2 = -Y 1 0 ∧ √(Y 0 1) * c = -Y 0 0 := by
    rcases le_or_gt (Y 0 0) 0 with h | h
    · exact ⟨√(-Y 1 0), Real.sq_sqrt (by linarith), by rw [habs, abs_of_nonpos h]⟩
    · exact ⟨-√(-Y 1 0), by rw [neg_sq, Real.sq_sqrt (by linarith)],
        by rw [mul_neg, habs, abs_of_pos h]⟩
  have ha : √(Y 0 1) ^ 2 = Y 0 1 := Real.sq_sqrt hy
  refine ⟨⟨!![√(Y 0 1), -c / (Y 0 1 - Y 1 0); c, √(Y 0 1) / (Y 0 1 - Y 1 0)], ?_⟩, ?_⟩
  · rw [det_fin_two_of]
    field_simp
    linear_combination ha + hc
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [hac, ha, hc, h11]

/-- **The conjugation orbit of `E = [[0, 1], [0, 0]]` in `SL(2, ℝ)`** is one half of the punctured
nilpotent cone: the nonzero trace-zero matrices of determinant zero with `Y₀₁ ≥ 0 ≥ Y₁₀`. -/
theorem range_coe_mul_single_mul_coe_inv :
    Set.range (fun g : SL(2, ℝ) ↦ (g : Matrix (Fin 2) (Fin 2) ℝ) * single 0 1 1 *
        ((g⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ)) =
      {Y | Y.trace = 0 ∧ Y.det = 0 ∧ Y ≠ 0 ∧ 0 ≤ Y 0 1 ∧ Y 1 0 ≤ 0} := by
  ext Y
  simp only [Set.mem_range, Set.mem_ofPred_eq, coe_mul_single_mul_coe_inv]
  constructor
  · rintro ⟨g, rfl⟩
    have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
      rw [← det_fin_two]
      exact g.property
    refine ⟨by simp [trace_fin_two], by simp [det_fin_two]; ring, fun h ↦ ?_, by simp [sq_nonneg],
      by simp [sq_nonneg]⟩
    have h0 : g 0 0 = 0 := by simpa using congrFun (congrFun h 0) 1
    have h1 : g 1 0 = 0 := by simpa using congrFun (congrFun h 1) 0
    simp [h0, h1] at hdet
  · rintro ⟨htr, hdet, hne, hy, hz⟩
    exact exists_eq_of_trace_eq_zero_of_det_eq_zero htr hdet hne hy hz

/-- The conjugation orbit of `-E` in `SL(2, ℝ)` is the other half of the punctured nilpotent cone,
the matrices with `Y₀₁ ≤ 0 ≤ Y₁₀`. -/
theorem range_coe_mul_neg_single_mul_coe_inv :
    Set.range (fun g : SL(2, ℝ) ↦ (g : Matrix (Fin 2) (Fin 2) ℝ) * -single 0 1 1 *
        ((g⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ)) =
      {Y | Y.trace = 0 ∧ Y.det = 0 ∧ Y ≠ 0 ∧ Y 0 1 ≤ 0 ∧ 0 ≤ Y 1 0} := by
  ext Y
  have h := Set.ext_iff.mp range_coe_mul_single_mul_coe_inv (-Y)
  simpa [det_neg, neg_eq_iff_eq_neg] using h

end SpecialLinearGroup

end Matrix
