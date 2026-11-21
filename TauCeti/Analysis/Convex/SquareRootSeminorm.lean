/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.Normed.Module.Seminorm.Basic
public import Mathlib.Analysis.Real.Sqrt

/-!
# Seminorms from convex two-homogeneous functions

The square root of a convex function homogeneous of degree two is a seminorm. Such a function is
automatically nonnegative (`TauCeti.nonneg_of_convexOn_smul_sq`).
This construction applies to convex energies without requiring a parallelogram identity;
in particular it applies to Sobolev energies before any Hilbertianity assumption.
-/

public section

open Set

namespace TauCeti

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {Q : E → ℝ}

/-- A convex two-homogeneous function is nonnegative: it vanishes at `0` and is even, so
convexity at the midpoint of `x` and `-x` gives `0 = Q 0 ≤ Q x`. -/
theorem nonneg_of_convexOn_smul_sq (hQ : ConvexOn ℝ univ Q)
    (hsmul : ∀ (c : ℝ) x, Q (c • x) = c ^ 2 * Q x) (x : E) : 0 ≤ Q x := by
  have h0 : Q 0 = 0 := by simpa using hsmul 0 0
  have hneg : Q (-x) = Q x := by simpa using hsmul (-1) x
  have h := hQ.2 (mem_univ x) (mem_univ (-x)) one_half_pos.le one_half_pos.le (add_halves 1)
  rw [← smul_add, add_neg_cancel, smul_zero, h0, hneg, smul_eq_mul] at h
  linarith

/-- The square root of a convex two-homogeneous function is subadditive. -/
theorem sqrt_add_le_of_convexOn_smul_sq (hQ : ConvexOn ℝ univ Q)
    (hsmul : ∀ (c : ℝ) x, Q (c • x) = c ^ 2 * Q x) (x y : E) :
    √(Q (x + y)) ≤ √(Q x) + √(Q y) := by
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  let a := √(Q x) + ε / 2
  let b := √(Q y) + ε / 2
  have ha : 0 < a := add_pos_of_nonneg_of_pos (Real.sqrt_nonneg _) (half_pos hε)
  have hb : 0 < b := add_pos_of_nonneg_of_pos (Real.sqrt_nonneg _) (half_pos hε)
  have hab : 0 < a + b := add_pos ha hb
  have hx : Q (a⁻¹ • x) ≤ 1 := by
    rw [hsmul]
    have hsq := Real.sq_sqrt (nonneg_of_convexOn_smul_sq hQ hsmul x)
    have hle : Q x ≤ a ^ 2 := by
      dsimp [a]
      nlinarith [Real.sqrt_nonneg (Q x)]
    exact (mul_le_mul_of_nonneg_left hle (sq_nonneg a⁻¹)).trans_eq (by field_simp)
  have hy : Q (b⁻¹ • y) ≤ 1 := by
    rw [hsmul]
    have hsq := Real.sq_sqrt (nonneg_of_convexOn_smul_sq hQ hsmul y)
    have hle : Q y ≤ b ^ 2 := by
      dsimp [b]
      nlinarith [Real.sqrt_nonneg (Q y)]
    exact (mul_le_mul_of_nonneg_left hle (sq_nonneg b⁻¹)).trans_eq (by field_simp)
  have h := hQ.2 (mem_univ (a⁻¹ • x)) (mem_univ (b⁻¹ • y))
    (div_nonneg ha.le hab.le) (div_nonneg hb.le hab.le)
    (by field_simp : a / (a + b) + b / (a + b) = 1)
  have heq : (a / (a + b)) • (a⁻¹ • x) + (b / (a + b)) • (b⁻¹ • y) =
      (a + b)⁻¹ • (x + y) := by
    simp only [smul_smul, smul_add]
    congr 1 <;> congr 1 <;> field_simp
  rw [heq, hsmul] at h
  have hle : (a + b)⁻¹ ^ 2 * Q (x + y) ≤ 1 := h.trans <| by
    calc a / (a + b) * Q (a⁻¹ • x) + b / (a + b) * Q (b⁻¹ • y)
        ≤ a / (a + b) * 1 + b / (a + b) * 1 := by gcongr
      _ = 1 := by field_simp
  have hbound : Q (x + y) ≤ (a + b) ^ 2 := by
    have := mul_le_mul_of_nonneg_left hle (sq_nonneg (a + b))
    field_simp at this
    nlinarith
  have hsqrt := (Real.sqrt_le_iff).2 ⟨hab.le, hbound⟩
  dsimp [a, b] at hsqrt
  linarith

/-- The seminorm whose square is a convex two-homogeneous function. -/
noncomputable def squareRootSeminorm (Q : E → ℝ) (hQ : ConvexOn ℝ univ Q)
    (hsmul : ∀ (c : ℝ) x, Q (c • x) = c ^ 2 * Q x) : Seminorm ℝ E :=
  Seminorm.of (fun x ↦ √(Q x)) (sqrt_add_le_of_convexOn_smul_sq hQ hsmul)
    (fun c x ↦ by rw [hsmul, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs, Real.norm_eq_abs])

/-- Evaluation of the square-root seminorm. -/
@[simp]
theorem squareRootSeminorm_apply (hQ : ConvexOn ℝ univ Q)
    (hsmul : ∀ (c : ℝ) x, Q (c • x) = c ^ 2 * Q x) (x : E) :
    squareRootSeminorm Q hQ hsmul x = √(Q x) := (rfl)

end TauCeti
