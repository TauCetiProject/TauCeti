/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.RandomMatrix.Wigner.Basic
public import TauCeti.Analysis.Matrix.ConstantOffDiagonal

/-!
# Centering Wigner matrices

Subtracting a constant from the upper entries gives a constant Hermitian off-diagonal
perturbation. The operator norm of this perturbation is at most the norm of the constant
times the square root of the dimension.
-/

public section

noncomputable section

namespace TauCeti

variable {Ω : Type*}

/-- Centering only the upper entries changes a Wigner matrix by the constant-upper-entry
Hermitian matrix with upper entry `c / √n`. The identity also holds at dimension zero. -/
theorem wignerMatrix_eq_center_add_hermitianOffDiagonal
    (ξ : StrictUpper → Ω → ℂ) (η : ℕ → Ω → ℝ) (c : ℂ) (n : ℕ) (ω : Ω) :
    wignerMatrix ξ η n ω = wignerMatrix (fun ij ω ↦ ξ ij ω - c) η n ω +
      hermitianOffDiagonal ((Real.sqrt n)⁻¹ • c) n := by
  ext i j
  rw [Matrix.add_apply]
  rcases lt_trichotomy i.val j.val with h | h | h
  · simp only [wignerMatrix_apply_of_lt _ _ _ h,
      hermitianOffDiagonal_apply_of_lt _ (Fin.mk_lt_mk.mpr h), Complex.real_smul]
    push_cast
    ring
  · obtain rfl := Fin.ext h
    simp
  · simp only [wignerMatrix_apply_of_gt _ _ _ h,
      hermitianOffDiagonal_apply_of_gt _ (Fin.mk_lt_mk.mpr h), star_sub,
      star_smul, star_trivial]
    simp only [Complex.real_smul]
    push_cast
    ring

open scoped Matrix.Norms.L2Operator in
/-- Subtracting a common constant from the upper entries changes the normalized Wigner
matrix by at most `√n * ‖c‖` in operator norm. -/
theorem l2_opNorm_wignerMatrix_sub_center_le
    (ξ : StrictUpper → Ω → ℂ) (η : ℕ → Ω → ℝ) (c : ℂ) (n : ℕ) (ω : Ω) :
    ‖wignerMatrix ξ η n ω - wignerMatrix (fun ij ω' ↦ ξ ij ω' - c) η n ω‖ ≤
      Real.sqrt n * ‖c‖ := by
  rw [wignerMatrix_eq_center_add_hermitianOffDiagonal ξ η c n ω, add_sub_cancel_left]
  refine (l2_opNorm_hermitianOffDiagonal_le _ _).trans_eq ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.2 (Nat.cast_pos.2 (Nat.pos_of_ne_zero hn))
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hs.le), ← mul_assoc]
  congr 1
  exact (mul_inv_eq_iff_eq_mul₀ hs.ne').2 (by rw [← pow_two, Real.sq_sqrt (Nat.cast_nonneg _)])

end TauCeti
