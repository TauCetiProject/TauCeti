/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Resolvent.Basic
public import TauCeti.Analysis.Matrix.Trace.Rank

import TauCeti.Analysis.Matrix.Resolvent.Stability

/-!
# Quadratic expansion of Hermitian resolvents

At a nonreal spectral parameter, the trace remainder in a Hermitian perturbation is bounded
uniformly in the background matrix, with a factor proportional to the perturbation rank.
The bound is quadratic for large perturbations and cubic for small perturbations.
The exact remainder is given by `Matrix.inv_add_sub_smul_one_sub_quadratic`.
The bound `Matrix.norm_trace_le_rank_mul_l2_opNorm` supplies the rank factor.
-/

public section

open scoped Matrix.Norms.L2Operator

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The trace error of the quadratic resolvent expansion is bounded by rank times the
square of the perturbation norm, with an additional factor linear in that norm for small
perturbations. At a nonreal spectral parameter, the bound is uniform in the Hermitian
background matrix. -/
theorem IsHermitian.norm_trace_inv_add_sub_smul_one_sub_quadratic_le
    {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    {z : ℂ} (hz : z.im ≠ 0) :
    let R := (A - z • 1)⁻¹
    let S := (A + B - z • 1)⁻¹
    ‖(S - (R - R * B * R + R * B * R * B * R)).trace‖ ≤
      B.rank * |z.im|⁻¹ ^ 3 * ‖B‖ ^ 2 * min (|z.im|⁻¹ * ‖B‖) 1 := by
  let R := (A - z • 1)⁻¹
  let S := (A + B - z • 1)⁻¹
  let b := |z.im|⁻¹
  have hAB := hA.add hB
  have hr : ‖R‖ ≤ b := hA.l2_opNorm_inv_sub_smul_one_le hz
  have hdiff : ‖S - R‖ ≤ min (b * ‖B‖) 1 * b := by
    rw [min_mul_of_nonneg _ _ (by positivity : 0 ≤ b), one_mul]
    refine le_min ?_ (hAB.l2_opNorm_inv_sub_smul_one_sub_le hA hz)
    simpa only [R, S, b, RCLike.im_to_complex, add_sub_cancel_left, neg_sub,
      sub_add_cancel_left, zero_sub, norm_neg] using
      hAB.norm_inv_sub_smul_one_sub_inv_sub_smul_one_le_matrix hA hz
  have hrank : (R * B * R * B * (S - R)).rank ≤ B.rank :=
    (rank_mul_le_left _ _).trans (rank_mul_le_right _ _)
  have hp : ‖R * B * R * B‖ ≤ b * ‖B‖ * b * ‖B‖ := by
    exact norm_mul_le_of_le (norm_mul_le_of_le (norm_mul_le_of_le hr le_rfl) hr) le_rfl
  calc
    _ = ‖(R * B * R * B * (S - R)).trace‖ := by
      rw [inv_add_sub_smul_one_sub_quadratic A B z
        (iff_of_true (hA.isUnit_sub_smul_one_of_im_ne_zero hz)
          (hAB.isUnit_sub_smul_one_of_im_ne_zero hz))]
    _ ≤ B.rank * (b * ‖B‖ * b * ‖B‖ * (min (b * ‖B‖) 1 * b)) := by
      refine (norm_trace_le_rank_mul_l2_opNorm _).trans ?_
      gcongr
      exact (norm_mul_le _ _).trans (by gcongr)
    _ = _ := by dsimp only [b]; ring

end Matrix
