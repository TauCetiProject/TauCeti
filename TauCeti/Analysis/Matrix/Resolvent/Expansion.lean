/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Resolvent.Basic
public import TauCeti.Analysis.Matrix.Trace.Rank

import TauCeti.Topology.Instances.Matrix

/-!
# Quadratic expansion of Hermitian resolvents

The trace remainder of the second-order expansion in a Hermitian perturbation is bounded
uniformly in the background matrix, with a factor proportional to the perturbation rank.
The bound is quadratic for large perturbations and cubic for small perturbations.
-/

public section

open scoped Matrix.Norms.L2Operator

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The trace error of the quadratic resolvent expansion is bounded by rank times the
square of the perturbation norm, with an additional factor linear in that norm for small
perturbations. The bound is uniform in the Hermitian background matrix. -/
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
  have hd : S - R = -(R * B * S) := by
    have h := hA.inv_sub_smul_one_sub_inv_sub_smul_one hAB hz hz
    simpa [R, S, neg_sub] using congrArg Neg.neg h
  have hexpand :
      S - (R - R * B * R + R * B * R * B * R) = R * B * R * B * (S - R) := by
    calc
      _ = (S - R) + R * B * R - R * B * R * B * R := by noncomm_ring
      _ = -(R * B * (S - R)) - R * B * R * B * R := by
        nth_rw 1 [hd]
        noncomm_ring
      _ = R * B * R * B * S - R * B * R * B * R := by
        congr 1
        rw [hd]
        noncomm_ring
      _ = R * B * R * B * (S - R) := (mul_sub _ _ _).symm
  have hr : ‖R‖ ≤ b := hA.l2_opNorm_inv_sub_smul_one_le hz
  have hs : ‖S‖ ≤ b := hAB.l2_opNorm_inv_sub_smul_one_le hz
  have hdiff : ‖S - R‖ ≤ min (b * ‖B‖) 1 * b := by
    rw [min_mul_of_nonneg _ _ (by positivity : 0 ≤ b), one_mul]
    refine le_min ?_ (hAB.l2_opNorm_inv_sub_smul_one_sub_le hA hz)
    rw [hd, norm_neg]
    exact (norm_mul_le _ _).trans (by gcongr; exact (norm_mul_le _ _).trans (by gcongr))
  have hrank : (R * B * R * B * (S - R)).rank ≤ B.rank :=
    (rank_mul_le_left _ _).trans (rank_mul_le_right _ _)
  have hp : ‖R * B * R * B‖ ≤ b * ‖B‖ * b * ‖B‖ := by
    exact norm_mul_le_of_le (norm_mul_le_of_le (norm_mul_le_of_le hr le_rfl) hr) le_rfl
  calc
    _ = ‖(R * B * R * B * (S - R)).trace‖ := by rw [hexpand]
    _ ≤ B.rank * (b * ‖B‖ * b * ‖B‖ * (min (b * ‖B‖) 1 * b)) := by
      refine (norm_trace_le_rank_mul_l2_opNorm _).trans ?_
      gcongr
      exact (norm_mul_le _ _).trans (by gcongr)
    _ = _ := by dsimp only [b]; ring

end Matrix

/-- The trace of the resolvent of a continuous Hermitian matrix family is continuous at a
fixed nonreal spectral parameter. -/
theorem Continuous.matrix_trace_inv_sub_smul_one {X n 𝕜 : Type*} [TopologicalSpace X]
    [Fintype n] [DecidableEq n] [RCLike 𝕜] {A : X → Matrix n n 𝕜}
    (hc : Continuous A) (hA : ∀ x, (A x).IsHermitian)
    {z : 𝕜} (hz : RCLike.im z ≠ 0) :
    Continuous (fun x ↦ (A x - z • 1)⁻¹.trace) := by
  apply Continuous.matrix_trace
  refine continuous_iff_continuousAt.2 fun x ↦ ?_
  exact (hc.sub continuous_const).continuousAt.matrix_inv
    (isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp
      ((hA x).isUnit_sub_smul_one_of_im_ne_zero hz)))
