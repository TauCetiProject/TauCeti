/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Topology.MetricSpace.Thickening
import TauCeti.Analysis.SpecialFunctions.Pow.Bounds

/-!
# Cauchy's estimate in a sector

Discs whose radii are a fixed multiple of the distance of their centers to the vertex, centered
at the points of a closed sector `|arg z| ≤ θ'`, stay inside every larger open sector
`|arg w| < θ`: this follows from compactness of the arc of unit directions of the closed sector.
On such discs the norms are comparable to the norm of the center, so Cauchy's estimate for the
derivative turns a power bound `‖f w‖ ≤ B ‖w‖ ^ ν` on the open sector into the bound
`‖f' z‖ ≤ K B ‖z‖ ^ (ν - 1)` on the closed subsector, with `K` depending only on the sectors
and `ν`.

## Main results

* `Complex.exists_pos_forall_closedBall_abs_arg_lt_of_le_pi`,
  `Complex.exists_pos_forall_closedBall_abs_arg_lt`: discs of radius proportional to the norm of
  their centers in a closed sector stay in a larger open sector.
* `Complex.exists_pos_norm_deriv_le_of_sector_bound`: a power bound in an open sector gives a
  derivative bound with the next lower power in a closed subsector.

The statements and proofs are adapted from the lean-DLMF project
(<https://github.com/bjbraams/lean-DLMF>), file `DLMFMathlib/Analysis/Complex/Sector.lean`, where
the sectors may have any bisector.
-/

public section

noncomputable section

open Metric Set
open scoped Real

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

namespace Complex

/-- For `θ' < θ ≤ π`, the closed balls of radius `c ‖z‖` around the points `z ≠ 0` of the closed
sector `|arg z| ≤ θ'` stay in the open sector `|arg w| < θ`, for some `0 < c ≤ 1 / 2`. -/
theorem exists_pos_forall_closedBall_abs_arg_lt_of_le_pi {θ θ' : ℝ} (hθ : θ ≤ π)
    (hθ' : θ' < θ) : ∃ c > 0, c ≤ 1 / 2 ∧ ∀ z : ℂ, z ≠ 0 → |z.arg| ≤ θ' →
      ∀ w ∈ closedBall z (c * ‖z‖), |w.arg| < θ := by
  let K : Set ℂ := (fun φ : ℝ => exp (φ * I)) '' Icc (-θ') θ'
  let U : Set ℂ := slitPlane ∩ (fun z : ℂ => |z.arg|) ⁻¹' Iio θ
  have hK : IsCompact K := isCompact_Icc.image (by fun_prop)
  have hU : IsOpen U := continuousOn_arg.abs.isOpen_inter_preimage isOpen_slitPlane isOpen_Iio
  have hKU : K ⊆ U := by
    rintro _ ⟨φ, hφ, rfl⟩
    have ha : (exp (φ * I)).arg = φ := by
      rw [arg_exp_mul_I, toIocMod_eq_self]
      constructor <;> linarith [hφ.1, hφ.2]
    refine ⟨mem_slitPlane_iff_arg.mpr ⟨by linarith [hφ.2], exp_ne_zero _⟩, ?_⟩
    rw [Set.mem_preimage, ha, Set.mem_Iio, abs_lt]
    constructor <;> linarith [hφ.1, hφ.2]
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hU hKU
  refine ⟨min δ (1 / 2), lt_min hδ (by norm_num), min_le_right _ _,
    fun z hz harg w hw => ?_⟩
  have hz0 : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hzr : (‖z‖ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hz0.ne'
  rw [mem_closedBall, dist_eq_norm] at hw
  have hunit : z / (‖z‖ : ℂ) ∈ K := by
    refine ⟨z.arg, abs_le.mp harg, ?_⟩
    rw [eq_div_iff hzr, mul_comm, norm_mul_exp_arg_mul_I]
  have hdist : dist (w / (‖z‖ : ℂ)) (z / (‖z‖ : ℂ)) ≤ δ := by
    rw [dist_eq_norm, ← sub_div, norm_div, norm_real, Real.norm_of_nonneg hz0.le]
    exact ((div_le_iff₀ hz0).mpr hw).trans (min_le_left _ _)
  have hwU := (hδU (mem_cthickening_of_dist_le _ _ _ K hunit hdist)).2
  rwa [Set.mem_preimage, Set.mem_Iio, div_eq_mul_inv, ← ofReal_inv,
    arg_mul_ofReal _ (inv_pos.mpr hz0)] at hwU

/-- For `θ' < θ`, the closed balls of radius `c ‖z‖` around the points `z ≠ 0` of the closed
sector `|arg z| ≤ θ'` stay in the open sector `|arg w| < θ`, for some `c > 0`, and the norms in
these balls lie between `‖z‖ / 2` and `2 ‖z‖`. -/
theorem exists_pos_forall_closedBall_abs_arg_lt {θ θ' : ℝ} (hθ' : θ' < θ) :
    ∃ c > 0, ∀ z : ℂ, z ≠ 0 → |z.arg| ≤ θ' → ∀ w ∈ closedBall z (c * ‖z‖),
      |w.arg| < θ ∧ ‖z‖ / 2 ≤ ‖w‖ ∧ ‖w‖ ≤ 2 * ‖z‖ := by
  obtain ⟨c, hc, hc2, h⟩ : ∃ c > 0, c ≤ 1 / 2 ∧ ∀ z : ℂ, z ≠ 0 → |z.arg| ≤ θ' →
      ∀ w ∈ closedBall z (c * ‖z‖), |w.arg| < θ := by
    rcases le_or_gt θ π with hθ | hθ
    · exact exists_pos_forall_closedBall_abs_arg_lt_of_le_pi hθ hθ'
    · exact ⟨1 / 2, by norm_num, le_rfl, fun _ _ _ w _ => (abs_arg_le_pi w).trans_lt hθ⟩
  refine ⟨c, hc, fun z hz harg w hw => ⟨h z hz harg w hw, ?_⟩⟩
  rw [mem_closedBall, dist_eq_norm] at hw
  have hnear : ‖w - z‖ ≤ ‖z‖ / 2 := hw.trans (by nlinarith [norm_nonneg z])
  have h1 := norm_le_norm_add_norm_sub z w
  have h2 := norm_le_norm_add_norm_sub w z
  rw [norm_sub_rev] at h1
  constructor <;> linarith

/-- **Cauchy's estimate in a sector.** For `θ' < θ` there is `K > 0` such that every `f`
holomorphic on `{A < ‖w‖, |arg w| < θ}` and bounded there by `B ‖w‖ ^ ν` satisfies
`‖f' z‖ ≤ K B ‖z‖ ^ (ν - 1)` for `2 max A 0 < ‖z‖` and `|arg z| ≤ θ'`. The constant does not
depend on `f`, `A` or `B`. -/
theorem exists_pos_norm_deriv_le_of_sector_bound {θ θ' : ℝ} (hθ' : θ' < θ) (ν : ℝ) :
    ∃ K > 0, ∀ (f : ℂ → E) (A B : ℝ),
      DifferentiableOn ℂ f {w | A < ‖w‖ ∧ |w.arg| < θ} →
      (∀ w, A < ‖w‖ → |w.arg| < θ → ‖f w‖ ≤ B * ‖w‖ ^ ν) →
      ∀ z : ℂ, 2 * max A 0 < ‖z‖ → |z.arg| ≤ θ' → ‖deriv f z‖ ≤ K * B * ‖z‖ ^ (ν - 1) := by
  obtain ⟨c, hc, hb⟩ := exists_pos_forall_closedBall_abs_arg_lt hθ'
  refine ⟨2 ^ |ν| / c, by positivity, fun f A B hf hbound z hz harg => ?_⟩
  have hz0 : 0 < ‖z‖ := by linarith [le_max_right A 0]
  have hzne : z ≠ 0 := norm_pos_iff.mp hz0
  have hB : 0 ≤ B := nonneg_of_mul_nonneg_left
    ((norm_nonneg _).trans (hbound z (by linarith [le_max_left A 0]) (harg.trans_lt hθ')))
    (Real.rpow_pos_of_pos hz0 ν)
  have hsub : closedBall z (c * ‖z‖) ⊆ {w | A < ‖w‖ ∧ |w.arg| < θ} := fun w hw => by
    have h := hb z hzne harg w hw
    exact ⟨by linarith [le_max_left A 0, h.2.1], h.1⟩
  have hd := norm_deriv_le_of_forall_mem_sphere_norm_le (mul_pos hc hz0)
    (hf.diffContOnCl_ball hsub) (C := B * 2 ^ |ν| * ‖z‖ ^ ν) fun w hw => by
      have hwc := sphere_subset_closedBall hw
      have h := hb z hzne harg w hwc
      calc ‖f w‖ ≤ B * ‖w‖ ^ ν := hbound w (hsub hwc).1 h.1
        _ ≤ B * (2 ^ |ν| * ‖z‖ ^ ν) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_two_rpow_abs_mul h.2.1 h.2.2) hB
        _ = B * 2 ^ |ν| * ‖z‖ ^ ν := by ring
  refine hd.trans_eq ?_
  rw [Real.rpow_sub hz0, Real.rpow_one]
  field_simp

end Complex
