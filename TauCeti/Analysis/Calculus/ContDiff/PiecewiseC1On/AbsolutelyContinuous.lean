/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.ContDiff.PiecewiseC1On
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.Analysis.Calculus.MeanValue
import TauCeti.Order.Interval.Finite

/-!
# Absolute continuity of piecewise `C¹` curves

A piecewise `C¹` curve in a real normed space is Lipschitz on its compact parameter interval, and
hence absolutely continuous. The derivative is bounded by `IsPiecewiseC1On.isBounded_image_deriv`;
the mean value inequality bounds the increment across each `C¹` piece, and the triangle inequality
glues these bounds across the finitely many breakpoints.

## Main results

* `TauCeti.IsPiecewiseC1On.exists_lipschitzOnWith` — a piecewise `C¹` curve is Lipschitz on
  `[[a, b]]`.
* `TauCeti.IsPiecewiseC1On.absolutelyContinuousOnInterval` — a piecewise `C¹` curve is absolutely
  continuous on `[[a, b]]`.
-/

public section

namespace TauCeti

open Set
open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {γ : ℝ → E} {a b : ℝ}

/-- A piecewise `C¹` curve is Lipschitz on its compact parameter interval, including across its
breakpoints. -/
theorem IsPiecewiseC1On.exists_lipschitzOnWith (hγ : IsPiecewiseC1On γ a b) :
    ∃ K : ℝ≥0, LipschitzOnWith K γ (uIcc a b) := by
  obtain ⟨C, hCpos, hC⟩ := hγ.isBounded_image_deriv.exists_pos_norm_le
  obtain ⟨p, -, hC1⟩ := hγ.exists_breakpoints
  let K : ℝ≥0 := ⟨C, hCpos.le⟩
  -- The mean value inequality bounds the increment across each `C¹` piece, and the triangle
  -- inequality glues these bounds across the breakpoints.
  have hinc {x y : ℝ} (hxy : x ≤ y) (hsub : Icc x y ⊆ uIcc a b) :
      dist (γ x) (γ y) ≤ K * (y - x) := by
    refine Icc_induction_of_disjoint_Ioo (p := p)
      (Q := fun c d => dist (γ c) (γ d) ≤ K * (d - c)) (fun c d hcd hsub hdisj => ?_)
      (fun c m d _ _ _ h₁ h₂ => ?_) hxy hsub
    · rcases hcd.eq_or_lt with rfl | hcd
      · simp
      have hlip : LipschitzOnWith K γ (Ioo c d) :=
        (convex_Ioo c d).lipschitzOnWith_of_nnnorm_deriv_le
          (fun t ht => ((hC1 c d hsub hdisj).differentiableOn one_ne_zero).differentiableAt
            (Icc_mem_nhds ht.1 ht.2))
          fun t ht => by
            rw [← NNReal.coe_le_coe, coe_nnnorm]
            exact hC _ ⟨t, hsub (Ioo_subset_Icc_self ht), rfl⟩
      replace hlip := hlip.closure (by rw [closure_Ioo hcd.ne]; exact hγ.continuousOn.mono hsub)
      rw [closure_Ioo hcd.ne] at hlip
      simpa [Real.dist_eq, abs_of_nonpos (sub_nonpos.2 hcd.le)] using
        hlip.dist_le_mul c (left_mem_Icc.2 hcd.le) d (right_mem_Icc.2 hcd.le)
    · calc dist (γ c) (γ d) ≤ dist (γ c) (γ m) + dist (γ m) (γ d) := dist_triangle _ _ _
        _ ≤ K * (m - c) + K * (d - m) := add_le_add h₁ h₂
        _ = K * (d - c) := by ring
  refine ⟨K, lipschitzOnWith_iff_dist_le_mul.mpr fun x hx y hy => ?_⟩
  rcases le_total x y with hxy | hxy
  · rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.2 hxy), neg_sub]
    exact hinc hxy (Icc_subset_uIcc.trans (uIcc_subset_uIcc hx hy))
  · rw [dist_comm, dist_comm x, Real.dist_eq, abs_of_nonpos (sub_nonpos.2 hxy), neg_sub]
    exact hinc hxy (Icc_subset_uIcc.trans (uIcc_subset_uIcc hy hx))

/-- Every piecewise `C¹` curve is absolutely continuous on its parameter interval. -/
theorem IsPiecewiseC1On.absolutelyContinuousOnInterval (hγ : IsPiecewiseC1On γ a b) :
    AbsolutelyContinuousOnInterval γ a b := by
  obtain ⟨K, hK⟩ := hγ.exists_lipschitzOnWith
  exact hK.absolutelyContinuousOnInterval

end TauCeti
