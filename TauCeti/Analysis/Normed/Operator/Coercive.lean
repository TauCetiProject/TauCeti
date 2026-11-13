/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

import TauCeti.Analysis.Real.Sqrt

/-!
# Positivity of coercive bilinear forms

`IsCoercive.apply_self_pos` extracts the strict diagonal positivity argument shared by
`TauCeti.coerciveRiemannianMetric` and `IsCoercive.pos_of_forall_apply_eq_smul_inner`.
It requires neither symmetry nor finite dimension.
Operator-norm convergence to a coercive form also gives eventual uniform multiplicative
comparison of square roots of diagonal values along any filter. The varying forms need
not be symmetric or coercive.
-/

public section

open Filter
open scoped Topology

namespace IsCoercive

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {B : E →L[ℝ] E →L[ℝ] ℝ}

/-- A coercive form is strictly positive on nonzero diagonal arguments. -/
theorem apply_self_pos (hB : IsCoercive B) {v : E} (hv : v ≠ 0) : 0 < B v v := by
  obtain ⟨c, hc, h⟩ := hB
  exact (mul_pos (mul_pos hc (norm_pos_iff.mpr hv)) (norm_pos_iff.mpr hv)).trans_le (h v)

end IsCoercive

namespace IsCoercive

variable {X : Type*} [SeminormedAddCommGroup X] [NormedSpace ℝ X]

/-- Operator-norm convergence to a coercive form gives uniform multiplicative bounds on the
square roots of diagonal values. No symmetry or positivity assumption on the varying forms
is required. -/
theorem eventually_sqrt_apply_apply_bounds {ι : Type*} {l : Filter ι}
    {B : ι → X →L[ℝ] X →L[ℝ] ℝ} {B₀ : X →L[ℝ] X →L[ℝ] ℝ}
    (h₀ : IsCoercive B₀) (hB : Tendsto B l (𝓝 B₀)) {r : ℝ} (hr : 1 < r) :
    ∀ᶠ s in l, ∀ v : X,
      Real.sqrt (B₀ v v) / r ≤ Real.sqrt (B s v v) ∧
      Real.sqrt (B s v v) ≤ r * Real.sqrt (B₀ v v) := by
  obtain ⟨C, hC, hcoercive⟩ := h₀
  -- Choose an operator-norm error controlled by the smaller square-root margin.
  have hrpos : 0 < r := zero_lt_one.trans hr
  have hri : 0 < r⁻¹ := inv_pos.mpr hrpos
  have hri1 : r⁻¹ < 1 := (inv_lt_one₀ hrpos).mpr hr
  have hd₂ : 0 < 1 - (r⁻¹) ^ 2 := by
    have hs := (sq_lt_sq₀ hri.le zero_le_one).mpr hri1
    nlinarith
  let d : ℝ := 1 - (r⁻¹) ^ 2
  have hd : 0 < d := hd₂
  have hnear : ∀ᶠ s in l, ‖B s - B₀‖ < d * C := by
    have hb := hB (Metric.ball_mem_nhds B₀ (mul_pos hd hC))
    filter_upwards [hb] with s hs
    simp only [Set.mem_preimage, Metric.mem_ball] at hs
    rwa [dist_eq_norm (B s) B₀] at hs
  filter_upwards [hnear] with s hs
  intro v
  -- Coercivity turns the absolute operator-norm error into relative diagonal error.
  have herror : |B s v v - B₀ v v| ≤ d * B₀ v v := calc
    _ = ‖(B s - B₀) v v‖ := by
      simp only [sub_apply, Real.norm_eq_abs]
    _ ≤ ‖B s - B₀‖ * ‖v‖ * ‖v‖ := (B s - B₀).le_opNorm₂ v v
    _ ≤ (d * C) * ‖v‖ * ‖v‖ := by gcongr
    _ = d * (C * ‖v‖ * ‖v‖) := by ring
    _ ≤ d * B₀ v v := mul_le_mul_of_nonneg_left (hcoercive v) hd.le
  exact Real.sqrt_bounds_of_abs_sub_le hr.le herror

end IsCoercive
