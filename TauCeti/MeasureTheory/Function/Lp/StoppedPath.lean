/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Algebra.Order.Group.Pointwise.Interval
import Mathlib.Tactic.Positivity
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# Stopped paths in `L∞`

A path `f : ℝ → E` in a normed group, stopped at time `t`, is the path `s ↦ f (min s t)`. For any
measure `μ` on `ℝ`, this file studies the classes `F t` of the stopped paths in `L∞(μ, E)` as
functions of the stopping time `t`. Since stopping changes the path uniformly in `s`, the
statements hold in the `L∞` distance (the limit statements for paths on any nonempty linear
order):

* if `f` is continuous, then `F` is continuous;
* if `f` tends to `b` at `-∞`, then `F t` tends to the constant class `b` as `t → -∞`;
* if `f` tends to a limit at `∞`, then `F t` tends to the class of `f` as `t → ∞`.

These are the deformations used to show that an index which is locally constant in an `L∞`
coefficient does not change along a path of admissible coefficients.

## Main results

* `TauCeti.continuous_of_ae_eq_comp_min`: the stopped paths of a continuous path depend
  continuously on the stopping time in `L∞`.
* `TauCeti.tendsto_atBot_of_ae_eq_comp_min` and `TauCeti.tendsto_atTop_of_ae_eq_comp_min`: the
  limits of the stopped paths as the stopping time tends to `-∞` and to `∞`.
-/

public section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E]

section Real

variable {μ : Measure ℝ} {f : ℝ → E} {F : ℝ → Lp E ∞ μ}

/-- If `F t` is the class in `L∞` of the continuous path `f` stopped at time `t`, then `F` is
continuous. -/
theorem continuous_of_ae_eq_comp_min (hf : Continuous f)
    (hF : ∀ t, F t =ᵐ[μ] fun s ↦ f (min s t)) : Continuous F := by
  refine Metric.continuous_iff.2 fun t ε hε ↦ ?_
  obtain ⟨δ, hδ, hfδ⟩ := Metric.continuous_iff.1 hf t (ε / 4) (by positivity)
  refine ⟨δ, hδ, fun t' ht' ↦ ?_⟩
  refine (Lp.dist_le_of_ae_dist_le_top (half_pos hε).le ?_).trans_lt (half_lt_self hε)
  filter_upwards [hF t', hF t] with s h' h
  rw [h', h]
  rcases le_total s (min t t') with hs | hs
  · rw [min_eq_left (hs.trans (min_le_right _ _)), min_eq_left (hs.trans (min_le_left _ _)),
      dist_self]
    positivity
  -- Both stopping times lie between `t` and `t'`, so within `δ` of `t`.
  have hclose (r : ℝ) (hr : r ∈ uIcc t t') : dist (f r) (f t) < ε / 4 := by
    rw [Real.dist_eq] at ht'
    exact hfδ r (by rw [Real.dist_eq]; exact (abs_sub_left_of_mem_uIcc hr).trans_lt ht')
  calc dist (f (min s t')) (f (min s t))
      ≤ dist (f (min s t')) (f t) + dist (f (min s t)) (f t) := dist_triangle_right _ _ _
    _ ≤ ε / 4 + ε / 4 := add_le_add
        (hclose _ ⟨le_min hs (min_le_right _ _), (min_le_right _ _).trans (le_max_right _ _)⟩).le
        (hclose _ ⟨le_min hs (min_le_left _ _), (min_le_right _ _).trans (le_max_left _ _)⟩).le
    _ = ε / 2 := by ring

end Real

section LinearOrder

variable {α : Type*} [MeasurableSpace α] [LinearOrder α] [Nonempty α] {μ : Measure α} {f : α → E}
  {F : α → Lp E ∞ μ}

/-- If `F t` is the class in `L∞` of the path `f` stopped at time `t`, and `f` tends to `b` at
`-∞`, then `F t` tends to the constant class `b` as `t → -∞`. -/
theorem tendsto_atBot_of_ae_eq_comp_min {b : E} (hf : Tendsto f atBot (𝓝 b))
    (hF : ∀ t, F t =ᵐ[μ] fun s ↦ f (min s t)) {G : Lp E ∞ μ} (hG : G =ᵐ[μ] fun _ ↦ b) :
    Tendsto F atBot (𝓝 G) := by
  refine Metric.tendsto_nhds.2 fun ε hε ↦ ?_
  obtain ⟨N, hN⟩ := eventually_atBot.1 (Metric.tendsto_nhds.1 hf (ε / 2) (half_pos hε))
  refine eventually_atBot.2 ⟨N, fun t ht ↦ ?_⟩
  refine (Lp.dist_le_of_ae_dist_le_top (half_pos hε).le ?_).trans_lt (half_lt_self hε)
  filter_upwards [hF t, hG] with s h h'
  rw [h, h']
  exact (hN _ ((min_le_right s t).trans ht)).le

/-- If `F t` is the class in `L∞` of the path `f` stopped at time `t`, and `f` has a limit at
`∞`, then `F t` tends to the class of `f` as `t → ∞`. -/
theorem tendsto_atTop_of_ae_eq_comp_min {b : E} (hf : Tendsto f atTop (𝓝 b))
    (hF : ∀ t, F t =ᵐ[μ] fun s ↦ f (min s t)) {G : Lp E ∞ μ} (hG : G =ᵐ[μ] f) :
    Tendsto F atTop (𝓝 G) := by
  refine Metric.tendsto_nhds.2 fun ε hε ↦ ?_
  obtain ⟨N, hN⟩ := eventually_atTop.1 (Metric.tendsto_nhds.1 hf (ε / 4) (by positivity))
  refine eventually_atTop.2 ⟨N, fun t ht ↦ ?_⟩
  refine (Lp.dist_le_of_ae_dist_le_top (half_pos hε).le ?_).trans_lt (half_lt_self hε)
  filter_upwards [hF t, hG] with s h h'
  rw [h, h']
  rcases le_total s t with hst | hst
  · rw [min_eq_left hst, dist_self]
    positivity
  rw [min_eq_right hst]
  calc dist (f t) (f s) ≤ dist (f t) b + dist (f s) b := dist_triangle_right _ _ _
    _ ≤ ε / 4 + ε / 4 := add_le_add (hN t ht).le (hN s (ht.trans hst)).le
    _ = ε / 2 := by ring

end LinearOrder

end TauCeti
