/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Order.Interval.Set.UnorderedInterval
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# Truncations of a path in `L∞`

For a path `A` with values in a normed group and a time `t`, the truncation `s ↦ A (min s t)`
follows `A` up to time `t` and then stays at `A t`. This file studies the `L∞` classes of the
truncations as functions of `t`, for an arbitrary measure on the time axis.

## Main results

* `MeasureTheory.Lp.continuous_of_forall_ae_eq_apply_min`: for a continuous path on `ℝ`, the
  truncations depend continuously on `t` in `L∞`.
* `MeasureTheory.Lp.tendsto_atTop_of_forall_ae_eq_apply_min`: if the path has a limit at `∞`,
  the truncations converge in `L∞` to the path itself as `t → ∞`.
* `MeasureTheory.Lp.tendsto_atBot_of_forall_ae_eq_apply_min`: if the path has limit `B` at `-∞`,
  the truncations converge in `L∞` to the constant `B` as `t → -∞`.
-/

public section

namespace MeasureTheory.Lp

open Filter Set
open scoped ENNReal Topology

variable {α E : Type*} [NormedAddCommGroup E]

section LinearOrder

variable [MeasurableSpace α] [LinearOrder α] [Nonempty α] {μ : Measure α} {A : α → E}
  {AT : α → Lp E ∞ μ}

/-- As `t → ∞`, the `L∞` classes of the truncations `s ↦ A (min s t)` of a path with a limit at
`∞` converge to the class of the path itself. -/
theorem tendsto_atTop_of_forall_ae_eq_apply_min {B : E} (htop : Tendsto A atTop (𝓝 B))
    {AL : Lp E ∞ μ} (hAL : AL =ᵐ[μ] A) (hAT : ∀ t, AT t =ᵐ[μ] fun s ↦ A (min s t)) :
    Tendsto AT atTop (𝓝 AL) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 htop (ε / 3) (by positivity)
  refine ⟨N, fun t ht ↦ ?_⟩
  rw [_root_.dist_eq_norm]
  refine lt_of_le_of_lt (b := 2 * ε / 3) ?_ (by linarith)
  refine norm_sub_le_of_ae_eq_of_ae_norm_sub_le (hAT t) hAL (by positivity)
    (.of_forall fun s ↦ ?_)
  rcases le_total s t with hs | hs
  · rw [min_eq_left hs, sub_self, _root_.norm_zero]
    positivity
  · rw [min_eq_right hs, ← _root_.dist_eq_norm]
    linarith [dist_triangle_right (A t) (A s) B, hN t ht, hN s (ht.trans hs)]

/-- As `t → -∞`, the `L∞` classes of the truncations `s ↦ A (min s t)` of a path with limit `B`
at `-∞` converge to the class of the constant `B`. -/
theorem tendsto_atBot_of_forall_ae_eq_apply_min {B : E} (hbot : Tendsto A atBot (𝓝 B))
    (hAT : ∀ t, AT t =ᵐ[μ] fun s ↦ A (min s t)) :
    Tendsto AT atBot (𝓝 ((memLp_top_const (μ := μ) B).toLp _)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atBot.1 (Metric.tendsto_nhds.1 hbot (ε / 2) (by positivity))
  refine eventually_atBot.2 ⟨N, fun t ht ↦ ?_⟩
  rw [_root_.dist_eq_norm]
  refine lt_of_le_of_lt (b := ε / 2) ?_ (by linarith)
  refine norm_sub_le_of_ae_eq_of_ae_norm_sub_le (hAT t) (memLp_top_const B).coeFn_toLp
    (by positivity) (.of_forall fun s ↦ ?_)
  rw [← _root_.dist_eq_norm]
  exact (hN _ ((min_le_right s t).trans ht)).le

end LinearOrder

/-- For a continuous path `A` on `ℝ`, the `L∞` classes of the truncations `s ↦ A (min s t)`
depend continuously on `t`. -/
theorem continuous_of_forall_ae_eq_apply_min {μ : Measure ℝ} {A : ℝ → E} {AT : ℝ → Lp E ∞ μ}
    (hA : Continuous A) (hAT : ∀ t, AT t =ᵐ[μ] fun s ↦ A (min s t)) : Continuous AT := by
  rw [Metric.continuous_iff]
  intro t₀ ε hε
  obtain ⟨δ, hδ, hAδ⟩ := Metric.continuousAt_iff.1 hA.continuousAt (ε / 3) (by positivity)
  refine ⟨δ, hδ, fun t ht ↦ ?_⟩
  rw [_root_.dist_eq_norm]
  refine lt_of_le_of_lt (b := 2 * ε / 3) ?_ (by linarith)
  refine norm_sub_le_of_ae_eq_of_ae_norm_sub_le (hAT t) (hAT t₀) (by positivity)
    (.of_forall fun s ↦ ?_)
  by_cases hs : s ≤ t ∧ s ≤ t₀
  · rw [min_eq_left hs.1, min_eq_left hs.2, sub_self, _root_.norm_zero]
    positivity
  -- Otherwise both truncation times lie between `t` and `t₀`, hence near `t₀`.
  have hlow : min t t₀ ≤ s := by
    by_contra h
    exact hs ⟨(lt_of_not_ge h).le.trans (min_le_left _ _),
      (lt_of_not_ge h).le.trans (min_le_right _ _)⟩
  have hnear {u : ℝ} (hu : u ∈ uIcc t t₀) : dist (A u) (A t₀) < ε / 3 := by
    refine hAδ ((Real.dist_eq _ _).trans_lt ?_)
    rw [abs_sub_comm]
    exact (abs_sub_right_of_mem_uIcc hu).trans_lt (by rwa [abs_sub_comm, ← Real.dist_eq])
  have h₁ := hnear (u := min s t) ⟨le_min hlow inf_le_left, (min_le_right s t).trans le_sup_left⟩
  have h₂ := hnear (u := min s t₀) ⟨le_min hlow inf_le_right,
    (min_le_right s t₀).trans le_sup_right⟩
  rw [← _root_.dist_eq_norm]
  linarith [dist_triangle_right (A (min s t)) (A (min s t₀)) (A t₀)]

end MeasureTheory.Lp
