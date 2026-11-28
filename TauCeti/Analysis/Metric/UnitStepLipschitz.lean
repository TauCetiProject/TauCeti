/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Tactic.Linarith

/-!
# Global Lipschitz continuity from bounded-step increments on a half-line

A function `f : ℝ → E` into a seminormed additive commutative group whose increments over
steps of length at most `δ > 0` on `[a, ∞)` satisfy `‖f v - f u‖ ≤ L * (v - u)` is globally
`L`-Lipschitz on `[a, ∞)` and grows at most linearly from `f a`.

## Provenance

Adapted from `grh-lean` (<https://github.com/lsernau/grh-lean>, Apache 2.0, Copyright 2026
Anthropic, PBC), commit `72fead102f663d5c7a407964a13dc0cf9d977207`, specifically
`New.abs_sub_le_of_unit_steps` in `grh/src/Lib/Analytic/PrimeNumberTheorem/Tauberian.lean`,
generalized from `ℝ → ℝ` on `[0, ∞)` with step `1` to any `SeminormedAddCommGroup` on
`[a, ∞)` with arbitrary step `δ > 0`.
-/

public section

open Set

namespace TauCeti

variable {E : Type*} [SeminormedAddCommGroup E] {f : ℝ → E} {a δ L : ℝ}

/-- If `‖f v - f u‖ ≤ L * (v - u)` whenever `a ≤ u ≤ v ≤ u + δ` with `0 < δ`, then
`‖f v - f u‖ ≤ L * |v - u|` for all `u, v ≥ a`. -/
theorem norm_sub_le_of_unit_steps (hδ : 0 < δ)
    (h_step : ∀ u v : ℝ, a ≤ u → u ≤ v → v ≤ u + δ → ‖f v - f u‖ ≤ L * (v - u))
    {u v : ℝ} (hu : a ≤ u) (hv : a ≤ v) :
    ‖f v - f u‖ ≤ L * |v - u| := by
  have hle : ∀ n : ℕ, ∀ x y : ℝ, a ≤ x → x ≤ y → y ≤ x + (n + 1 : ℕ) * δ →
      ‖f y - f x‖ ≤ L * (y - x) := by
    intro n
    induction n with
    | zero =>
      intro x y hx hxy hy
      exact h_step x y hx hxy (by simpa using hy)
    | succ k ih =>
      intro x y hx hxy hy
      rcases le_total y (x + δ) with hy' | hy'
      · exact h_step x y hx hxy hy'
      · have h1 := h_step x (x + δ) hx (by linarith) le_rfl
        have h2 := ih (x + δ) y (by linarith) hy' (by push_cast at hy ⊢; linarith)
        have htri : ‖f y - f x‖ ≤ ‖f y - f (x + δ)‖ + ‖f (x + δ) - f x‖ := by
          simpa [sub_add_sub_cancel] using norm_add_le (f y - f (x + δ)) (f (x + δ) - f x)
        linarith
  rcases le_total u v with huv | hvu
  · rw [abs_of_nonneg (sub_nonneg.mpr huv)]
    have hlt : (v - u) / δ < (⌊(v - u) / δ⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    exact hle ⌊(v - u) / δ⌋₊ u v hu huv (by
      have := (div_lt_iff₀ hδ).mp hlt
      push_cast
      linarith)
  · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hvu), norm_sub_rev]
    have hlt : (u - v) / δ < (⌊(u - v) / δ⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    exact hle ⌊(u - v) / δ⌋₊ v u hv hvu (by
      have := (div_lt_iff₀ hδ).mp hlt
      push_cast
      linarith)

/-- If `‖f v - f u‖ ≤ L * (v - u)` whenever `a ≤ u ≤ v ≤ u + δ` with `0 < δ`, then `f` is
`L`-Lipschitz on `[a, ∞)`. -/
theorem lipschitzOnWith_Ici_of_unit_steps (hδ : 0 < δ)
    (h_step : ∀ u v : ℝ, a ≤ u → u ≤ v → v ≤ u + δ → ‖f v - f u‖ ≤ L * (v - u)) :
    ∃ hL : 0 ≤ L, LipschitzOnWith ⟨L, hL⟩ f (Ici a) := by
  have hL : 0 ≤ L := by
    have h0 := (norm_nonneg (f (a + δ) - f a)).trans
      (h_step a (a + δ) le_rfl (by linarith) le_rfl)
    rw [add_sub_cancel_left] at h0
    exact nonneg_of_mul_nonneg_left h0 hδ
  refine ⟨hL, LipschitzOnWith.of_dist_le_mul fun x hx y hy ↦ ?_⟩
  rw [dist_eq_norm, Real.dist_eq]
  exact norm_sub_le_of_unit_steps hδ h_step hy hx

/-- If `‖f v - f u‖ ≤ L * (v - u)` whenever `a ≤ u ≤ v ≤ u + δ` with `0 < δ`, then
`‖f v‖ ≤ ‖f a‖ + L * (v - a)` for all `v ≥ a`. -/
theorem norm_le_add_mul_of_unit_steps (hδ : 0 < δ)
    (h_step : ∀ u v : ℝ, a ≤ u → u ≤ v → v ≤ u + δ → ‖f v - f u‖ ≤ L * (v - u))
    {v : ℝ} (hv : a ≤ v) :
    ‖f v‖ ≤ ‖f a‖ + L * (v - a) := by
  have hsub := norm_sub_le_of_unit_steps hδ h_step le_rfl hv
  rw [abs_of_nonneg (sub_nonneg.mpr hv)] at hsub
  have htri : ‖f v‖ ≤ ‖f v - f a‖ + ‖f a‖ := by
    simpa [sub_add_cancel] using norm_add_le (f v - f a) (f a)
  linarith

end TauCeti
