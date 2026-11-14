/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Analysis.Complex.Polydisc.Division

/-!
# Checks for one-coordinate polydisc bounds

The function `z ↦ z 0 ^ 2` attains the pure-power bound when the large and small radii are
`2` and `1`. A shifted root tests the general product bound, and a vector-valued example checks
that the estimates apply to normed spaces rather than only to scalar-valued functions.
The maximum principle also includes the radius-zero case.
-/

open Metric

-- The pure-power estimate is sharp: the resulting bound at `z 0 = 1` is exactly `1`.
example {z : Fin 1 → ℂ} (hz : z ∈ closedBall 0 1) : ‖z 0 ^ 2‖ ≤ 1 := by
  have hbound (w : Fin 1 → ℂ) (hw : w ∈ closedBall 0 2) : ‖w 0 ^ 2‖ ≤ (4 : ℝ) := by
    rw [norm_pow]
    have hwi : ‖w 0‖ ≤ 2 := (norm_le_pi_norm w 0).trans (by simpa using hw)
    nlinarith [norm_nonneg (w 0)]
  have h := TauCeti.norm_le_mul_pow_of_eq_pow_smul (f := fun z : Fin 1 → ℂ => z 0 ^ 2)
    (g := fun _ => (1 : ℂ)) 0 2 (by norm_num) (by norm_num) (by norm_num)
    (fun _ _ => analyticAt_const) (by simp) hbound hz
  norm_num at h ⊢
  exact h

-- A nonzero root uses the `2 * r / (R - r)` ratio, not the pure-power ratio `r / R`.
example {z : Fin 1 → ℂ} (hz : z ∈ closedBall 0 1) : ‖z 0 - 1‖ ≤ 4 := by
  have hbound (w : Fin 1 → ℂ) (hw : w ∈ closedBall 0 3) : ‖w 0 - 1‖ ≤ (4 : ℝ) := by
    have hwi : ‖w 0‖ ≤ 3 := (norm_le_pi_norm w 0).trans (by simpa using hw)
    calc
      ‖w 0 - 1‖ ≤ ‖w 0‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ ≤ 4 := by simp only [norm_one]; linarith
  have h := TauCeti.norm_le_mul_pow_of_eq_prod_smul (f := fun z : Fin 1 → ℂ => z 0 - 1)
    (g := fun _ => (1 : ℂ)) 0 {1} 1 (by norm_num) (by norm_num)
    (fun _ _ => analyticAt_const) (by simp) (by simp) hbound hz
  norm_num at h
  exact h

-- Division works for vector-valued functions without assuming completeness.
example (v : ℂ × ℂ) {M : ℝ}
    (hbound : ∀ z : Fin 2 → ℂ, z ∈ closedBall 0 2 → ‖z 0 • v‖ ≤ M) : ‖v‖ ≤ M / 2 := by
  simpa using TauCeti.norm_le_of_eq_pow_smul (f := fun z : Fin 2 → ℂ => z 0 • v)
    (g := fun _ => v) 0 1 (by norm_num : (0 : ℝ) < 2)
    (fun _ _ => analyticAt_const) (by simp) hbound (z := 0) (by simp)

-- A radius-zero polydisc consists of its coordinate face as well.
example {f : (Fin 1 → ℂ) → ℂ} (hf : AnalyticOnNhd ℂ f (closedBall 0 0))
    {M : ℝ} (hM : ∀ z ∈ closedBall 0 0, ‖z 0‖ = 0 → ‖f z‖ ≤ M) : ‖f 0‖ ≤ M := by
  exact TauCeti.norm_le_of_forall_norm_coord_eq 0 hf hM (by simp)
