/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
module

public import TauCeti.Analysis.Complex.GrowthOrder

/-!
# Logarithmic-exponential bounds imply order at most one

A bound by `exp (C (1+‖s‖) log (2+‖s‖))` gives `OrderLE f 1`.
This is the growth comparison used after estimating split Mellin integrals.
-/

public section

open Real Filter Asymptotics Bornology Topology

namespace TauCeti

/-- A global logarithmic-exponential norm bound implies order at most one. -/
theorem orderLE_one_of_norm_le_exp_mul_log {f : ℂ → ℂ} {C : ℝ}
    (hf : ∀ s, ‖f s‖ ≤ exp (C * (1 + ‖s‖) * log (2 + ‖s‖))) : OrderLE f 1 := by
  rw [orderLE_def]
  intro p hp
  have ho := (Real.isLittleO_add_one_mul_log_add_two_rpow hp).const_mul_left C
  apply IsBigO.of_bound 1
  filter_upwards [tendsto_norm_cobounded_atTop.eventually ho.eventuallyLE] with s hs
  simp only [Real.norm_eq_abs] at hs
  rw [Real.norm_eq_abs, abs_of_pos (exp_pos _), one_mul]
  apply (hf s).trans
  apply exp_le_exp.mpr
  have hpow : 0 ≤ ‖s‖ ^ p := Real.rpow_nonneg (norm_nonneg _) _
  rw [abs_of_nonneg hpow] at hs
  calc
    C * (1 + ‖s‖) * log (2 + ‖s‖) ≤ |C * ((1 + ‖s‖) * log (2 + ‖s‖))| := by
      simpa only [mul_assoc] using le_abs_self (C * ((1 + ‖s‖) * log (2 + ‖s‖)))
    _ ≤ ‖s‖ ^ p := hs

end TauCeti
