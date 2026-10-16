/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Factorial.Basic

/-!
# Factorials tend to zero in every p-adic field

The integers `n!` converge to zero at every finite place, although none is zero. This provides
one sequence of rational parameters that simultaneously contracts every local unipotent
one-parameter subgroup. Divisibility by each fixed prime power suffices for the convergence.
-/

public section

namespace TauCeti

open Filter Topology

/-- The factorials, viewed in a fixed p-adic field, tend to zero. -/
theorem tendsto_padic_natCast_factorial (p : ℕ) [hp : Fact p.Prime] :
    Tendsto (fun n : ℕ ↦ (n.factorial : ℚ_[p])) atTop (𝓝 0) := by
  have hpow : Tendsto (fun k : ℕ ↦ (p : ℝ)⁻¹ ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity)
      (inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt))
  refine Metric.tendsto_atTop.mpr fun ε hε ↦ ?_
  obtain ⟨k, hk⟩ := (hpow.eventually (gt_mem_nhds hε)).exists
  refine ⟨p ^ k, fun n hn ↦ ?_⟩
  have hd : (p : ℤ) ^ k ∣ (n.factorial : ℤ) := by
    exact_mod_cast Nat.dvd_factorial (pow_pos hp.out.pos _) hn
  have hnorm := (Padic.norm_int_le_pow_iff_dvd (p := p) (n.factorial : ℤ) k).mpr hd
  simp only [Int.cast_natCast, zpow_neg, zpow_natCast, ← inv_pow] at hnorm
  simpa only [dist_zero_right] using hnorm.trans_lt hk

end TauCeti
