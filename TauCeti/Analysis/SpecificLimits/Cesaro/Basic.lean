/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Real-cutoff Cesàro means

For a convergent sequence `a : ℕ → E` in a real normed space, the discrete Cesàro theorem
(`Filter.Tendsto.cesaro_smul`) extends immediately to the real-cutoff average
`x⁻¹ • ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n` (`TauCeti.tendsto_inv_smul_sum_Icc_floor`) by asymptotic
equivalence `⌊x⌋₊ ~ x`.

## Main results

* `TauCeti.tendsto_inv_smul_sum_Icc_floor`: real-cutoff Cesàro mean for convergent sequences.
-/

public section

open Filter Finset Topology

namespace TauCeti

/-- A sequence in a normed space converging to `l` has real-cutoff Cesàro mean
`x⁻¹ • ∑ n ∈ Icc 1 ⌊x⌋₊, a n → l`. -/
theorem tendsto_inv_smul_sum_Icc_floor {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a : ℕ → E} {l : E} (ha : Tendsto a atTop (𝓝 l)) :
    Tendsto (fun x : ℝ ↦ x⁻¹ • ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n) atTop (𝓝 l) := by
  have hces' : Tendsto (fun x : ℝ ↦ (⌊x⌋₊ : ℝ)⁻¹ • ∑ n ∈ Finset.range ⌊x⌋₊, a (n + 1))
      atTop (𝓝 l) :=
    (ha.comp (tendsto_add_atTop_nat 1)).cesaro_smul.comp tendsto_nat_floor_atTop
  have hces : Tendsto (fun x : ℝ ↦ (⌊x⌋₊ : ℝ)⁻¹ • ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n)
      atTop (𝓝 l) := by
    simpa only [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel,
      add_comm 1] using hces'
  exact ((Asymptotics.isEquivalent_nat_floor (R := ℝ)).inv.smul
    Asymptotics.IsEquivalent.refl).tendsto_nhds hces

end TauCeti
