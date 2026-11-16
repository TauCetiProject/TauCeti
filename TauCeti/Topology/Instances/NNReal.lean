/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Instances.NNReal.Lemmas
public import Mathlib.Topology.Order.WithTop
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Order-topological limits in `ℝ≥0` and `WithTop ι`

This file collects elementary monotone approximations in `ℝ≥0` and `WithTop ι`:
- natural-number casts `(n : WithTop ι)` tend to `⊤` in any unbounded Archimedean ordered
  semiring with the order topology;
- the truncated left shifts `t - 1 / (n + 1 : ℝ≥0)` are monotone and converge to `t` both in `ℝ≥0`
  and after coercion to `WithTop ℝ≥0`;
- strict inequalities `x < (t : WithTop ℝ≥0)` are witnessed by positive dyadic/reciprocal cushions
  `x + 1 / (k + 1) ≤ t`.
-/

public section

open Filter Set
open scoped NNReal Topology

/-- Natural-number casts in `WithTop ι` converge to `⊤` in any unbounded Archimedean ordered
semiring with the order topology. -/
theorem WithTop.tendsto_coe_natCast_atTop {ι : Type*} [Semiring ι] [LinearOrder ι]
    [IsOrderedRing ι] [NoMaxOrder ι] [Archimedean ι] [TopologicalSpace ι] [OrderTopology ι] :
    Tendsto (fun n : ℕ ↦ ((n : ι) : WithTop ι)) atTop (𝓝 ⊤) :=
  WithTop.tendsto_coe_atTop.comp tendsto_natCast_atTop_atTop

namespace NNReal

/-- Truncated left shifts `t - 1 / (n + 1)` form a monotone sequence in `ℝ≥0`. -/
theorem monotone_tsub_one_div_add_one (t : ℝ≥0) :
    Monotone (fun n : ℕ ↦ t - 1 / (n + 1 : ℝ≥0)) := by
  intro m n hmn
  refine tsub_le_tsub_left (one_div_le_one_div_of_le (by positivity) ?_) t
  exact add_le_add_left (Nat.cast_le.mpr hmn) 1

/-- Truncated left shifts `t - 1 / (n + 1)` converge to `t` in `ℝ≥0`. -/
theorem tendsto_tsub_one_div_add_one (t : ℝ≥0) :
    Tendsto (fun n : ℕ ↦ t - 1 / (n + 1 : ℝ≥0)) atTop (𝓝 t) := by
  have hinv_real : Tendsto (fun n : ℕ ↦ (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hinv : Tendsto (fun n : ℕ ↦ (1 : ℝ≥0) / (n + 1 : ℝ≥0)) atTop (𝓝 0) := by
    rw [← NNReal.tendsto_coe]
    simpa using hinv_real
  simpa using tendsto_const_nhds.sub hinv

/-- Truncated left shifts `t - 1 / (n + 1)` coerced to `WithTop ℝ≥0` converge to `t`. -/
theorem tendsto_coe_tsub_one_div_add_one (t : ℝ≥0) :
    Tendsto (fun n : ℕ ↦ ((t - 1 / (n + 1 : ℝ≥0) : ℝ≥0) : WithTop ℝ≥0))
      atTop (𝓝 (t : WithTop ℝ≥0)) :=
  (WithTop.continuous_coe.tendsto t).comp (tendsto_tsub_one_div_add_one t)

/-- A strict upper bound `x < (t : WithTop ℝ≥0)` is witnessed by adding a reciprocal step
`1 / (k + 1)`. -/
theorem lt_coe_iff_exists_add_one_div_add_one_le {x : WithTop ℝ≥0} {t : ℝ≥0} :
    x < (t : WithTop ℝ≥0) ↔
      ∃ k : ℕ, x + ((1 / (k + 1 : ℝ≥0) : ℝ≥0) : WithTop ℝ≥0) ≤ (t : WithTop ℝ≥0) := by
  cases x with
  | top =>
    exact ⟨fun h ↦ (not_top_lt h).elim,
      fun ⟨_, hk⟩ ↦ (WithTop.coe_ne_top (top_le_iff.mp (le_self_add.trans hk))).elim⟩
  | coe u =>
    have hinv : Tendsto (fun k : ℕ ↦ (1 : ℝ≥0) / (k + 1 : ℝ≥0)) atTop (𝓝 0) := by
      rw [← NNReal.tendsto_coe]
      simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have htend : Tendsto (fun k : ℕ ↦ u + 1 / (k + 1 : ℝ≥0)) atTop (𝓝 u) := by
      simpa using tendsto_const_nhds.add hinv
    have hgt (k : ℕ) : u < u + 1 / (k + 1 : ℝ≥0) := lt_add_of_pos_right u (by positivity)
    have hIoi := iUnion_Ici_eq_Ioi_of_lt_of_tendsto hgt htend
    simp only [WithTop.coe_lt_coe, ← WithTop.coe_add, WithTop.coe_le_coe]
    simpa only [mem_iUnion, mem_Ici, mem_Ioi] using (Set.ext_iff.mp hIoi t).symm

end NNReal

end
