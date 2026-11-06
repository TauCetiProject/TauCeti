/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Filter.ENNReal
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Limits superior and inferior of sums in `ℝ≥0∞`

Mathlib's `ENNReal.limsup_add_le` asks the filter to be closed under countable intersections, a
hypothesis its proof uses but the statement does not need: the upper limit of a sum of
`ℝ≥0∞`-valued functions is at most the sum of their upper limits along every filter
(`ENNReal.limsup_add_le'`). Neighbourhood filters, along which difference quotients are taken, are
not closed under countable intersections.

Adding a sequence with a finite limit raises the lower limit by that limit
(`ENNReal.le_liminf_add_of_tendsto`).
-/

public section

open Filter Topology
open scoped ENNReal NNReal

namespace ENNReal

variable {α : Type*} {f : Filter α}

/-- The upper limit of a sum of `ℝ≥0∞`-valued functions is at most the sum of their upper limits,
along any filter. -/
theorem limsup_add_le' (u v : α → ℝ≥0∞) : f.limsup (u + v) ≤ f.limsup u + f.limsup v := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε hlt ↦ ?_
  have hε2 : ((ε / 2 : ℝ≥0) : ℝ≥0∞) ≠ 0 := by simpa using hε.ne'
  have hu := eventually_lt_of_limsup_lt (ENNReal.lt_add_right (lt_top_iff_ne_top.1 <|
    (le_self_add.trans_lt hlt)) hε2)
  have hv := eventually_lt_of_limsup_lt (ENNReal.lt_add_right (lt_top_iff_ne_top.1 <|
    (le_add_self.trans_lt hlt)) hε2)
  refine limsup_le_of_le (h := ?_)
  filter_upwards [hu, hv] with a hua hva
  calc (u + v) a ≤ (f.limsup u + (ε / 2 : ℝ≥0)) + (f.limsup v + (ε / 2 : ℝ≥0)) :=
        add_le_add hua.le hva.le
    _ = f.limsup u + f.limsup v + ε := by
        rw [add_add_add_comm, ← ENNReal.coe_add, add_halves]

/-- Adding a sequence `b` with a finite limit `B` raises the lower limit of `A` by at least `B`. -/
theorem le_liminf_add_of_tendsto [f.NeBot] (A b : α → ℝ≥0∞) {B : ℝ≥0∞} (hB : B ≠ ∞)
    (hb : Tendsto b f (𝓝 B)) : liminf A f + B ≤ liminf (fun j => A j + b j) f := by
  have h0 : Tendsto (fun j => B - b j) f (𝓝 0) := by
    simpa only [tsub_self] using ENNReal.Tendsto.sub tendsto_const_nhds hb (Or.inl hB)
  calc liminf A f + B = liminf (fun j => A j + B) f :=
        (liminf_add_const f A B (by isBoundedDefault) (by isBoundedDefault)).symm
    _ ≤ liminf ((fun j => A j + b j) + fun j => B - b j) f :=
        liminf_le_liminf (.of_forall fun j => by
          rw [Pi.add_apply, add_assoc]
          gcongr
          exact le_add_tsub)
    _ = liminf (fun j => A j + b j) f := ENNReal.liminf_add_of_right_tendsto_zero h0 _

end ENNReal
