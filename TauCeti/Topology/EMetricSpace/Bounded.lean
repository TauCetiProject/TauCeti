/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.EMetricSpace.Diam

/-!
# Families at bounded distance from a point

A family at distance at most `R ≠ ⊤` from a point has range of finite diameter.

## Main results

* `TauCeti.ediam_range_ne_top_of_edist_le`: the range of such a family has finite diameter.
-/

public section

open Set
open scoped ENNReal

namespace TauCeti

variable {X : Type*} [PseudoEMetricSpace X] {x : X}

/-- A family at distance at most `R ≠ ⊤` from a point has range of finite diameter. -/
theorem ediam_range_ne_top_of_edist_le {ι : Type*} {R : ℝ≥0∞} (hR : R ≠ ⊤) {w : ι → X}
    (hw : ∀ i, edist x (w i) ≤ R) : Metric.ediam (range w) ≠ ⊤ := by
  refine ne_top_of_le_ne_top (b := 2 * R) (by finiteness)
    ((Metric.ediam_mono (t := Metric.closedEBall x R) ?_).trans Metric.ediam_closedEBall_le)
  rintro _ ⟨i, rfl⟩
  exact Metric.mem_closedEBall.2 (by rw [edist_comm]; exact hw i)

end TauCeti
