/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Measure
public import Mathlib.MeasureTheory.Function.L1Space.Integrable

import Mathlib.Analysis.Convex.Continuous
import Mathlib.Topology.Order.Compact

/-!
# Compact sublevels from an integrable exponential of a convex potential

If a finite convex potential `φ : E → ℝ` on a finite-dimensional real normed space has
integrable `exp (-φ)`, its sublevel sets are compact and it attains a global minimum.
There is no normalization or previously assumed coercivity, and dimension zero is included.

Integrability bounds the Haar measure of every sublevel. A larger sublevel with nonempty
interior is bounded by `MeasureTheory.Measure.isBounded_iff_measure_ne_top_of_convex`, so
all closed sublevels are compact. Minimizing over the nonempty sublevel through the origin
then gives a global minimum.

## References

* Brayden Letwin, *The KLS constant is O(log^(1/4) n)*, arXiv:2607.24164v1, opening sentence
  of the proof of Lemma A.4. The normalization there implies the integrability used here.
* Adapted from `human-ai-mathematics/kls-lean` at commit
  `33fff6ea218ae07e42115bd1eacfcf7d39c534cb`,
  `formalization/FunctionalInequalities/Analysis/Convex/Coercivity.lean`.
-/

public section

open MeasureTheory Set

namespace ConvexOn

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {φ : E → ℝ}

/-- An integrable exponential of a finite convex potential makes every sublevel compact. -/
theorem isCompact_sublevel_of_integrable_exp_neg (hφ : ConvexOn ℝ univ φ)
    (m : Measure E) [m.IsAddHaarMeasure] (hint : Integrable (fun x => Real.exp (-φ x)) m)
    (c : ℝ) : IsCompact {x | φ x ≤ c} := by
  have hcont : Continuous φ := continuousOn_univ.mp (hφ.continuousOn isOpen_univ)
  have hlevel_finite (d : ℝ) : m {x | φ x ≤ d} < ⊤ := by
    apply lt_of_le_of_lt (measure_mono ?_) (hint.measure_ge_lt_top (Real.exp_pos (-d)))
    intro x hx
    exact Real.exp_le_exp.mpr (neg_le_neg hx)
  let d : ℝ := max c (φ 0 + 1)
  have hcd : c ≤ d := le_max_left _ _
  have hzero : φ (0 : E) < d := by
    have hd : φ (0 : E) + 1 ≤ d := le_max_right _ _
    linarith
  have hopen : IsOpen {x | φ x < d} := isOpen_lt hcont continuous_const
  have hi : (interior {x | φ x ≤ d}).Nonempty := by
    refine ⟨0, mem_interior_iff_mem_nhds.mpr ?_⟩
    exact Filter.mem_of_superset (hopen.mem_nhds hzero) fun x (hx : φ x < d) => hx.le
  have hconv : Convex ℝ {x | φ x ≤ d} := by simpa using hφ.convex_le d
  have hbd := (m.isBounded_iff_measure_ne_top_of_convex hconv hi).2 (hlevel_finite d).ne
  apply Metric.isCompact_of_isClosed_isBounded (isClosed_le hcont continuous_const)
  exact hbd.subset fun _ hx => hx.trans hcd

/-- A finite convex potential with integrable exponential attains a global minimum. -/
theorem exists_isMinOn_of_integrable_exp_neg (hφ : ConvexOn ℝ univ φ)
    (m : Measure E) [m.IsAddHaarMeasure] (hint : Integrable (fun x => Real.exp (-φ x)) m) :
    ∃ x, IsMinOn φ univ x := by
  have hcont : Continuous φ := continuousOn_univ.mp (hφ.continuousOn isOpen_univ)
  obtain ⟨x, hx, hmin⟩ :=
    (hφ.isCompact_sublevel_of_integrable_exp_neg m hint (φ 0)).exists_isMinOn
      ⟨0, le_refl (φ (0 : E))⟩ hcont.continuousOn
  refine ⟨x, fun y _ => ?_⟩
  by_cases hy : φ y ≤ φ 0
  · exact hmin hy
  · exact hx.trans (le_of_lt (lt_of_not_ge hy))

end ConvexOn
