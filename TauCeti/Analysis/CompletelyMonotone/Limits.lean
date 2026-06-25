/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Order.MonotoneConvergence
public import TauCeti.Analysis.CompletelyMonotone.Basic

/-!
# Limit at infinity of a completely monotone function

A completely monotone function is nonincreasing on `[0, ∞)` and bounded below by `0`, so it
converges to a nonnegative limit as `t → ∞`. This basic object-API fact extends
`CompletelyMonotone/Basic.lean`.

## Main declarations

* `TauCeti.IsCompletelyMonotone.tendsto_atTop`: `f` has a limit `L ≥ 0` at infinity.

## References

* Roadmap: `TauCetiRoadmap/OneParameterSemigroups/README.md`, Part B (Bernstein theorem milestone).
-/

public section

open Set Filter
open scoped Topology

namespace TauCeti

variable {f : ℝ → ℝ}

namespace IsCompletelyMonotone

/-- A completely monotone function has a limit `L ≥ 0` at infinity: it is antitone on `[0, ∞)`
and bounded below by `0`. -/
lemma tendsto_atTop (hf : IsCompletelyMonotone f) :
    ∃ L, Tendsto f atTop (nhds L) ∧ 0 ≤ L := by
  have hanti := hf.antitoneOn
  set g := fun t : ℝ => f (max t 0) with hg
  have hg_anti : Antitone g := fun a b hab =>
    hanti (mem_Ici.mpr (le_max_right _ _)) (mem_Ici.mpr (le_max_right _ _))
      (max_le_max_right 0 hab)
  have hg_bdd : BddBelow (Set.range g) :=
    ⟨0, fun _ ⟨t, ht⟩ => ht ▸ hf.nonneg (le_max_right _ _)⟩
  refine ⟨⨅ i, g i, ?_, le_ciInf (fun _ => hf.nonneg (le_max_right _ _))⟩
  exact (tendsto_atTop_ciInf hg_anti hg_bdd).congr'
    (eventually_atTop.mpr ⟨0, fun t ht => by simp [hg, max_eq_left ht]⟩)

end IsCompletelyMonotone

end TauCeti
