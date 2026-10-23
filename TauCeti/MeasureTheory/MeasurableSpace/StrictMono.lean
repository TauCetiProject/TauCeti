/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Measurable sets of strictly increasing tuples

Strictly increasing finite tuples form a measurable set, as do those whose entries
lie in a given open interval. These sets describe ordered regions in finite products.
-/

public section

open Set

namespace TauCeti

variable {α : Type*} [LinearOrder α] [TopologicalSpace α] [OrderClosedTopology α]
  [SecondCountableTopology α] [MeasurableSpace α] [OpensMeasurableSpace α] {n : ℕ}

/-- Strictly increasing finite tuples form a measurable set. -/
theorem measurableSet_setOf_strictMono :
    MeasurableSet {x : Fin n → α | StrictMono x} := by
  simp only [StrictMono, ofPred_forall]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
    MeasurableSet.iInter fun _ => measurableSet_lt (measurable_pi_apply i)
      (measurable_pi_apply j)

/-- The strictly increasing tuples in an open interval form a measurable set. -/
theorem measurableSet_strictMono_mem_Ioo (n : ℕ) (a b : α) :
    MeasurableSet {y : Fin n → α | StrictMono y ∧ ∀ i, y i ∈ Ioo a b} := by
  simp only [ofPred_and, ofPred_forall]
  exact measurableSet_setOf_strictMono.inter
    (MeasurableSet.iInter fun i => measurable_pi_apply i measurableSet_Ioo)

end TauCeti
