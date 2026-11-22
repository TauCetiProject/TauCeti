/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Measurable sets of strictly increasing families

Strictly increasing families indexed by a countable preorder, such as finite tuples or
sequences, form a measurable set, as do those whose entries all lie in a given measurable
set. The values lie in a preorder whose order is closed for a second-countable topology, as
for the real numbers. These sets describe ordered regions in products.
-/

public section

open Set

namespace TauCeti

variable {ι α : Type*} [Preorder ι] [Countable ι] [Preorder α] [TopologicalSpace α]
  [OrderClosedTopology α] [SecondCountableTopology α] [MeasurableSpace α]
  [OpensMeasurableSpace α]

/-- Strictly increasing families indexed by a countable preorder form a measurable set. -/
theorem measurableSet_setOf_strictMono :
    MeasurableSet {x : ι → α | StrictMono x} := by
  -- `x i < x j` holds on the closed set `x i ≤ x j` minus the closed set `x j ≤ x i`.
  have hlt (i j : ι) : MeasurableSet {x : ι → α | x i < x j} := by
    simp only [lt_iff_le_not_ge, ofPred_and, ← compl_ofPred]
    exact (isClosed_le (continuous_apply i) (continuous_apply j)).measurableSet.inter
      (isClosed_le (continuous_apply j) (continuous_apply i)).measurableSet.compl
  simp only [StrictMono, ofPred_forall]
  exact .iInter fun i => .iInter fun j => .iInter fun _ => hlt i j

/-- Strictly increasing families with every entry in a measurable set `s` form a measurable
set. -/
theorem measurableSet_setOf_strictMono_and_forall_mem {s : Set α} (hs : MeasurableSet s) :
    MeasurableSet {y : ι → α | StrictMono y ∧ ∀ i, y i ∈ s} := by
  simp only [ofPred_and, ofPred_forall]
  exact measurableSet_setOf_strictMono.inter (.iInter fun i => measurable_pi_apply i hs)

end TauCeti
