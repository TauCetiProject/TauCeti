/-
Copyright (c) 2026 The Tau Ceti contributors and Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Jon Crall, GPT-6
-/
module

public import Mathlib.Topology.ContinuousMap.CompactlySupported
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Topology.Order.Compact

/-!
# Maps on compactly supported continuous functions

Order and `nnrealPart` lemmas for Mathlib's `CompactlySupportedContinuousMap.toReal`, the map
`C_c(X, ℝ≥0) → C_c(X, ℝ)`: it sends `0` to `0`, it is an order embedding, and on nonnegative
functions it is inverse to `CompactlySupportedContinuousMap.nnrealPart`.

The forgetful map from compactly supported to continuous functions preserves
addition and constant scalar multiplication whenever those operations are defined.

On a linearly ordered domain, a compactly supported continuous function is dominated by a
constant multiple of the indicator of a closed interval.
-/

public section

open Set
open scoped ENNReal NNReal CompactlySupported

namespace CompactlySupportedContinuousMap

variable {X : Type*} [TopologicalSpace X]

/-- Forgetting compact support preserves addition. -/
@[simp]
theorem toContinuousMap_add {Y : Type*} [TopologicalSpace Y]
    [AddZeroClass Y] [ContinuousAdd Y] (f g : C_c(X, Y)) :
    (f + g).toContinuousMap = f.toContinuousMap + g.toContinuousMap :=
  rfl

/-- Forgetting compact support preserves scalar multiplication. -/
@[simp]
theorem toContinuousMap_smul {R Y : Type*} [TopologicalSpace Y]
    [Zero Y] [SMulZeroClass R Y] [ContinuousConstSMul R Y]
    (r : R) (f : C_c(X, Y)) :
    (r • f).toContinuousMap = r • f.toContinuousMap :=
  rfl

/-- `toReal` sends the zero function to the zero function. -/
@[simp]
lemma toReal_zero : (0 : C_c(X, ℝ≥0)).toReal = 0 := by
  ext x
  simp

/-- `toReal` is an order embedding. -/
@[simp]
lemma toReal_le_toReal_iff {f g : C_c(X, ℝ≥0)} : f.toReal ≤ g.toReal ↔ f ≤ g := by
  simp [le_def]

/-- On a nonnegative function, `toReal` is a left inverse of `nnrealPart`; compare
`nnrealPart_toReal_eq`. -/
lemma toReal_nnrealPart_of_nonneg {f : C_c(X, ℝ)} (hf : 0 ≤ f) :
    f.nnrealPart.toReal = f := by
  ext x
  simpa using le_def.1 hf x

section Order

variable [LinearOrder X] [ClosedIicTopology X] [ClosedIciTopology X] [Nonempty X]
  {E : Type*} [NormedAddGroup E]

/-- On a linearly ordered domain, a compactly supported continuous function is dominated by a
constant multiple of the indicator of a closed interval. -/
theorem exists_enorm_le_indicator (f : C_c(X, E)) :
    ∃ (C : ℝ≥0) (a b : X), ∀ y, ‖f y‖ₑ ≤ (Icc a b).indicator (fun _ ↦ (C : ℝ≥0∞)) y := by
  obtain ⟨C, hC⟩ := (map_continuous f).bounded_above_of_compact_support f.hasCompactSupport
  obtain ⟨a, ha⟩ := f.hasCompactSupport.isCompact.bddBelow
  obtain ⟨b, hb⟩ := f.hasCompactSupport.isCompact.bddAbove
  refine ⟨C.toNNReal, a, b, fun y ↦ ?_⟩
  by_cases hy : y ∈ tsupport f
  · rw [indicator_of_mem (show y ∈ Icc a b from ⟨ha hy, hb hy⟩), ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hC y)
  · simp [image_eq_zero_of_notMem_tsupport hy]

end Order

end CompactlySupportedContinuousMap
