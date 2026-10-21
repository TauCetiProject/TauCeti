/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousMap.CompactlySupported

/-!
# The map `toReal` on compactly supported continuous functions

Order and `nnrealPart` lemmas for Mathlib's `CompactlySupportedContinuousMap.toReal`, the map
`C_c(X, ℝ≥0) → C_c(X, ℝ)`: it sends `0` to `0`, it is an order embedding, and on nonnegative
functions it is inverse to `CompactlySupportedContinuousMap.nnrealPart`.
-/

public section

open scoped NNReal CompactlySupported

namespace CompactlySupportedContinuousMap

variable {X : Type*} [TopologicalSpace X]

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

end CompactlySupportedContinuousMap
