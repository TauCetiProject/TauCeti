/-
Copyright (c) 2026 The Tau Ceti contributors and Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Jon Crall, GPT-6
-/
module

public import Mathlib.Topology.ContinuousMap.CompactlySupported

/-!
# Maps on compactly supported continuous functions

Order and `nnrealPart` lemmas for Mathlib's `CompactlySupportedContinuousMap.toReal`, the map
`C_c(X, ℝ≥0) → C_c(X, ℝ)`: it sends `0` to `0`, it is an order embedding, and on nonnegative
functions it is inverse to `CompactlySupportedContinuousMap.nnrealPart`.

The forgetful map from compactly supported to continuous functions preserves
addition and constant scalar multiplication whenever those operations are defined.

A compactly supported continuous function on `ℝ` vanishes off a window of natural half-length
around every translation (`CompactlySupportedContinuousMap.exists_natCast_apply_sub_eq_zero`).
-/

public section

open scoped NNReal CompactlySupported

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

/-- A compactly supported continuous function on `ℝ` has translates `y ↦ f (y - c)` vanishing
off a window `[c - R, c + R]` whose half-length `R` is a natural number. -/
theorem exists_natCast_apply_sub_eq_zero (f : C_c(ℝ, ℝ)) :
    ∃ R : ℕ, ∀ y c : ℝ, (y < c - R ∨ c + R < y) → f (y - c) = 0 := by
  obtain ⟨r, -, hr⟩ := f.hasCompactSupport.exists_pos_le_norm
  refine ⟨⌈r⌉₊, fun y c h ↦ hr _ ?_⟩
  rw [Real.norm_eq_abs, le_abs]
  rcases h with h | h
  exacts [Or.inr (by linarith [Nat.le_ceil r]), Or.inl (by linarith [Nat.le_ceil r])]

end CompactlySupportedContinuousMap
