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
constant multiple of the indicator of a closed interval, and such a domination forces it to vanish
off that interval.

A compactly supported continuous function on `X` extends by zero along an open embedding
`e : X → Y` into a Hausdorff space to a compactly supported continuous function on `Y`
(`CompactlySupportedContinuousMap.extendZero`). Every compactly supported continuous function on
`Y` whose support lies in the range of `e` arises this way
(`CompactlySupportedContinuousMap.exists_extendZero_eq`).
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

/-- A function dominated by a multiple of the indicator of `Icc a b` vanishes off `Icc a b`. -/
theorem eq_zero_of_enorm_le_indicator [Preorder X] {E : Type*} [NormedAddGroup E]
    {f : C_c(X, E)} {C : ℝ≥0} {a b x : X}
    (hf : ∀ y, ‖f y‖ₑ ≤ (Icc a b).indicator (fun _ ↦ (C : ℝ≥0∞)) y) (hx : x ∉ Icc a b) :
    f x = 0 := by
  simpa [indicator_of_notMem hx] using hf x

section ExtendZero

open Topology

variable {Y β : Type*} [TopologicalSpace Y] [T2Space Y] [TopologicalSpace β] [Zero β]
  {e : X → Y}

/-- The extension by zero of a compactly supported continuous function along an open embedding
`e` into a Hausdorff space: it agrees with `f` on the range of `e` and vanishes off it. -/
noncomputable def extendZero (he : IsOpenEmbedding e) (f : C_c(X, β)) : C_c(Y, β) where
  toFun := Function.extend e f 0
  continuous_toFun := continuous_of_tsupport fun y hy ↦ by
    obtain ⟨x, -, rfl⟩ := f.hasCompactSupport.tsupport_extend_zero_subset he.continuous hy
    rw [← he.continuousAt_iff, Function.extend_comp he.injective]
    exact f.continuous.continuousAt
  hasCompactSupport' := f.hasCompactSupport.extend_zero he.continuous

/-- The extension by zero is `Function.extend e f 0`. -/
theorem coe_extendZero (he : IsOpenEmbedding e) (f : C_c(X, β)) :
    ⇑(f.extendZero he) = Function.extend e f 0 :=
  (rfl)

/-- The extension by zero agrees with `f` along the embedding. -/
@[simp]
theorem extendZero_apply (he : IsOpenEmbedding e) (f : C_c(X, β)) (x : X) :
    f.extendZero he (e x) = f x :=
  he.injective.extend_apply _ _ x

/-- The extension by zero vanishes off the range of the embedding. -/
theorem extendZero_apply_of_notMem_range (he : IsOpenEmbedding e) (f : C_c(X, β)) {y : Y}
    (hy : y ∉ range e) : f.extendZero he y = 0 :=
  Function.extend_apply' _ _ _ fun ⟨x, hx⟩ ↦ hy ⟨x, hx⟩

/-- A compactly supported continuous function whose support lies in the range of an open
embedding `e` is the extension by zero of a compactly supported continuous function on the domain
of `e`. -/
theorem exists_extendZero_eq (he : IsOpenEmbedding e) (g : C_c(Y, β))
    (hg : tsupport g ⊆ range e) : ∃ f : C_c(X, β), f.extendZero he = g := by
  have hc : HasCompactSupport (g ∘ e) :=
    (he.isInducing.isCompact_preimage' g.hasCompactSupport hg).of_isClosed_subset
      (isClosed_tsupport _) (tsupport_comp_subset_preimage g he.continuous)
  refine ⟨⟨⟨g ∘ e, g.continuous.comp he.continuous⟩, hc⟩, ext fun y ↦ ?_⟩
  by_cases hy : y ∈ range e
  · obtain ⟨x, rfl⟩ := hy
    simp
  · rw [extendZero_apply_of_notMem_range he _ hy,
      image_eq_zero_of_notMem_tsupport fun h ↦ hy (hg h)]

end ExtendZero

end CompactlySupportedContinuousMap
