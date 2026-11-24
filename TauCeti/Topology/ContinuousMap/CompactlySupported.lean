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

A real linear functional on `C_c(X, F)` that is bounded above on the fields of norm at most one
supported in a set `K` is bounded in absolute value by a constant times the sup norm on all fields
supported in `K` (`CompactlySupportedContinuousMap.exists_abs_le_mul_of_forall_le`).
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

/-- A one-sided bound of a real linear functional `L` on the fields of norm at most one supported
in `K` bounds `|L f|` by a constant times any pointwise bound on a field `f` supported in `K`. -/
theorem exists_abs_le_mul_of_forall_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {L : C_c(X, F) →ₗ[ℝ] ℝ} {K : Set X}
    (hK : ∃ C : ℝ, ∀ f : C_c(X, F), tsupport f ⊆ K → (∀ x, ‖f x‖ ≤ 1) → L f ≤ C) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : C_c(X, F), tsupport f ⊆ K → ∀ c : ℝ, 0 ≤ c → (∀ x, ‖f x‖ ≤ c) →
      |L f| ≤ C * c := by
  obtain ⟨C, hC⟩ := hK
  refine ⟨max C 0, le_max_right _ _, fun f hfK c hc hfc => ?_⟩
  rcases hc.eq_or_lt with rfl | hc0
  · simp [show f = 0 from ext fun x => norm_le_zero_iff.1 (hfc x)]
  -- Rescale `f` by `± c⁻¹` to a field of norm at most one.
  have hunit (s : ℝ) (hs : |s| = c⁻¹) : s * L f ≤ max C 0 := by
    rw [← smul_eq_mul, ← map_smul]
    refine (hC (s • f) ?_ fun x => ?_).trans (le_max_left _ _)
    · rw [coe_smul]
      exact (closure_mono (Function.support_const_smul_subset s _)).trans hfK
    rw [smul_apply, norm_smul, Real.norm_eq_abs, hs, inv_mul_le_one₀ hc0]
    exact hfc x
  have h₁ := (inv_mul_le_iff₀ hc0).1 (hunit c⁻¹ (abs_of_pos (inv_pos.2 hc0)))
  have h₂ := (inv_mul_le_iff₀ hc0).1
    (by simpa using hunit (-c⁻¹) (by rw [abs_neg, abs_of_pos (inv_pos.2 hc0)]) :
      c⁻¹ * -L f ≤ max C 0)
  rw [abs_le]
  constructor <;> linarith

/-- A function dominated by a multiple of the indicator of `Icc a b` vanishes off `Icc a b`. -/
theorem eq_zero_of_enorm_le_indicator [Preorder X] {E : Type*} [NormedAddGroup E]
    {f : C_c(X, E)} {C : ℝ≥0} {a b x : X}
    (hf : ∀ y, ‖f y‖ₑ ≤ (Icc a b).indicator (fun _ ↦ (C : ℝ≥0∞)) y) (hx : x ∉ Icc a b) :
    f x = 0 := by
  simpa [indicator_of_notMem hx] using hf x

end CompactlySupportedContinuousMap
