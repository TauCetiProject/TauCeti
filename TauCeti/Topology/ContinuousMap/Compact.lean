/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Topology.ContinuousMap.Ordered
import Mathlib.Tactic.FieldSimp

/-!
# Uniform positivity of continuous functions

The continuous real-valued functions bounded below by a positive constant form a convex set.
On a compact domain this set is open for the uniform topology. These facts apply, for example,
to separating positive continuous functions in the proof of Pietsch domination.

A continuous linear functional on `C(X, ℝ)` that is bounded above by some `u ≤ 0` on the
uniformly positive functions is nonpositive on every nonnegative function: adding a small positive
constant to a nonnegative function makes it uniformly positive. This is the positivity of the
functional produced by separating the uniformly positive functions from a cone.

## Main results

* `ContinuousMap.convex_uniformlyPositive`: the uniformly positive functions form a convex set.
* `ContinuousMap.isOpen_uniformlyPositive`: on a compact space they form an open set.
* `ContinuousLinearMap.apply_nonpos_of_forall_uniformlyPositive_lt`: a functional bounded above
  by `u ≤ 0` on the uniformly positive functions is nonpositive on the nonnegative functions.
-/

public section

open Metric

namespace ContinuousMap

/-- The continuous real functions uniformly bounded below by a positive constant form a
convex set. -/
theorem convex_uniformlyPositive {X : Type*} [TopologicalSpace X] :
    Convex ℝ {h : C(X, ℝ) | ∃ δ > 0, ∀ x, δ ≤ h x} := by
  rintro h₁ ⟨δ₁, hδ₁, h₁δ⟩ h₂ ⟨δ₂, hδ₂, h₂δ⟩ a b ha hb hab
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun f ↦ ?_⟩
  have e₁ := (min_le_left δ₁ δ₂).trans (h₁δ f)
  have e₂ := (min_le_right δ₁ δ₂).trans (h₂δ f)
  simp only [ContinuousMap.add_apply, ContinuousMap.smul_apply, smul_eq_mul]
  calc
    min δ₁ δ₂ = a * min δ₁ δ₂ + b * min δ₁ δ₂ := by rw [← add_mul, hab, one_mul]
    _ ≤ a * h₁ f + b * h₂ f := by gcongr

/-- Uniform positivity is open in the uniform topology on continuous functions
on a compact space. -/
theorem isOpen_uniformlyPositive {X : Type*} [TopologicalSpace X] [CompactSpace X] :
    IsOpen {h : C(X, ℝ) | ∃ δ > 0, ∀ x, δ ≤ h x} := by
  refine Metric.isOpen_iff.2 ?_
  rintro h ⟨δ, hδ, hhδ⟩
  refine ⟨δ / 2, half_pos hδ, fun h' hh' ↦ ⟨δ / 2, half_pos hδ, fun f ↦ ?_⟩⟩
  have := (ContinuousMap.dist_apply_le_dist (f := h') (g := h) f).trans (mem_ball.1 hh').le
  rw [Real.dist_eq] at this
  linarith [hhδ f, (abs_le.1 this).1]

end ContinuousMap

namespace ContinuousLinearMap

/-- A continuous linear functional on `C(X, ℝ)` that is bounded above by some `u ≤ 0` on the
functions bounded below by a positive constant is nonpositive on the nonnegative functions. -/
theorem apply_nonpos_of_forall_uniformlyPositive_lt {X : Type*} [TopologicalSpace X]
    (L : StrongDual ℝ C(X, ℝ)) {u : ℝ} (hu : u ≤ 0)
    (hL : ∀ h ∈ {h : C(X, ℝ) | ∃ δ > 0, ∀ x, δ ≤ h x}, L h < u) {h : C(X, ℝ)} (hh : 0 ≤ h) :
    L h ≤ 0 := by
  have hL1 : L 1 < 0 := (hL 1 ⟨1, one_pos, fun _ ↦ le_rfl⟩).trans_le hu
  -- `h + ε • 1` is bounded below by `ε`, so `L h + ε L 1 < 0`, for every `ε > 0`.
  by_contra! hpos
  have hε : 0 < L h / -L 1 := div_pos hpos (neg_pos.2 hL1)
  have hmem : h + (L h / -L 1) • (1 : C(X, ℝ)) ∈ {h : C(X, ℝ) | ∃ δ > 0, ∀ x, δ ≤ h x} :=
    ⟨_, hε, fun x ↦ by simpa using hh x⟩
  have hlt := (hL _ hmem).trans_le hu
  rw [map_add, map_smul, smul_eq_mul] at hlt
  have hcancel : L h / -L 1 * L 1 = -L h := by field_simp [hL1.ne]
  linarith

end ContinuousLinearMap
