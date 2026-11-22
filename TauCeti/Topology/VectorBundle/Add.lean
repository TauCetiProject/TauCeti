/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.VectorBundle.Basic

/-!
# Fibrewise addition on a topological vector bundle

The fibrewise sum of two continuous maps into the total space of a topological vector bundle over a
common, possibly varying, base map is continuous (`ContinuousWithinAt.add_totalSpace`,
`ContinuousAt.add_totalSpace`, `Continuous.add_totalSpace`). In a linear trivialization near the
base image, fibrewise addition reduces to addition in the model fibre.
-/

public section

open Bundle Filter

section MovingBase

variable {𝕜 B F : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {E : B → Type*}
  [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜 (E x)] [∀ x, TopologicalSpace (E x)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle 𝕜 F E]

variable {Y : Type*} [TopologicalSpace Y] {b : Y → B} {s t : ∀ y, E (b y)}
  {u : Set Y} {y₀ : Y}

variable (𝕜) in
include 𝕜 in
/-- The fibrewise sum of maps into a vector bundle over a common, possibly varying, base map,
both continuous at a point within a set, is continuous there. -/
theorem ContinuousWithinAt.add_totalSpace
    (hs : ContinuousWithinAt (fun y ↦ TotalSpace.mk' F (b y) (s y)) u y₀)
    (ht : ContinuousWithinAt (fun y ↦ TotalSpace.mk' F (b y) (t y)) u y₀) :
    ContinuousWithinAt (fun y ↦ TotalSpace.mk' F (b y) (s y + t y)) u y₀ := by
  rw [FiberBundle.continuousWithinAt_totalSpace] at hs ht ⊢
  let e := trivializationAt F E (b y₀)
  have hy₀ : b y₀ ∈ e.baseSet := mem_baseSet_trivializationAt F E (b y₀)
  refine ⟨hs.1, (hs.2.add ht.2).congr_of_eventuallyEq ?_
    ((e.linear 𝕜 hy₀).map_add (s y₀) (t y₀))⟩
  filter_upwards [hs.1.eventually (e.open_baseSet.mem_nhds hy₀)] with y hy
  exact (e.linear 𝕜 hy).map_add (s y) (t y)

variable (𝕜) in
include 𝕜 in
/-- The fibrewise sum of maps into a vector bundle over a common, possibly varying, base map,
both continuous at a point, is continuous there. -/
theorem ContinuousAt.add_totalSpace
    (hs : ContinuousAt (fun y ↦ TotalSpace.mk' F (b y) (s y)) y₀)
    (ht : ContinuousAt (fun y ↦ TotalSpace.mk' F (b y) (t y)) y₀) :
    ContinuousAt (fun y ↦ TotalSpace.mk' F (b y) (s y + t y)) y₀ := by
  rw [← continuousWithinAt_univ] at hs ht ⊢
  exact hs.add_totalSpace 𝕜 ht

variable (𝕜) in
include 𝕜 in
/-- The fibrewise sum of continuous maps into a vector bundle over a common, possibly
varying, base map is continuous. -/
theorem Continuous.add_totalSpace
    (hs : Continuous (fun y ↦ TotalSpace.mk' F (b y) (s y)))
    (ht : Continuous (fun y ↦ TotalSpace.mk' F (b y) (t y))) :
    Continuous (fun y ↦ TotalSpace.mk' F (b y) (s y + t y)) :=
  continuous_iff_continuousAt.2 fun _ ↦ hs.continuousAt.add_totalSpace 𝕜 ht.continuousAt

end MovingBase
