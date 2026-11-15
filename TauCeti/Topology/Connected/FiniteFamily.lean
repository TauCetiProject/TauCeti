/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Topology.Separation.Hausdorff

/-!
# Continuous choices from a finite family

A continuous function taking its values in a finite family of continuous functions must choose
the same member throughout a connected parameter space, provided that member is pointwise
distinct from all the others. This is useful for comparing different continuous labellings of
simple roots: agreement at one parameter forces agreement everywhere.

Locally, distinctness can be replaced by persistence of collisions: if every family member
agreeing with the chosen member at the central parameter continues to agree nearby, a
continuous selection agrees with that member on a neighborhood.
-/

public section

open Set Topology

namespace TauCeti

/-- A continuous selection from a finite continuous family agrees locally with a chosen
member if their values agree at the central parameter and collisions with that member
persist nearby. -/
theorem eventuallyEq_of_continuousAt_mem_range {B Y ι : Type*} [TopologicalSpace B]
    [TopologicalSpace Y] [T2Space Y] [Finite ι] {r : ι → B → Y} {f : B → Y} {b₀ : B}
    (hr : ∀ j, ContinuousAt (r j) b₀) (hf : ContinuousAt f b₀)
    (hmem : ∀ᶠ b in 𝓝 b₀, f b ∈ range (fun j ↦ r j b)) {i : ι}
    (h₀ : r i b₀ = f b₀)
    (hcollision : ∀ j, r j b₀ = r i b₀ → r j =ᶠ[𝓝 b₀] r i) :
    r i =ᶠ[𝓝 b₀] f := by
  have hsep : ∀ᶠ b in 𝓝 b₀, ∀ j, r j b = f b → r j b = r i b := by
    refine Filter.eventually_all.2 fun j ↦ ?_
    by_cases hj : r j b₀ = r i b₀
    · exact (hcollision j hj).mono fun _ hb _ ↦ hb
    · exact ((hr j).ne_iff_eventually_ne hf).1 (h₀ ▸ hj) |>.mono fun _ hb heq ↦ (hb heq).elim
  filter_upwards [hmem, hsep] with b ⟨j, hj⟩ hsb
  exact (hsb j hj).symm.trans hj

/-- A continuous choice from finitely many continuous functions on a preconnected space agrees
everywhere with the member it chooses at one point, provided that member is pointwise distinct
from all the others. -/
theorem eq_of_continuous_mem_range {B Y ι : Type*} [TopologicalSpace B]
    [PreconnectedSpace B] [TopologicalSpace Y] [T2Space Y] [Finite ι]
    {r : ι → B → Y} {f : B → Y} {i : ι} {b₀ : B} (hr : ∀ j, Continuous (r j))
    (hf : Continuous f) (hdistinct : ∀ b j, r j b = r i b → j = i)
    (hmem : ∀ b, f b ∈ range (fun j ↦ r j b)) (h₀ : r i b₀ = f b₀) : r i = f := by
  have hopen : IsOpen {b | r i b = f b} := isOpen_iff_mem_nhds.2 fun b hb ↦
    eventuallyEq_of_continuousAt_mem_range (fun j ↦ (hr j).continuousAt) hf.continuousAt
      (.of_forall hmem) hb fun j hj ↦ by rw [hdistinct b j hj]
  exact funext <| eq_univ_iff_forall.1 <|
    IsClopen.eq_univ ⟨isClosed_eq (hr i) hf, hopen⟩ ⟨b₀, h₀⟩

end TauCeti
