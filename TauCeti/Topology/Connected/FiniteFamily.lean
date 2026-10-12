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

A continuous function taking its values in a finite family of continuous functions which are
pointwise distinct must choose the same member throughout a connected parameter space.
This is useful for comparing different continuous labellings of simple roots: agreement at
one parameter forces agreement everywhere.

Locally, distinctness can be replaced by persistence of collisions: if every family member
agreeing with the chosen member at the central parameter continues to agree nearby, a
continuous selection agrees with that member on a neighborhood.
-/

public section

open Set

namespace TauCeti

/-- A continuous selection from a finite continuous family agrees locally with a chosen
member if their values agree at the central parameter and collisions with that member
persist nearby. Members with different central values are separated by continuity. -/
theorem eventuallyEq_of_continuousAt_mem_range {B Y ι : Type*} [TopologicalSpace B]
    [TopologicalSpace Y] [T2Space Y] [Finite ι] {r : ι → B → Y} {f : B → Y} {b₀ : B}
    (hr : ∀ j, ContinuousAt (r j) b₀) (hf : ContinuousAt f b₀)
    (hmem : ∀ᶠ b in nhds b₀, f b ∈ Set.range (fun j ↦ r j b)) {i : ι}
    (h₀ : r i b₀ = f b₀)
    (hcollision : ∀ j, r j b₀ = r i b₀ → r j =ᶠ[nhds b₀] r i) :
    r i =ᶠ[nhds b₀] f := by
  have hsep : ∀ᶠ b in nhds b₀, ∀ j, r j b = f b → r j b = r i b := by
    rw [Filter.eventually_all]
    intro j
    by_cases hj : r j b₀ = r i b₀
    · exact (hcollision j hj).mono fun _ hb _ ↦ hb
    · have hne : r j b₀ ≠ f b₀ := by rwa [← h₀]
      exact ((hr j).ne_iff_eventually_ne hf).mp hne |>.mono fun _ hb heq ↦ (hb heq).elim
  filter_upwards [hmem, hsep] with b hb hsb
  obtain ⟨j, hj⟩ := hb
  exact (hsb j hj).symm.trans hj

/-- A continuous choice from finitely many pointwise distinct continuous functions on a
preconnected space agrees everywhere with the member it chooses at one point. -/
theorem eq_of_continuous_mem_range {B Y ι : Type*} [TopologicalSpace B]
    [PreconnectedSpace B] [TopologicalSpace Y] [T2Space Y] [Finite ι]
    {r : ι → B → Y} {f : B → Y} (hr : ∀ i, Continuous (r i)) (hf : Continuous f)
    (hinj : ∀ b, Function.Injective (fun i => r i b))
    (hmem : ∀ b, f b ∈ range (fun i => r i b)) (b₀ : B) {i : ι}
    (h₀ : r i b₀ = f b₀) : r i = f := by
  have heq : {b | r i b = f b} = ⋂ j, {b | j ≠ i → r j b ≠ f b} := by
    ext b
    simp only [mem_ofPred_eq, mem_iInter]
    constructor
    · intro hb j hji hj
      exact hji (hinj b (hj.trans hb.symm))
    · intro hb
      obtain ⟨j, hj⟩ := hmem b
      have hji : j = i := by
        by_contra hne
        exact hb j hne hj
      simpa [hji] using hj
  have hopen : IsOpen {b | r i b = f b} := by
    rw [heq]
    refine isOpen_iInter_of_finite fun j => ?_
    by_cases hji : j = i
    · simp [hji]
    · simpa [hji] using isOpen_ne_fun (hr j) hf
  have hcl : IsClopen {b | r i b = f b} := ⟨isClosed_eq (hr i) hf, hopen⟩
  have hall := hcl.eq_univ ⟨b₀, h₀⟩
  exact funext fun b => by
    have hb : b ∈ {b | r i b = f b} := by rw [hall]; exact mem_univ b
    exact hb

end TauCeti
