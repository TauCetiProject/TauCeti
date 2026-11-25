/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Separation.Hausdorff

/-!
# Avoiding finitely many points is an open condition

In a `T1Space` the complement of a point is open (Mathlib's `isOpen_ne`). Intersecting finitely
many such complements and pulling back along a continuous map shows that the points where a
continuous map into a `T1Space` avoids finitely many given values form an open set
(`TauCeti.isOpen_forall_ne`). For instance, the real coordinates of the complex plane minus
finitely many points form an open subset of `ℝ × ℝ`. In a Hausdorff space the values may also move
continuously: on an open set where the map and the values are continuous, the points where the map
avoids the values form an open set (`TauCeti.isOpen_setOf_mem_and_forall_ne`).
-/

public section

namespace TauCeti

/-- The points where a continuous map into a `T1Space` avoids finitely many values `c i` form an
open set. -/
theorem isOpen_forall_ne {X Y ι : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T1Space Y]
    [Finite ι] {f : X → Y} (hf : Continuous f) {c : ι → Y} :
    IsOpen {x : X | ∀ i, f x ≠ c i} := by
  rw [Set.ofPred_forall]
  exact isOpen_iInter_of_finite fun _ ↦ isOpen_ne.preimage hf

/-- On an open set `U`, the points where a map `f` into a Hausdorff space avoids finitely many
values `g x i`, with `f` and `g` continuous on `U`, form an open set. -/
theorem isOpen_setOf_mem_and_forall_ne {X Y ι : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space Y] [Finite ι] {U : Set X} (hU : IsOpen U) {f : X → Y} (hf : ContinuousOn f U)
    {g : X → ι → Y} (hg : ContinuousOn g U) :
    IsOpen {x | x ∈ U ∧ ∀ i, f x ≠ g x i} := by
  have hO : IsOpen {r : Y × (ι → Y) | ∀ i, r.1 ≠ r.2 i} := by
    rw [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun i ↦
      isOpen_ne_fun continuous_fst ((continuous_apply i).comp continuous_snd)
  exact (hf.prodMk hg).isOpen_inter_preimage hU hO

end TauCeti
