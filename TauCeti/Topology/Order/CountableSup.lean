/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Bases
public import Mathlib.Topology.Order.Basic

/-!
# Countable families realizing a pointwise supremum

For second-countable domain and codomain, a pointwise supremum of continuous functions into a
complete linear order is already the supremum of a countable subfamily. The same subfamily works
at every point. This allows variational suprema to be used in measurability arguments.

The countable-subcover theorem `TopologicalSpace.isOpen_iUnion_countable` is applied to strict
subgraphs in the product of the domain and codomain.
-/

public section

open Set TopologicalSpace

namespace TauCeti

/-- A pointwise supremum of continuous functions between second-countable spaces, with values
in a complete linear order, is realized by a single countable subfamily. -/
theorem exists_countable_iSup_eq_of_continuous {X Y ι : Type*} [TopologicalSpace X]
    [SecondCountableTopology X] [CompleteLinearOrder Y] [TopologicalSpace Y]
    [OrderClosedTopology Y] [SecondCountableTopology Y] {f : ι → X → Y}
    (hf : ∀ i, Continuous (f i)) :
    ∃ C : Set ι, C.Countable ∧ ∀ x, (⨆ i, f i x) = ⨆ i ∈ C, f i x := by
  let U (i : ι) : Set (X × Y) := {p | p.2 < f i p.1}
  obtain ⟨C, hC, hU⟩ := isOpen_iUnion_countable U
    (fun i ↦ isOpen_lt continuous_snd ((hf i).comp continuous_fst))
  refine ⟨C, hC, fun x ↦ le_antisymm ?_ (iSup₂_le fun i _ ↦ le_iSup (fun j ↦ f j x) i)⟩
  refine iSup_le fun i ↦ le_of_forall_lt fun r hr ↦ ?_
  have hp : (x, r) ∈ ⋃ i, U i := mem_iUnion.mpr ⟨i, hr⟩
  rw [← hU] at hp
  obtain ⟨j, hj, hrj⟩ := mem_iUnion₂.mp hp
  exact (hrj : r < f j x).trans_le (le_iSup₂_of_le j hj le_rfl)

end TauCeti
