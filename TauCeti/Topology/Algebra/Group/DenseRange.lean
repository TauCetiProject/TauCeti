/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.Image
public import Mathlib.Topology.Algebra.Group.Neighborhood

/-!
# Finite approximation along dense maps

A dense map into a topological additive group approximates a finite set in both directions,
while retaining prescribed small elements in the source. A separate element can be
approximated in the same neighbourhood. This supplies the finite data for perturbing
rational presentations, with padding chosen to generate an open ideal or contain a unit.

The approximation uses Mathlib's `mem_closure_iff_nhds_zero`.
-/

public section

namespace TauCeti

open Topology

open scoped Classical in
/-- A finite set containing zero and a separate element admit approximations along a dense map,
within a neighbourhood of zero. The approximating finite set may be required to contain
any prescribed finite set whose image lies in that neighbourhood. Both directions of
approximation are retained, so adjoining these small elements introduces no new bounds. -/
theorem exists_finset_superset_forall_sub_mem_of_denseRange {R B : Type*}
    [AddGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B]
    {φ : R → B} (hφ : DenseRange φ) {V : Set B} (hV : V ∈ 𝓝 0) {T : Finset B}
    (hT : 0 ∈ T) (S : Finset R) (hS : ∀ x ∈ S, φ x ∈ V) (s : B) :
    ∃ (T' : Finset R) (s' : R), S ⊆ T' ∧
      (∀ t ∈ T, ∃ u ∈ T'.image φ, t - u ∈ V) ∧
      (∀ u ∈ T'.image φ, ∃ t ∈ T, u - t ∈ V) ∧ s - φ s' ∈ V := by
  classical
  have happrox : ∀ b : B, ∃ x : R, φ x - b ∈ V ∧ b - φ x ∈ V := fun b ↦ by
    simpa using mem_closure_iff_nhds_zero.mp (hφ b) _
      (Filter.inter_mem hV (neg_mem_nhds_zero B hV))
  choose a ha ha' using happrox
  refine ⟨T.image a ∪ S, a s, by simp, fun t ht ↦ ⟨φ (a t), by grind, ha' t⟩,
    fun u hu ↦ ?_, ha' s⟩
  simp only [Finset.mem_image, Finset.mem_union] at hu
  -- The prescribed small elements are close to zero, which belongs to the target set.
  obtain ⟨x, ⟨t, ht, rfl⟩ | hx, rfl⟩ := hu
  exacts [⟨t, ht, ha t⟩, ⟨0, hT, by simpa using hS x hx⟩]

end TauCeti
