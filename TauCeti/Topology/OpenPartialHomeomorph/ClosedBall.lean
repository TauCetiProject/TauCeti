/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.OpenPartialHomeomorph.Continuity

/-!
# Closed balls of a chart covering a compact set

An open partial homeomorphism `φ : M → E` into a pseudometric space pulls closed balls of `E`
back to `M` through `φ.symm`. This file proves that a compact subset `A` of the source of `φ` is
covered by finitely many such balls centred at points of `A`, all lying in the target of `φ` and
pulling back into a given neighbourhood of `A`
(`OpenPartialHomeomorph.exists_finset_closedBall_cover`).
-/

public section

open Metric Set Topology

namespace OpenPartialHomeomorph

variable {M E : Type*} [TopologicalSpace M] [PseudoMetricSpace E]

/-- A compact subset `A` of the source of a chart `φ` is covered by finitely many closed balls of
`φ`, centred at points of `A`, whose images lie in a given neighbourhood `U` of `A`. -/
theorem exists_finset_closedBall_cover (φ : OpenPartialHomeomorph M E) {A U : Set M}
    (hA : IsCompact A) (hAφ : A ⊆ φ.source) (hU : U ∈ 𝓝ˢ A) :
    ∃ (t : Finset M) (r : M → ℝ), (∀ a ∈ t, a ∈ A ∧ 0 < r a ∧
      closedBall (φ a) (r a) ⊆ φ.target ∧ φ.symm '' closedBall (φ a) (r a) ⊆ U) ∧
      A ⊆ φ.symm '' ⋃ a ∈ t, closedBall (φ a) (r a) := by
  have h (a : M) (ha : a ∈ A) : ∃ r > 0, closedBall (φ a) r ⊆ φ.target ∩ φ.symm ⁻¹' U := by
    have ha' := φ.map_source (hAφ ha)
    refine nhds_basis_closedBall.mem_iff.1 (Filter.inter_mem (φ.open_target.mem_nhds ha') ?_)
    refine (φ.continuousAt_symm ha').preimage_mem_nhds ?_
    rw [φ.left_inv (hAφ ha)]
    exact mem_nhdsSet_iff_forall.1 hU a ha
  choose! r hr hrU using h
  obtain ⟨t, htA, hAt⟩ := hA.elim_nhds_subcover (fun a ↦ φ.source ∩ φ ⁻¹' ball (φ a) (r a))
    fun a ha ↦ Filter.inter_mem (φ.open_source.mem_nhds (hAφ ha))
      ((φ.continuousAt (hAφ ha)).preimage_mem_nhds (ball_mem_nhds _ (hr a ha)))
  refine ⟨t, r, fun a ha ↦ ⟨htA a ha, hr a (htA a ha), fun z hz ↦ (hrU a (htA a ha) hz).1, ?_⟩,
    fun x hx ↦ ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact (hrU a (htA a ha) hz).2
  · obtain ⟨hxs, a, ha, hxb⟩ : x ∈ φ.source ∧ ∃ a ∈ t, φ x ∈ ball (φ a) (r a) := by
      simpa using hAt hx
    exact ⟨φ x, mem_biUnion ha (ball_subset_closedBall hxb), φ.left_inv hxs⟩

end OpenPartialHomeomorph
