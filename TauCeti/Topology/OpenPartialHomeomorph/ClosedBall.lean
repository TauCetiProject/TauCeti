/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.OpenPartialHomeomorph.Continuity
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Closed balls of a chart covering a compact set

An open partial homeomorphism `φ : M → E` into a pseudometric space pulls closed balls of `E`
back to `M` through `φ.symm`. This file proves that a compact subset `A` of the source of `φ` is
covered by finitely many such balls centred at points of `A`, all lying in the target of `φ` and
pulling back into a given neighbourhood of `A`
(`OpenPartialHomeomorph.exists_finset_closedBall_cover`).

A compact set `A` in the interior of a set `C ⊆ φ.source` also has a uniform margin in `C`
measured in `φ`: every point of `C` within some fixed `η > 0` of a point of `A`, after applying
`φ`, lies in the interior of `C` (`OpenPartialHomeomorph.exists_pos_forall_mem_interior`).
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
  refine ⟨t, r, fun a ha ↦ ⟨htA a ha, hr a (htA a ha), fun z hz ↦ (hrU a (htA a ha) hz).1,
    image_subset_iff.2 fun z hz ↦ (hrU a (htA a ha) hz).2⟩, fun x hx ↦ ?_⟩
  obtain ⟨hxs, a, ha, hxb⟩ : x ∈ φ.source ∧ ∃ a ∈ t, φ x ∈ ball (φ a) (r a) := by
    simpa using hAt hx
  exact ⟨φ x, mem_biUnion ha (ball_subset_closedBall hxb), φ.left_inv hxs⟩

/-- In an open partial homeomorphism `φ` into a pseudometric space, a compact set `A` in the
interior of `C ⊆ φ.source` has a margin: there is `η > 0` such that every point of `C` within `η`
of a point of `A`, measured in `φ`, lies in the interior of `C`. -/
theorem exists_pos_forall_mem_interior (φ : OpenPartialHomeomorph M E) {A C : Set M}
    (hA : IsCompact A) (hAC : A ⊆ interior C) (hCφ : C ⊆ φ.source) :
    ∃ η > 0, ∀ a ∈ A, ∀ x ∈ C, dist (φ x) (φ a) < η → x ∈ interior C := by
  have hT : IsCompact (φ '' A) :=
    hA.image_of_continuousOn (φ.continuousOn.mono (hAC.trans (interior_subset.trans hCφ)))
  have hU : IsOpen (φ '' interior C) :=
    φ.isOpen_image_of_subset_source isOpen_interior (interior_subset.trans hCφ)
  obtain ⟨η, hη, hsub⟩ := hT.exists_thickening_subset_open hU (image_mono hAC)
  refine ⟨η, hη, fun a ha x hx hxa ↦ ?_⟩
  obtain ⟨c, hc, hcx⟩ := hsub (mem_thickening_iff.2 ⟨φ a, mem_image_of_mem φ ha, hxa⟩)
  rwa [← φ.injOn (hCφ (interior_subset hc)) (hCφ hx) hcx]

end OpenPartialHomeomorph
