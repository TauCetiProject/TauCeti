/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.UnitInterval

/-!
# Subdividing a continuous-map square under a neighbourhood cover

A continuous square with a neighbourhood cover admits a finite grid subdivision such
that every closed grid cell maps into one member of the cover. This is useful, in particular, for
turning a homotopy between paths into relations among paths lying in members of an open cover.

The grid construction adapts `coveredPartwise_exists` from
`LeanPool.DirectedTopologyLean4.DihomotopyCover.lean` (LeanPool commit
`34ba5ae88508eccb9d88380a7126a595e3796832`, Apache-2.0; copyright (c) 2026 Dominique Lawson,
Henning Basold, and Peter Bruin). The general form follows Mathlib's
`exists_monotone_Icc_subset_open_cover_unitInterval_prod_self`.
-/

public section

open Set Topology
open scoped unitInterval

namespace ContinuousMap

/-- A neighbourhood cover of a continuous square admits a finite monotone grid whose closed
cells each map into a cover member. -/
theorem exists_grid_subdivision {X : Type*} [TopologicalSpace X] {ι : Sort*}
    (K : C(↥unitInterval × ↥unitInterval, X)) (U : ι → Set X)
    (hU : ∀ z, ∃ i, U i ∈ 𝓝 (K z)) :
    ∃ (n : ℕ) (t : Fin (n + 1) → unitInterval),
      t 0 = 0 ∧ t (Fin.last n) = 1 ∧ Monotone t ∧
        ∀ j k : Fin n, ∃ i, MapsTo K
          (Icc (t j.castSucc) (t j.succ) ×ˢ Icc (t k.castSucc) (t k.succ)) (U i) := by
  let V : ι → Set (unitInterval × unitInterval) := fun i => K ⁻¹' interior (U i)
  have hVopen : ∀ i, IsOpen (V i) := fun i => isOpen_interior.preimage K.continuous
  have hVcover : Set.univ ⊆ ⋃ i, V i := by
    intro x _
    rcases hU x with ⟨i, hi⟩
    exact mem_iUnion.2 ⟨i, mem_interior_iff_mem_nhds.mpr hi⟩
  obtain ⟨t, ht0, hmono, ⟨m, htail⟩, hcell⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval_prod_self hVopen hVcover
  refine ⟨m, fun k ↦ t k, by simpa using ht0, by simpa using htail m le_rfl,
    fun a b hab ↦ hmono (by simpa using hab), ?_⟩
  intro j k
  obtain ⟨i, hi⟩ := hcell j k
  exact ⟨i, fun z hz ↦ interior_subset (hi hz)⟩

end ContinuousMap
