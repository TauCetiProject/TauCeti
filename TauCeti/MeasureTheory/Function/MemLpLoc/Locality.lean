/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.MemLpLoc.Basic
import Mathlib.Topology.Separation.Regular

/-!
# Locality of local `Lᵖ` classes

For an arbitrary subset `U` of a regular topological measure space, `TauCeti.MemLpLoc p U` has the
sheaf property: membership holds on `U` if and only if it holds on a relative neighbourhood of each
point of `U` (`TauCeti.memLpLoc_iff_locally`), or on the traces `U ∩ O i` of any open cover of `U`
(`TauCeti.memLpLoc_iff_forall_inter`).

## Main results

* `TauCeti.memLpLoc_iff_locally`: local `Lᵖ` membership holds iff it holds near each point.
* `TauCeti.memLpLoc_iff_forall_inter`: local `Lᵖ` membership on `U` is membership on the traces
  `U ∩ O i` of an open cover.
* `TauCeti.memLpLoc_iSup_iff`: the sheaf property for open covers of an open set.
-/

public section

open MeasureTheory Set TopologicalSpace Filter
open scoped Topology

namespace TauCeti

section MemLpLoc

variable {E F : Type*} [TopologicalSpace E] [RegularSpace E] [MeasureSpace E]
  [NormedAddCommGroup F] {p : ENNReal} {U : Set E} {f : E → F}

/-- Local `Lᵖ` membership is a local property: it holds on `U` exactly when every point of `U`
has a neighbourhood within `U` on which it holds. -/
theorem memLpLoc_iff_locally :
    MemLpLoc p U f ↔ ∀ x ∈ U, ∃ V ∈ 𝓝[U] x, MemLpLoc p V f := by
  refine ⟨fun hf _ _ => ⟨U, self_mem_nhdsWithin, hf⟩,
    fun h => memLpLoc_iff.2 fun K hKU hK => ?_⟩
  refine hK.induction_on (p := fun s => MemLp f p (volume.restrict s)) (by simp)
    (fun s t hst ht => ht.mono_measure (Measure.restrict_mono hst le_rfl))
    (fun s t hs ht => (hs.add_measure ht).mono_measure (Measure.restrict_union_le s t))
    fun x hx => ?_
  obtain ⟨V, hV, hfV⟩ := h x (hKU hx)
  obtain ⟨O, hO, hOV⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hV
  obtain ⟨C, ⟨hCnhds, hCclosed⟩, hCO⟩ := (closed_nhds_basis x).mem_iff.1 hO
  exact ⟨K ∩ C, inter_mem_nhdsWithin K hCnhds,
    memLpLoc_iff.1 hfV _ (fun z hz => hOV ⟨hCO hz.2, hKU hz.1⟩) (hK.inter_right hCclosed)⟩

/-- Local `Lᵖ` membership on `U` can be checked on the traces `U ∩ O i` of an open cover. -/
theorem memLpLoc_iff_forall_inter {ι : Type*} (O : ι → Opens E)
    (hU : U ⊆ ⋃ i, (O i : Set E)) :
    MemLpLoc p U f ↔ ∀ i, MemLpLoc p (U ∩ O i) f := by
  refine ⟨fun hf i => hf.mono_set inter_subset_left, fun h => memLpLoc_iff_locally.2 ?_⟩
  intro x hx
  obtain ⟨i, hi⟩ := mem_iUnion.1 (hU hx)
  exact ⟨U ∩ O i, inter_mem_nhdsWithin U ((O i).isOpen.mem_nhds hi), h i⟩

/-- Local `Lᵖ` membership on the union of open sets is membership on each of them. -/
theorem memLpLoc_iSup_iff {ι : Type*} (V : ι → Opens E) :
    MemLpLoc p (⨆ i, V i : Opens E) f ↔ ∀ i, MemLpLoc p (V i) f := by
  rw [memLpLoc_iff_forall_inter V (by simp)]
  simp only [Opens.coe_iSup, inter_eq_right.2 (subset_iUnion (fun i => (V i : Set E)) _)]

end MemLpLoc

end TauCeti
