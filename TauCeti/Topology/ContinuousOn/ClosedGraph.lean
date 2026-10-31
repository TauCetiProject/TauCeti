/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Maps.Proper.Basic

/-!
# Closed graphs and continuity on a set

A function whose graph over a set `s` is closed and whose values on `s` lie in a compact set is
continuous on `s`. This is the relative form of Mathlib's `continuous_of_isClosed_graph`; it
identifies a bounded single-valued closure of a graph with a continuous function.
Conversely, `ContinuousOn.closure_graphOn_inter` recovers a continuous function's graph from
its restriction to a relatively dense subset. This permits extending a description of a graph
across an exceptional locus without making any choices of values there.
-/

public section

open Set

namespace TauCeti

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A function whose graph over `s` is closed and which maps `s` into a compact set is continuous
on `s`. -/
theorem continuousOn_of_isClosed_graphOn {f : X → Y} {s : Set X} {K : Set Y}
    (hf : IsClosed (s.graphOn f)) (hK : IsCompact K) (hfK : MapsTo f s K) :
    ContinuousOn f s := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let F : s → K := fun x ↦ ⟨f x, hfK x.2⟩
  have hgraph : F.graph = Prod.map Subtype.val Subtype.val ⁻¹' s.graphOn f := by
    ext ⟨x, y⟩
    simp [F, Function.graph, Subtype.ext_iff]
  have hF : Continuous F := continuous_of_isClosed_graph <| by
    rw [hgraph]
    exact hf.preimage (continuous_subtype_val.prodMap continuous_subtype_val)
  exact continuousOn_iff_continuous_domRestrict.mpr (continuous_subtype_val.comp hF)

end TauCeti

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A continuous function on `s` is recovered from its graph on a relatively dense subset `t`:
the graph closure, restricted back to points over `s`, is exactly its graph on `s`. -/
theorem ContinuousOn.closure_graphOn_inter [T2Space Y] {f : X → Y} {s t : Set X}
    (hf : ContinuousOn f s) (hts : t ⊆ s) (hst : s ⊆ closure t) :
    closure (t.graphOn f) ∩ (s ×ˢ univ) = s.graphOn f := by
  let e : s × Y → X × Y := Prod.map Subtype.val id
  have he : Topology.IsEmbedding e := Topology.IsEmbedding.subtypeVal.prodMap .id
  have himage : e '' (Function.graph (fun x : s ↦ f x) ∩ ((Subtype.val ⁻¹' t) ×ˢ univ)) =
      t.graphOn f := by
    ext ⟨x, y⟩
    simp only [mem_image, mem_inter_iff, Function.mem_graph, mem_prod, mem_preimage,
      mem_univ, and_true, Prod.exists, e, Prod.map_apply, id_eq, Prod.mk.injEq,
      mem_graphOn]
    constructor
    · rintro ⟨a, b, ⟨hab, ha⟩, rfl, rfl⟩
      exact ⟨ha, hab⟩
    · rintro ⟨hx, rfl⟩
      exact ⟨⟨x, hts hx⟩, f x, ⟨rfl, hx⟩, rfl, rfl⟩
  have hclosed := (continuousOn_iff_continuous_domRestrict.mp hf).isClosed_graph
  apply Subset.antisymm
  · rintro ⟨x, y⟩ ⟨hxy, hx, -⟩
    have hpre : (⟨x, hx⟩, y) ∈ e ⁻¹' closure (t.graphOn f) := hxy
    rw [← himage, ← he.closure_eq_preimage_closure_image] at hpre
    exact mem_graphOn.mpr ⟨hx, closure_minimal inter_subset_left hclosed hpre⟩
  · rintro ⟨x, y⟩ hxy
    obtain ⟨hx, hy⟩ := mem_graphOn.mp hxy
    dsimp only at hy
    subst y
    refine ⟨?_, hx, mem_univ _⟩
    simpa only [graphOn, id_eq] using
      (continuousWithinAt_id.prodMk ((hf x hx).mono hts)).mem_closure_image (hst hx)
