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
In the other direction, `TauCeti.isClosed_graphOn_of_continuousOn` shows that the graph of a map
`f` on `s` is closed when `j ∘ f` extends, for a continuous injection `j` into a Hausdorff space,
to a map continuous on a closed set `F ⊇ s` that sends `F \ s` outside the range of `j`.
Conversely, `ContinuousOn.closure_graphOn_inter` recovers a continuous function's graph from its
restriction to a relatively dense subset. This permits extending a description of a graph
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
  let F : s → K := fun x ↦ ⟨f x, hfK x.property⟩
  have hgraph : F.graph = Prod.map Subtype.val Subtype.val ⁻¹' s.graphOn f := by
    ext ⟨x, y⟩
    simp [F, Function.graph, Subtype.ext_iff]
  have hF : Continuous F := continuous_of_isClosed_graph <| by
    rw [hgraph]
    exact hf.preimage (continuous_subtypeVal.prodMap continuous_subtypeVal)
  exact continuousOn_iff_continuous_domRestrict.mpr (continuous_subtypeVal.comp hF)

/-- **The graph of a map that extends beyond its domain is closed.** Let `j : Y → Z` be a
continuous injection into a Hausdorff space, and `F` a closed subset of `X` containing `s`. If `f`
followed by `j` extends from `s` to a map `c` continuous on `F` which sends the points of `F`
outside `s` outside the image of `j`, then the graph of `f` on `s` is closed in `X × Y`.

This is the situation of a collar `(s, t) ↦ φ_t(s)`, `t < 0`, of the boundary `S` of a manifold
with boundary `W` by the backward flow of an outward vector field, with `Y` the interior of `W` and
`F = S × (-∞, 0]`. -/
theorem isClosed_graphOn_of_continuousOn {Z : Type*} [TopologicalSpace Z] [T2Space Z]
    {j : Y → Z} (hj : Continuous j) (hj' : Function.Injective j) {f : X → Y} {s F : Set X}
    {c : X → Z} (hF : IsClosed F) (hc : ContinuousOn c F) (hsF : s ⊆ F)
    (hce : ∀ x ∈ s, c x = j (f x)) (hcF : ∀ x ∈ F \ s, c x ∉ range j) :
    IsClosed (s.graphOn f) := by
  -- The graph lies in the closed set of pairs `(x, y)` with `x ∈ F` and `c x = j y`.
  have hK : IsClosed ({p : X × Y | p.1 ∈ F} ∩
      (fun p : X × Y ↦ (c p.1, j p.2)) ⁻¹' diagonal Z) :=
    ((hc.comp continuous_fst.continuousOn fun _ hp ↦ hp).prodMk
      (hj.comp continuous_snd).continuousOn).preimage_isClosed_of_isClosed
      (hF.preimage continuous_fst) isClosed_diagonal
  have hsub : s.graphOn f ⊆ {p : X × Y | p.1 ∈ F} ∩
      (fun p : X × Y ↦ (c p.1, j p.2)) ⁻¹' diagonal Z := by
    rintro ⟨x, y⟩ hxy
    obtain ⟨hx, hxy⟩ := mem_graphOn.1 hxy
    exact ⟨hsF hx, mem_preimage.2 (mem_diagonal_iff.2 ((hce x hx).trans (congrArg j hxy)))⟩
  refine isClosed_of_closure_subset fun p hp ↦ ?_
  obtain ⟨hpF, hpc⟩ := hK.closure_subset_iff.2 hsub hp
  have hpc' : c p.1 = j p.2 := mem_diagonal_iff.1 (mem_preimage.1 hpc)
  -- The point `p.1` lies in `F` and `c` sends it into the image of `j`, so it lies in `s`.
  have hps : p.1 ∈ s := of_not_not fun h ↦ hcF p.1 ⟨hpF, h⟩ ⟨p.2, hpc'.symm⟩
  exact mem_graphOn.2 ⟨hps, hj' ((hce p.1 hps).symm.trans hpc')⟩

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
    have hpre : (⟨x, hx⟩, y) ∈ e ⁻¹' closure (t.graphOn f) := by
      simpa only [mem_preimage, e, Prod.map_apply, id_eq] using hxy
    rw [← himage, ← he.closure_eq_preimage_closure_image] at hpre
    exact mem_graphOn.mpr ⟨hx, closure_minimal inter_subset_left hclosed hpre⟩
  · rintro ⟨x, y⟩ hxy
    obtain ⟨hx, hy⟩ := mem_graphOn.mp hxy
    dsimp only at hy
    subst y
    refine ⟨?_, hx, mem_univ _⟩
    simpa only [graphOn, id_eq] using
      (continuousWithinAt_id.prodMk ((hf x hx).mono hts)).mem_closure_image (hst hx)
