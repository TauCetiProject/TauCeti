/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Stallings.Coset.Embedding
public import TauCeti.Combinatorics.Graph.Stallings.Isomorphism

/-!
# Uniqueness of folded based cores

The embedding of a connected folded based core into its coset graph has image exactly
the based core of that coset graph. Consequently it is isomorphic to the canonical subgroup
graph, and two folded based cores accept the same subgroup precisely when they are
isomorphic. Such a based labelled isomorphism is unique. No finiteness or finite-alphabet
assumption is needed, and the isolated base vertex of the trivial subgroup is retained.

## References

* I. Kapovich and A. Myasnikov, *Stallings foldings and subgroups of free groups*,
  Section 5, Theorems 5.1–5.2.
-/

public section

namespace TauCeti.StallingsGraph

variable {α : Type*} {S T : StallingsGraph α}

/-- The coset graph's induced quiver, used when mapping paths into it. -/
@[instance_reducible] local instance (H : Subgroup (FreeGroup α)) :
    Quiver H.cosetGraph.graph.V := H.cosetGraph.graph.toQuiver

/-- A folded based core fills precisely the core darts of its coset graph. -/
theorem Hom.range_mapE_cosetGraph_eq_coreDarts
    (f : S.Hom (S.subgroup S.base).cosetGraph) (hfold : S.IsFolded)
    (hcore : S.graph.IsCore S.base) :
    Set.range f.graphHom.mapE =
      (S.subgroup S.base).cosetGraph.graph.coreDarts (S.subgroup S.base).cosetGraph.base := by
  obtain ⟨hreach, hcover⟩ := (S.graph.isCore_iff S.base).mp hcore
  obtain ⟨_, hfE⟩ := f.injective_cosetGraph hfold hreach
  ext e
  constructor
  · rintro ⟨e, rfl⟩
    -- Injectivity preserves the reduced loop witnessing each source dart.
    obtain ⟨p, hp, he⟩ := hcover e
    have h : ∃ q : (S.subgroup S.base).cosetGraph.graph.Path
        (f.graphHom.mapV S.base) (f.graphHom.mapV S.base),
        SerreGraph.Path.IsReduced (S.subgroup S.base).cosetGraph.graph q ∧
          f.graphHom.mapE e ∈ SerreGraph.Path.darts (S.subgroup S.base).cosetGraph.graph q := by
      refine ⟨f.graphHom.toPrefunctor.mapPath p,
        (f.graphHom.isReduced_mapPath_iff S.graph hfE p).mpr hp, ?_⟩
      -- Substitution avoids `rw`'s transparency mismatch at the mapped path's endpoints.
      exact (f.graphHom.darts_mapPath S.graph p).symm ▸ List.mem_map_of_mem he
    apply ((S.subgroup S.base).cosetGraph.graph.mem_coreDarts_iff _ _).mpr
    exact f.map_base ▸ h
  · intro he
    have h : ∃ p : (S.subgroup S.base).cosetGraph.graph.Path
        (f.graphHom.mapV S.base) (f.graphHom.mapV S.base),
        SerreGraph.Path.IsReduced (S.subgroup S.base).cosetGraph.graph p ∧
          e ∈ SerreGraph.Path.darts (S.subgroup S.base).cosetGraph.graph p := by
      rw [f.map_base]
      exact ((S.subgroup S.base).cosetGraph.graph.mem_coreDarts_iff _ e).mp he
    obtain ⟨p, hp, he⟩ := h
    have hg : (S.subgroup S.base).cosetGraph.read p ∈ S.subgroup S.base := by
      have hs := (congrArg (S.subgroup S.base).cosetGraph.subgroup f.map_base).trans
        (S.subgroup S.base).cosetGraph_subgroup
      simpa only [hs] using (S.subgroup S.base).cosetGraph.read_mem_subgroup p
    -- The same accepted element has a reduced source loop. Its image is the target loop
    -- by foldedness, so every dart of the latter lies in the image.
    obtain ⟨q, hq, hread⟩ := S.mem_subgroup_iff_exists_reduced_path.mp hg
    have hmap : f.graphHom.toPrefunctor.mapPath q = p :=
      (S.subgroup S.base).cosetGraph_isFolded.path_eq_of_read_eq _ _ _
        ((f.graphHom.isReduced_mapPath_iff S.graph hfE q).mpr hq) hp
        ((f.read_mapPath q).trans hread)
    rw [← hmap] at he
    have he' := f.graphHom.darts_mapPath S.graph q ▸ he
    obtain ⟨d, _, hd⟩ := List.mem_map.mp he'
    exact ⟨d, hd⟩

/-- The image on vertices also includes exactly the canonical core, including its base
when there are no darts. -/
theorem Hom.range_mapV_cosetGraph_eq_coreVertices
    (f : S.Hom (S.subgroup S.base).cosetGraph) (hfold : S.IsFolded)
    (hcore : S.graph.IsCore S.base) :
    Set.range f.graphHom.mapV =
      (S.subgroup S.base).cosetGraph.graph.coreVertices (S.subgroup S.base).cosetGraph.base := by
  have hE := f.range_mapE_cosetGraph_eq_coreDarts hfold hcore
  have hreach := ((S.graph.isCore_iff S.base).mp hcore).1
  ext v
  constructor
  · rintro ⟨v, rfl⟩
    obtain ⟨p⟩ := hreach v
    cases p with
    | nil =>
      exact ((S.subgroup S.base).cosetGraph.graph.mem_coreVertices_iff _ _).mpr
        (Or.inl f.map_base)
    | cons p e =>
      have he : f.graphHom.mapE e.1 ∈ (S.subgroup S.base).cosetGraph.graph.coreDarts
          (S.subgroup S.base).cosetGraph.base := by
        rw [← hE]
        exact ⟨e.1, rfl⟩
      have ht := (S.subgroup S.base).cosetGraph.graph.tgt_mem_coreVertices _ he
      simpa only [f.graphHom.map_tgt, e.2.2] using ht
  · intro hv
    rcases ((S.subgroup S.base).cosetGraph.graph.mem_coreVertices_iff _ v).mp hv with
      rfl | ⟨e, he, rfl⟩
    · exact ⟨S.base, f.map_base⟩
    · rw [← hE] at he
      obtain ⟨d, rfl⟩ := he
      exact ⟨S.graph.src d, (f.graphHom.map_src d).symm⟩

/-- Every folded based core is isomorphic to the canonical graph of the subgroup it reads. -/
theorem nonempty_iso_subgroupGraph (hfold : S.IsFolded) (hcore : S.graph.IsCore S.base) :
    Nonempty (Iso S (S.subgroup S.base).subgroupGraph) := by
  classical
  have hreach := ((S.graph.isCore_iff S.base).mp hcore).1
  obtain ⟨f⟩ := (nonempty_hom_cosetGraph_iff hreach).mpr le_rfl
  obtain ⟨hfV, hfE⟩ := f.injective_cosetGraph hfold hreach
  have hV := f.range_mapV_cosetGraph_eq_coreVertices hfold hcore
  have hE := f.range_mapE_cosetGraph_eq_coreDarts hfold hcore
  let g : S.Hom (S.subgroup S.base).cosetGraph.core := {
    graphHom := {
      mapV := fun v => ⟨f.graphHom.mapV v, hV ▸ Set.mem_range_self v⟩
      mapE := fun e => ⟨f.graphHom.mapE e, hE ▸ Set.mem_range_self e⟩
      map_src := fun e => Subtype.ext (f.graphHom.map_src e)
      map_rev := fun e => Subtype.ext (f.graphHom.map_rev e) }
    map_base := Subtype.ext f.map_base
    map_label := fun e => f.map_label e }
  have hgV : Function.Bijective g.graphHom.mapV := by
    refine ⟨fun v w h => hfV (congrArg Subtype.val h), ?_⟩
    intro v
    obtain ⟨w, hw⟩ := (Set.ext_iff.mp hV v.1).mpr v.2
    exact ⟨w, Subtype.ext hw⟩
  have hgE : Function.Bijective g.graphHom.mapE := by
    refine ⟨fun e d h => hfE (congrArg Subtype.val h), ?_⟩
    intro e
    obtain ⟨d, hd⟩ := (Set.ext_iff.mp hE e.1).mpr e.2
    exact ⟨d, Subtype.ext hd⟩
  rw [Subgroup.subgroupGraph_def]
  exact ⟨g.toIso hgV hgE⟩

/-- Two folded based cores represent the same subgroup if and only if they are isomorphic.
No extra identification of basepoints or conjugacy of subgroups is allowed. -/
theorem nonempty_iso_iff_subgroup_eq (hS : S.IsFolded) (hT : T.IsFolded)
    (hSc : S.graph.IsCore S.base) (hTc : T.graph.IsCore T.base) :
    Nonempty (Iso S T) ↔ S.subgroup S.base = T.subgroup T.base := by
  constructor
  · rintro ⟨f⟩
    exact f.subgroup_eq
  · intro h
    obtain ⟨f⟩ := nonempty_iso_subgroupGraph hS hSc
    obtain ⟨g⟩ := nonempty_iso_subgroupGraph hT hTc
    rw [← h] at g
    exact ⟨f.trans g.symm⟩

/-- A folded based core representing the same subgroup as another has exactly one based
labelled isomorphism to it. -/
theorem nonempty_unique_iso_of_subgroup_eq (hS : S.IsFolded) (hT : T.IsFolded)
    (hSc : S.graph.IsCore S.base) (hTc : T.graph.IsCore T.base)
    (h : S.subgroup S.base = T.subgroup T.base) : Nonempty (Unique (Iso S T)) := by
  obtain ⟨f⟩ := (nonempty_iso_iff_subgroup_eq hS hT hSc hTc).mpr h
  exact ⟨⟨⟨f⟩, fun g => Iso.eq_of_isFolded_of_reachable hT
    ((S.graph.isCore_iff S.base).mp hSc).1 g f⟩⟩

end TauCeti.StallingsGraph
