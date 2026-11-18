/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Network.Isomorphism.Walk
public import TauCeti.Combinatorics.Network.MixedCapacity

/-!
# Path families and separators under network isomorphisms

A network isomorphism transports an indexed family of directed walks by transporting each walk.
This gives an equivalence even when the endpoints depend on the index, as they do for paths
between terminal sets. It preserves the conditions used by the path-packing interfaces: every
member being a path, pairwise arrow disjointness, pairwise vertex disjointness, and pairwise
internal disjointness for common terminals.

Mixed separators transport in parallel. The vertex finset is relabelled by the vertex
equivalence and the arrow finset by the equivalence on total arrows. A transported family of
walks therefore meets a transported separator exactly when the original family meets the
original separator. None of these results requires finite vertex or arrow types; finiteness is
carried only by the index type or by the separator finsets themselves.

## Main definitions

* `TauCeti.Network.Iso.pathFamilyEquiv`: the equivalence between indexed walk families under a
  network isomorphism.

## Main results

* `TauCeti.Network.Iso.pairwise_disjoint_arrows_pathFamilyEquiv_iff` and
  `TauCeti.Network.Iso.pairwise_disjoint_vertices_pathFamilyEquiv_iff`: transport of the two
  disjointness conditions for path packings.
* `TauCeti.Network.Iso.pairwise_internallyDisjoint_pathFamilyEquiv_iff`: transport of internal
  vertex disjointness for families with common terminals.
* `TauCeti.Network.Iso.isMixedSeparator_map_iff`: mixed vertex-and-arrow separators are
  invariant under network isomorphisms.
-/

public section

namespace TauCeti.Network.Iso

universe u u' v v' w w'

variable {K : Type w} [LE K] {V : Type u} {W : Type u'}
  {N : Network.{u, v} K V} {N' : Network.{u', v'} K W}

/-! ### Indexed path families -/

/-- Pointwise transport of walks gives an equivalence between indexed path families. The source
and target may depend on the index, which includes both fixed-terminal and set-to-set families. -/
def pathFamilyEquiv (e : N ≃ₙ N') {I : Type w'} (s t : I → V) :
    (∀ i, ArrowWalk N.Hom (s i) (t i)) ≃
      (∀ i, ArrowWalk N'.Hom (e.vertexEquiv (s i)) (e.vertexEquiv (t i))) :=
  Equiv.piCongrRight fun i ↦ e.pathEquiv (s i) (t i)

@[simp]
theorem pathFamilyEquiv_apply (e : N ≃ₙ N') {I : Type w'} (s t : I → V)
    (P : ∀ i, ArrowWalk N.Hom (s i) (t i)) (i : I) :
    e.pathFamilyEquiv s t P i = e.mapPath (P i) :=
  by
    rw [pathFamilyEquiv, Equiv.piCongrRight_apply]
    exact e.pathEquiv_apply (P i)

@[simp]
theorem pathFamilyEquiv_symm_apply (e : N ≃ₙ N') {I : Type w'} (s t : I → V)
    (P : ∀ i, ArrowWalk N'.Hom (e.vertexEquiv (s i)) (e.vertexEquiv (t i))) (i : I) :
    (e.pathFamilyEquiv s t).symm P i = (e.pathEquiv (s i) (t i)).symm (P i) :=
  (rfl)

/-- Transporting a restricted or reindexed family is the restriction of the transported family. -/
theorem pathFamilyEquiv_comp (e : N ≃ₙ N') {I J : Type w'} (s t : I → V)
    (P : ∀ i, ArrowWalk N.Hom (s i) (t i)) (f : J → I) :
    e.pathFamilyEquiv (s ∘ f) (t ∘ f) (fun j ↦ P (f j)) =
      fun j ↦ e.pathFamilyEquiv s t P (f j) :=
  by
    funext j
    rw [pathFamilyEquiv_apply, pathFamilyEquiv_apply]

/-- Pairwise arrow disjointness is preserved and reflected for indexed walk families. -/
theorem pairwise_disjoint_arrows_pathFamilyEquiv_iff (e : N ≃ₙ N') {I : Type w'}
    (s t : I → V) (P : ∀ i, ArrowWalk N.Hom (s i) (t i)) :
    (Pairwise fun i j ↦ (e.pathFamilyEquiv s t P i).arrows.Disjoint
      (e.pathFamilyEquiv s t P j).arrows) ↔
      Pairwise fun i j ↦ (P i).arrows.Disjoint (P j).arrows := by
  constructor
  · intro h i j hij
    have h' : (e.pathFamilyEquiv s t P i).arrows.Disjoint
        (e.pathFamilyEquiv s t P j).arrows := h hij
    rw [pathFamilyEquiv_apply, pathFamilyEquiv_apply] at h'
    exact (e.disjoint_arrows_mapPath (P i) (P j)).1 h'
  · intro h i j hij
    rw [pathFamilyEquiv_apply, pathFamilyEquiv_apply]
    exact (e.disjoint_arrows_mapPath (P i) (P j)).2 (h hij)

/-- Pairwise vertex disjointness is preserved and reflected for indexed walk families. -/
theorem pairwise_disjoint_vertices_pathFamilyEquiv_iff (e : N ≃ₙ N') {I : Type w'}
    (s t : I → V) (P : ∀ i, ArrowWalk N.Hom (s i) (t i)) :
    (Pairwise fun i j ↦ (e.pathFamilyEquiv s t P i).vertices.Disjoint
      (e.pathFamilyEquiv s t P j).vertices) ↔
      Pairwise fun i j ↦ (P i).vertices.Disjoint (P j).vertices := by
  constructor
  · intro h i j hij
    have h' : (e.pathFamilyEquiv s t P i).vertices.Disjoint
        (e.pathFamilyEquiv s t P j).vertices := h hij
    rw [pathFamilyEquiv_apply, pathFamilyEquiv_apply] at h'
    exact (e.disjoint_vertices_mapPath (P i) (P j)).1 h'
  · intro h i j hij
    rw [pathFamilyEquiv_apply, pathFamilyEquiv_apply]
    exact (e.disjoint_vertices_mapPath (P i) (P j)).2 (h hij)

/-- Pairwise internal vertex disjointness is preserved and reflected for a family whose members
all have the same source and target. -/
theorem pairwise_internallyDisjoint_pathFamilyEquiv_iff (e : N ≃ₙ N') {I : Type w'}
    {s t : V} (P : I → ArrowWalk N.Hom s t) :
    (Pairwise fun i j ↦
      (e.pathFamilyEquiv (fun _ ↦ s) (fun _ ↦ t) P i).InternallyDisjoint
        (e.pathFamilyEquiv (fun _ ↦ s) (fun _ ↦ t) P j)) ↔
      Pairwise fun i j ↦ (P i).InternallyDisjoint (P j) := by
  constructor
  · intro h i j hij
    have h' :
        (e.pathFamilyEquiv (fun _ ↦ s) (fun _ ↦ t) P i).InternallyDisjoint
          (e.pathFamilyEquiv (fun _ ↦ s) (fun _ ↦ t) P j) := h hij
    rw [pathFamilyEquiv_apply, pathFamilyEquiv_apply] at h'
    exact (e.internallyDisjoint_mapPath (P i) (P j)).1 h'
  · intro h i j hij
    rw [pathFamilyEquiv_apply, pathFamilyEquiv_apply]
    exact (e.internallyDisjoint_mapPath (P i) (P j)).2 (h hij)

/-! ### Mixed separators -/

/-- A mixed separator remains a mixed separator after relabelling both its vertices and its
individual arrow identities. This preserves and reflects the property, including loops and
parallel arrows. -/
@[simp]
theorem isMixedSeparator_map_iff (e : N ≃ₙ N') (X : Finset V)
    (F : Finset (Σ x y, N.Hom x y)) {s t : V} :
    IsMixedSeparator (X.map e.vertexEquiv.toEmbedding) (F.map e.totalHomEquiv.toEmbedding)
      (e.vertexEquiv s) (e.vertexEquiv t) ↔ IsMixedSeparator X F s t := by
  classical
  constructor
  · intro h
    refine isMixedSeparator_iff.2 ⟨?_, ?_, fun p ↦ ?_⟩
    · simpa using h.source_notMem
    · simpa using h.target_notMem
    · rcases h.exists_mem (e.mapPath p) with ⟨v, hvp, hvX⟩ | ⟨a, hap, haF⟩
      · rw [e.vertices_mapPath] at hvp
        obtain ⟨v', hvp, hv'⟩ := List.mem_map.1 hvp
        obtain ⟨v'', hvX, hv''⟩ := Finset.mem_map.1 hvX
        have hv : v' = v'' := e.vertexEquiv.injective (hv'.trans hv''.symm)
        subst v''
        exact Or.inl ⟨v', hvp, hvX⟩
      · rw [e.arrows_mapPath] at hap
        obtain ⟨a', hap, ha'⟩ := List.mem_map.1 hap
        obtain ⟨a'', haF, ha''⟩ := Finset.mem_map.1 haF
        have ha : a' = a'' := e.totalHomEquiv.injective (ha'.trans ha''.symm)
        subst a''
        exact Or.inr ⟨a', hap, haF⟩
  · intro h
    refine isMixedSeparator_iff.2 ⟨?_, ?_, fun p ↦ ?_⟩
    · simpa using h.source_notMem
    · simpa using h.target_notMem
    · obtain ⟨p, rfl⟩ := (e.pathEquiv s t).surjective p
      rcases h.exists_mem p with ⟨v, hvp, hvX⟩ | ⟨a, hap, haF⟩
      · refine Or.inl ⟨e.vertexEquiv v, ?_, ?_⟩
        · rw [pathEquiv_apply, e.vertices_mapPath]
          exact List.mem_map_of_mem hvp
        · rw [Finset.mem_map]
          exact ⟨v, hvX, rfl⟩
      · refine Or.inr ⟨e.totalHomEquiv a, ?_, ?_⟩
        · rw [pathEquiv_apply, e.arrows_mapPath]
          exact List.mem_map_of_mem hap
        · rw [Finset.mem_map]
          exact ⟨a, haF, rfl⟩

end TauCeti.Network.Iso
