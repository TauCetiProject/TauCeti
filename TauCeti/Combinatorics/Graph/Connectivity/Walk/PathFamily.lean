/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Connectivity.Walk.Isomorphism

/-!
# Relabelling multigraph path families

Graph isomorphisms identify families of edge-labelled walks, even when each member has different
endpoints. They preserve and reflect disjointness of traversed edge identities, disjointness of
whole vertex supports, and internal vertex disjointness for common endpoints. In particular,
transporting a family of distinct paths does not identify paths using different parallel edges.

The family equivalence uses arbitrary index types; neither the graphs nor the families need be
finite. Finite families therefore retain their index set and cardinality without any finiteness
assumption on the ambient vertex or edge types.
-/

public section

universe u v u' v' w

namespace Graph.Iso

variable {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
variable {G : Graph α β} {H : Graph α' β'}

/-- An isomorphism preserves and reflects disjointness of traversed edge identities. -/
@[simp]
theorem disjoint_edges_mapWalk_iff (f : G.Iso H) {x y z t : V(G)}
    (p : G.Walk x y) (q : G.Walk z t) :
    (f.mapWalk p).edges.Disjoint (f.mapWalk q).edges ↔ p.edges.Disjoint q.edges := by
  simp only [edges_mapWalk, List.unattach, List.Disjoint.map_iff Subtype.val_injective,
    List.Disjoint.map_iff f.edgeEquiv.injective]
  simpa only [List.map_subtype, List.map_id', Walk.edgesAttach_unattach] using
    (List.Disjoint.map_iff (s := p.edgesAttach) (t := q.edgesAttach)
      Subtype.val_injective).symm

/-- An isomorphism preserves and reflects disjointness including the walk endpoints. -/
@[simp]
theorem disjoint_support_mapWalk_iff (f : G.Iso H) {x y z t : V(G)}
    (p : G.Walk x y) (q : G.Walk z t) :
    (f.mapWalk p).support.Disjoint (f.mapWalk q).support ↔ p.support.Disjoint q.support := by
  simp only [support_mapWalk, List.unattach, List.Disjoint.map_iff Subtype.val_injective,
    List.Disjoint.map_iff f.vertexEquiv.injective]
  simpa only [List.map_subtype, List.map_id', Walk.vertices_toBidirected] using
    (List.Disjoint.map_iff (s := (p.toBidirected x.2).vertices)
      (t := (q.toBidirected z.2).vertices) Subtype.val_injective).symm

/-- An isomorphism preserves and reflects internal disjointness for common endpoints. -/
@[simp]
theorem internallyDisjoint_mapWalk_iff (f : G.Iso H) {x y : V(G)} (p q : G.Walk x y) :
    (f.mapWalk p).InternallyDisjoint (f.mapWalk q) ↔ p.InternallyDisjoint q := by
  rw [Walk.internallyDisjoint_def, Walk.internallyDisjoint_def]
  constructor
  · intro h a hap haq
    let a' : V(G) := ⟨a, p.support_subset_vertexSet x.2 a hap⟩
    have ha := h (f.vertexEquiv a')
      ((f.vertexEquiv_mem_support_mapWalk_iff p a').2 hap)
      ((f.vertexEquiv_mem_support_mapWalk_iff q a').2 haq)
    exact ha.imp
      (fun hx ↦ congrArg Subtype.val (f.vertexEquiv.injective (Subtype.ext hx)))
      (fun hy ↦ congrArg Subtype.val (f.vertexEquiv.injective (Subtype.ext hy)))
  · intro h a hap haq
    let a' : V(H) := ⟨a, (f.mapWalk p).support_subset_vertexSet (f.vertexEquiv x).2 a hap⟩
    have hp : (f.vertexEquiv (f.vertexEquiv.symm a') : α') ∈ (f.mapWalk p).support := by
      simpa [a'] using hap
    have hq : (f.vertexEquiv (f.vertexEquiv.symm a') : α') ∈ (f.mapWalk q).support := by
      simpa [a'] using haq
    have ha := h _ ((f.vertexEquiv_mem_support_mapWalk_iff p _).1 hp)
      ((f.vertexEquiv_mem_support_mapWalk_iff q _).1 hq)
    rcases ha with hx | hy
    · left
      exact congrArg Subtype.val (by simpa using congrArg f.vertexEquiv (Subtype.ext hx))
    · right
      exact congrArg Subtype.val (by simpa using congrArg f.vertexEquiv (Subtype.ext hy))

/-- Relabel an indexed walk family, allowing each member to have its own endpoints. -/
def walkFamilyEquiv (f : G.Iso H) {ι : Type w} (a b : ι → V(G)) :
    (∀ i, G.Walk (a i) (b i)) ≃
      (∀ i, H.Walk (f.vertexEquiv (a i)) (f.vertexEquiv (b i))) :=
  Equiv.piCongrRight fun i ↦ f.walkEquiv (a i) (b i)

/-- The transported member is the ordinary walk transport. -/
@[simp]
theorem walkFamilyEquiv_apply (f : G.Iso H) {ι : Type w} (a b : ι → V(G))
    (P : ∀ i, G.Walk (a i) (b i)) (i : ι) :
    f.walkFamilyEquiv a b P i = f.mapWalk (P i) := by
  simp [walkFamilyEquiv]

/-- Inverse family transport acts memberwise by inverse walk transport. -/
@[simp]
theorem walkFamilyEquiv_symm_apply (f : G.Iso H) {ι : Type w} (a b : ι → V(G))
    (P : ∀ i, H.Walk (f.vertexEquiv (a i)) (f.vertexEquiv (b i))) (i : ι) :
    (f.walkFamilyEquiv a b).symm P i = (f.walkEquiv (a i) (b i)).symm (P i) := (rfl)

/-- Relabel a family of simple paths, with index-dependent endpoints. -/
def pathFamilyEquiv (f : G.Iso H) {ι : Type w} (a b : ι → V(G)) :
    (∀ i, {p : G.Walk (a i) (b i) // p.IsPath}) ≃
      (∀ i, {p : H.Walk (f.vertexEquiv (a i)) (f.vertexEquiv (b i)) // p.IsPath}) :=
  Equiv.piCongrRight fun i ↦ (f.walkEquiv (a i) (b i)).subtypeEquiv
    (fun p ↦ by simp)

/-- Relabelling a path family transports its underlying walks. -/
@[simp]
theorem pathFamilyEquiv_apply_val (f : G.Iso H) {ι : Type w} (a b : ι → V(G))
    (P : ∀ i, {p : G.Walk (a i) (b i) // p.IsPath}) (i : ι) :
    (f.pathFamilyEquiv a b P i).val = f.mapWalk (P i).val := by
  simp [pathFamilyEquiv]

/-- Inverse path-family transport recovers each underlying walk by the inverse equivalence. -/
@[simp]
theorem pathFamilyEquiv_symm_apply_val (f : G.Iso H) {ι : Type w} (a b : ι → V(G))
    (P : ∀ i, {p : H.Walk (f.vertexEquiv (a i)) (f.vertexEquiv (b i)) // p.IsPath})
    (i : ι) :
    ((f.pathFamilyEquiv a b).symm P i).val =
      (f.walkEquiv (a i) (b i)).symm (P i).val := (rfl)

end Graph.Iso
