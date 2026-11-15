/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Connectivity.Walk.OfSimpleGraph

/-!
# Projecting multigraph paths to the underlying simple graph

A path in a multigraph cannot traverse a loop, since that would repeat its incident vertex.
Consequently, forgetting the identities of its traversed edges gives a path in the underlying
simple graph. This file constructs that projection and proves that it preserves the complete
vertex sequence, and computes it on trivial paths, on paths beginning with an edge, and on
reversed paths. In particular, projection preserves and reflects vertex-disjointness and
internal vertex-disjointness.

Distinct paths using parallel edges can have the same projection. Thus the construction is a
map of paths, rather than an equivalence; the reverse operation
`SimpleGraph.Walk.liftToGraph` chooses an actual edge for every adjacency.
-/

public section

universe u v

namespace Graph.Walk

variable {α : Type u} {β : Type v} {G : Graph α β} {s t : V(G)}

private theorem exists_projectPath' {x y : α} (p : G.Walk x y) (hp : p.IsPath)
    (hx : x ∈ V(G)) (hy : y ∈ V(G)) :
    ∃ q : G.toSimpleGraph.Walk ⟨x, hx⟩ ⟨y, hy⟩,
      q.IsPath ∧ q.support.map Subtype.val = p.support := by
  induction p with
  | nil =>
      exact ⟨.nil, by simp, by
        simp only [SimpleGraph.Walk.support_nil, List.map_cons, List.map_nil, support_nil]⟩
  | @cons x y z e h p ih =>
      have hp' : p.IsPath ∧ x ∉ p.support := (isPath_cons e h p).mp hp
      obtain ⟨q, _, hsupport⟩ := ih hp'.1 h.right_mem hy
      have hxy : (⟨x, hx⟩ : V(G)) ≠ ⟨y, h.right_mem⟩ := by
        intro hxy
        have hxy' : x = y := congrArg Subtype.val hxy
        exact hp'.2 (by simpa only [hxy'] using p.start_mem_support)
      let hAdj : G.toSimpleGraph.Adj ⟨x, hx⟩ ⟨y, h.right_mem⟩ :=
        ⟨hxy, ⟨e, h⟩⟩
      let q' := SimpleGraph.Walk.cons hAdj q
      have hsupport' : q'.support.map Subtype.val = (cons e h p).support := by
        simp only [q', SimpleGraph.Walk.support_cons, List.map_cons, support_cons, hsupport]
      refine ⟨q', ?_, hsupport'⟩
      rw [SimpleGraph.Walk.isPath_def, ← List.nodup_map_iff Subtype.val_injective, hsupport']
      exact (isPath_def _).mp hp

/-- Project a multigraph path to a path in its underlying simple graph by forgetting edge
identities. The projection retains the entire vertex sequence. -/
noncomputable def projectPath (p : G.Walk s t) (hp : p.IsPath) :
    {q : G.toSimpleGraph.Walk s t //
      q.IsPath ∧ q.support.unattach = p.support} := by
  let h := exists_projectPath' p hp s.property t.property
  refine ⟨Classical.choose h, (Classical.choose_spec h).1, ?_⟩
  simpa only [List.unattach] using (Classical.choose_spec h).2

/-- The projection of a multigraph path is a simple-graph path. -/
@[simp]
theorem projectPath_isPath (p : G.Walk s t) (hp : p.IsPath) :
    (p.projectPath hp : G.toSimpleGraph.Walk s t).IsPath :=
  (p.projectPath hp).property.1

/-- Projection preserves the complete vertex sequence after forgetting membership proofs. -/
@[simp]
theorem support_projectPath (p : G.Walk s t) (hp : p.IsPath) :
    (p.projectPath hp : G.toSimpleGraph.Walk s t).support.unattach = p.support :=
  (p.projectPath hp).property.2

/-- Projection preserves path length. -/
@[simp]
theorem length_projectPath (p : G.Walk s t) (hp : p.IsPath) :
    (p.projectPath hp : G.toSimpleGraph.Walk s t).length = p.length := by
  have h := congrArg List.length (support_projectPath p hp)
  simp only [List.unattach, List.length_map, SimpleGraph.Walk.length_support, length_support] at h
  omega

private theorem projectPath_eq_of_support_unattach (p : G.Walk s t) (hp : p.IsPath)
    (q : G.toSimpleGraph.Walk s t) (hq : q.support.unattach = p.support) :
    (p.projectPath hp : G.toSimpleGraph.Walk s t) = q :=
  SimpleGraph.Walk.ext_support <| List.map_injective_iff.2 Subtype.val_injective <| by
    simpa only [List.unattach] using (support_projectPath p hp).trans hq.symm

/-- Projecting the trivial path gives the trivial path. -/
@[simp]
theorem projectPath_nil (hp : (nil : G.Walk s s).IsPath) :
    ((nil : G.Walk s s).projectPath hp : G.toSimpleGraph.Walk s s) = .nil :=
  projectPath_eq_of_support_unattach _ hp _ (by simp)

/-- Projecting a path that starts with the edge `e` from `s` to `t` starts with the adjacency
from `s` to `t`; the edge is not a loop because the path does not revisit `s`. -/
@[simp]
theorem projectPath_cons {u : V(G)} (e : β) (h : G.IsLink e s t) (p : G.Walk t u)
    (hp : (cons e h p).IsPath) :
    ((cons e h p).projectPath hp : G.toSimpleGraph.Walk s u) =
      .cons (by
          rw [toSimpleGraph_adj]
          exact ⟨fun hst ↦ ((isPath_cons e h p).mp hp).2 (by
            simpa only [hst] using p.start_mem_support), h.adj⟩)
        (p.projectPath ((isPath_cons e h p).mp hp).1 : G.toSimpleGraph.Walk t u) :=
  projectPath_eq_of_support_unattach _ hp _ (by
    rw [SimpleGraph.Walk.support_cons, List.unattach_cons, support_projectPath, support_cons])

/-- Projection commutes with reversal. -/
@[simp]
theorem projectPath_reverse (p : G.Walk s t) (hp : p.reverse.IsPath) :
    (p.reverse.projectPath hp : G.toSimpleGraph.Walk t s) =
      (p.projectPath ((isPath_reverse p).mp hp) : G.toSimpleGraph.Walk s t).reverse :=
  projectPath_eq_of_support_unattach _ hp _ (by simp [support_reverse])

/-- Two projected paths are vertex-disjoint exactly when the original paths are. -/
theorem support_projectPath_disjoint_iff {s₁ t₁ s₂ t₂ : V(G)}
    (p : G.Walk s₁ t₁) (hp : p.IsPath) (q : G.Walk s₂ t₂) (hq : q.IsPath) :
    (p.projectPath hp : G.toSimpleGraph.Walk s₁ t₁).support.Disjoint
        (q.projectPath hq : G.toSimpleGraph.Walk s₂ t₂).support ↔
      p.support.Disjoint q.support := by
  rw [← List.Disjoint.map_iff Subtype.val_injective]
  simp only [List.map_subtype, List.map_id_fun', id_eq, support_projectPath]

/-- Projection preserves and reflects pairwise vertex-disjointness of path families, including
families whose members have different endpoints. -/
theorem pairwise_support_projectPath_disjoint_iff {ι : Type*} {s t : ι → V(G)}
    (P : ∀ i, G.Walk (s i) (t i)) (hP : ∀ i, (P i).IsPath) :
    (Pairwise fun i j ↦
      ((P i).projectPath (hP i) : G.toSimpleGraph.Walk (s i) (t i)).support.Disjoint
        ((P j).projectPath (hP j) : G.toSimpleGraph.Walk (s j) (t j)).support) ↔
      Pairwise fun i j ↦ (P i).support.Disjoint (P j).support := by
  constructor <;> intro h i j hij
  · exact (support_projectPath_disjoint_iff (P i) (hP i) (P j) (hP j)).mp (h hij)
  · exact (support_projectPath_disjoint_iff (P i) (hP i) (P j) (hP j)).mpr (h hij)

/-- Two projected paths share only their endpoints exactly when the original paths are internally
disjoint. This is the internal-disjointness characterization without importing the later
simple-graph Menger interface. -/
theorem internallyDisjoint_projectPath_iff (p q : G.Walk s t)
    (hp : p.IsPath) (hq : q.IsPath) :
    (∀ v ∈ (p.projectPath hp : G.toSimpleGraph.Walk s t).support,
        v ∈ (q.projectPath hq : G.toSimpleGraph.Walk s t).support → v = s ∨ v = t) ↔
      p.InternallyDisjoint q := by
  rw [internallyDisjoint_def]
  have hsp :
      (p.projectPath hp : G.toSimpleGraph.Walk s t).support.map Subtype.val = p.support := by
    simpa only [List.map_subtype, List.map_id_fun', id_eq] using support_projectPath p hp
  have hsq :
      (q.projectPath hq : G.toSimpleGraph.Walk s t).support.map Subtype.val = q.support := by
    simpa only [List.map_subtype, List.map_id_fun', id_eq] using support_projectPath q hq
  constructor
  · intro h x hxp hxq
    obtain ⟨x', hxp', rfl⟩ := List.mem_map.mp (hsp ▸ hxp)
    have hxq' : x' ∈ (q.projectPath hq : G.toSimpleGraph.Walk s t).support := by
      rw [← List.mem_map_of_injective Subtype.val_injective, hsq]
      exact hxq
    simpa only [Subtype.val_inj] using h x' hxp' hxq'
  · intro h x hxp hxq
    have hxp' : (x : α) ∈ p.support := by
      rw [← hsp]
      exact List.mem_map.mpr ⟨x, hxp, rfl⟩
    have hxq' : (x : α) ∈ q.support := by
      rw [← hsq]
      exact List.mem_map.mpr ⟨x, hxq, rfl⟩
    simpa only [Subtype.ext_iff] using h x hxp' hxq'

private theorem IsPath.exists_internal_vertex_of_not_adj' {x z : α} (p : G.Walk x z)
    (hp : p.IsPath) (hx : x ∈ V(G)) (hz : z ∈ V(G)) (hxz : x ≠ z)
    (hadj : ¬G.toSimpleGraph.Adj ⟨x, hx⟩ ⟨z, hz⟩) :
    ∃ v ∈ p.support, v ≠ x ∧ v ≠ z := by
  cases p with
  | nil => exact (hxz rfl).elim
  | @cons x y z e h p =>
      have hp' : p.IsPath ∧ x ∉ p.support := (isPath_cons e h p).mp hp
      have hyx : y ≠ x := fun hyx ↦ hp'.2 (by simpa only [hyx] using p.start_mem_support)
      have hyt : y ≠ z := by
        intro hyz
        subst z
        apply hadj
        exact ⟨fun hxy ↦ hyx (congrArg Subtype.val hxy).symm, ⟨e, h⟩⟩
      exact ⟨y, by simp, hyx, hyt⟩

/-- A path between distinct nonadjacent actual vertices has an internal vertex. -/
theorem IsPath.exists_internal_vertex_of_not_adj (p : G.Walk s t) (hp : p.IsPath)
    (hst : s ≠ t) (hadj : ¬G.toSimpleGraph.Adj s t) :
    ∃ v ∈ p.support, v ≠ s ∧ v ≠ t :=
  hp.exists_internal_vertex_of_not_adj' p s.property t.property
    (fun h ↦ hst (Subtype.ext h)) hadj

/-- For distinct nonadjacent terminals, projection preserves the distinct members of an
internally vertex-disjoint path family. The nonadjacency assumption is essential: parallel
one-edge paths have the same projection and no internal vertex. -/
theorem projectPath_injective_of_pairwise_internallyDisjoint {ι : Type*}
    (P : ι → G.Walk s t) (hpath : ∀ i, (P i).IsPath)
    (hdisj : Pairwise fun i j ↦ (P i).InternallyDisjoint (P j))
    (hst : s ≠ t) (hadj : ¬G.toSimpleGraph.Adj s t) :
    Function.Injective fun i ↦ ((P i).projectPath (hpath i) : G.toSimpleGraph.Walk s t) := by
  intro i j hij
  by_contra hne
  obtain ⟨v, hv, hvs, hvt⟩ := (hpath i).exists_internal_vertex_of_not_adj (P i) hst hadj
  have hij' :
      ((P i).projectPath (hpath i) : G.toSimpleGraph.Walk s t) =
        ((P j).projectPath (hpath j) : G.toSimpleGraph.Walk s t) := hij
  have hsupp : (P i).support = (P j).support := by
    simpa only [List.map_subtype, List.map_id_fun', id_eq, support_projectPath] using
      congrArg (fun q : G.toSimpleGraph.Walk s t ↦ q.support.map Subtype.val) hij'
  exact (internallyDisjoint_def.mp (hdisj hne) v hv (hsupp ▸ hv)).elim hvs hvt

end Graph.Walk
