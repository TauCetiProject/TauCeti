/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Iso
public import TauCeti.Combinatorics.Graph.Serre.Path.Basic

/-!
# Connected components of Serre graphs

The connected component of a vertex `v` in a Serre graph `Γ` is the subgraph
`SerreGraph.component Γ v` consisting of all vertices reachable from `v` by a Serre path and all
darts incident to them. Every dart starting in the component ends in it as well, so the dart set
equals `Γ.inducedDarts (Γ.componentVertices v)` and is closed under reversal.

Every path in `Γ` starting in the component remains in it and lifts through the inclusion
`SerreGraph.componentInclusion`. Consequently `Γ.component v` is connected, and when `Γ` is
preconnected the inclusion is an isomorphism `SerreGraph.componentIso`.

## Main definitions

* `TauCeti.SerreGraph.componentVertices`: the vertices reachable from a base vertex.
* `TauCeti.SerreGraph.componentDarts`: the darts starting at vertices reachable from the base
  vertex.
* `TauCeti.SerreGraph.component`: the connected component of a vertex as a Serre subgraph.
* `TauCeti.SerreGraph.componentBase`: the base vertex viewed in its component.
* `TauCeti.SerreGraph.componentInclusion`: the inclusion morphism into the ambient graph.
* `TauCeti.SerreGraph.componentIso`: the isomorphism `Γ.component v ≃ Γ` when `Γ` is preconnected.

## References

* J.-P. Serre, *Trees*, Chapter I, §2.1–§2.2.
-/

public section

universe u v

namespace TauCeti.SerreGraph

variable (Γ : SerreGraph.{u, v}) (v : Γ.V)

/-- The vertices of `Γ` reachable from `v` by a path. -/
def componentVertices : Set Γ.V :=
  {a | Nonempty (Γ.Path v a)}

@[simp] theorem mem_componentVertices_iff {a : Γ.V} :
    a ∈ Γ.componentVertices v ↔ Nonempty (Γ.Path v a) := (Iff.rfl)

theorem self_mem_componentVertices : v ∈ Γ.componentVertices v :=
  ⟨.nil⟩

/-- Reachability from `v` is preserved along paths. -/
theorem mem_componentVertices_of_path {a b : Γ.V} (ha : a ∈ Γ.componentVertices v)
    (p : Γ.Path a b) : b ∈ Γ.componentVertices v :=
  let ⟨q⟩ := ha; ⟨q.comp p⟩

/-- The darts of `Γ` issuing from vertices in the component of `v`. -/
def componentDarts : Set Γ.E :=
  {e | Γ.src e ∈ Γ.componentVertices v}

@[simp] theorem mem_componentDarts_iff {e : Γ.E} :
    e ∈ Γ.componentDarts v ↔ Γ.src e ∈ Γ.componentVertices v := (Iff.rfl)

/-- The source of a dart in the component of `v` lies in the component of `v`. -/
theorem src_mem_componentVertices {e : Γ.E} (he : e ∈ Γ.componentDarts v) :
    Γ.src e ∈ Γ.componentVertices v := he

/-- The target of a dart in the component of `v` lies in the component of `v`. -/
theorem tgt_mem_componentVertices {e : Γ.E} (he : e ∈ Γ.componentDarts v) :
    Γ.tgt e ∈ Γ.componentVertices v :=
  Γ.mem_componentVertices_of_path v he (Γ.dart e).toPath

/-- The dart set of a connected component is closed under reversal. -/
theorem rev_mem_componentDarts_iff (e : Γ.E) :
    Γ.rev e ∈ Γ.componentDarts v ↔ e ∈ Γ.componentDarts v :=
  ⟨fun h => by simpa using Γ.tgt_mem_componentVertices v h,
    fun h => by simpa using Γ.tgt_mem_componentVertices v h⟩

/-- The darts of the component of `v` are precisely the darts induced by its vertices. -/
theorem componentDarts_eq_inducedDarts :
    Γ.componentDarts v = Γ.inducedDarts (Γ.componentVertices v) := by
  ext e
  rw [mem_componentDarts_iff, mem_inducedDarts_iff]
  exact ⟨fun h => ⟨h, Γ.tgt_mem_componentVertices v h⟩, fun h => h.1⟩

/-- The connected component of `v` in `Γ`, as a Serre subgraph. -/
abbrev component : SerreGraph.{u, v} :=
  Γ.subgraph (Γ.componentVertices v) (Γ.componentDarts v)
    (fun _ => Γ.src_mem_componentVertices v) fun e => (Γ.rev_mem_componentDarts_iff v e).mpr

/-- The base vertex `v` viewed as a vertex of its connected component. -/
def componentBase : (Γ.component v).V :=
  ⟨v, Γ.self_mem_componentVertices v⟩

@[simp] theorem componentBase_val : (Γ.componentBase v).1 = v := (rfl)

/-- The inclusion of the connected component of `v` into `Γ`. -/
abbrev componentInclusion : (Γ.component v).Hom Γ :=
  Γ.subgraphInclusion _ _ _ _

/-- Every dart traversed by a path starting in the component of `v` lies in that component. -/
theorem mem_componentDarts_of_mem_darts {a b : Γ.V} (ha : a ∈ Γ.componentVertices v)
    (p : Γ.Path a b) {e : Γ.E} (he : e ∈ Path.darts Γ p) : e ∈ Γ.componentDarts v := by
  obtain ⟨q, -, rfl⟩ := Path.exists_eq_cons_comp_of_mem_darts Γ p he
  exact Γ.mem_componentVertices_of_path v ha q

/-- Every path starting in the component of `v` lifts to a path in the component. -/
theorem exists_component_path {a b : Γ.V} (ha : a ∈ Γ.componentVertices v) (p : Γ.Path a b) :
    ∃ q : (Γ.component v).Path ⟨a, ha⟩ ⟨b, Γ.mem_componentVertices_of_path v ha p⟩,
      (Γ.componentInclusion v).toPrefunctor.mapPath q = p :=
  Γ.exists_subgraph_path _ _ _ _ p (fun _ he => Γ.mem_componentDarts_of_mem_darts v ha p he)
    ha (Γ.mem_componentVertices_of_path v ha p)

/-- The connected component of `v` is preconnected. -/
theorem component_preconnected : (Γ.component v).Preconnected :=
  (Γ.component v).preconnected_of_forall_nonempty_path (Γ.componentBase v) fun ⟨a, ha⟩ => by
    obtain ⟨p⟩ := ha
    obtain ⟨q, -⟩ := Γ.exists_component_path v (Γ.self_mem_componentVertices v) p
    exact ⟨q⟩

/-- The connected component of `v` is connected. -/
theorem component_connected : (Γ.component v).Connected :=
  ((Γ.component v).connected_iff).mpr ⟨⟨Γ.componentBase v⟩, Γ.component_preconnected v⟩

/-- In a graph all of whose darts are loops, the component of `v` has only the vertex `v`. -/
theorem componentVertices_eq_singleton_of_forall_src_eq_tgt (h : ∀ e, Γ.src e = Γ.tgt e) :
    Γ.componentVertices v = {v} := by
  ext a
  rw [mem_componentVertices_iff, Γ.nonempty_path_iff_of_forall_src_eq_tgt h, Set.mem_singleton_iff,
    eq_comm]

/-- In a preconnected graph every vertex belongs to the component of `v`. -/
theorem componentVertices_eq_univ (hΓ : Γ.Preconnected) : Γ.componentVertices v = Set.univ :=
  Set.eq_univ_of_forall fun a => Γ.preconnected_iff.mp hΓ v a

/-- In a preconnected graph every dart belongs to the component of `v`. -/
theorem componentDarts_eq_univ (hΓ : Γ.Preconnected) : Γ.componentDarts v = Set.univ :=
  Set.eq_univ_of_forall fun e => Γ.preconnected_iff.mp hΓ v (Γ.src e)

/-- In a preconnected graph, the inclusion of the component of `v` is an isomorphism with `Γ`. -/
noncomputable def componentIso (hΓ : Γ.Preconnected) : (Γ.component v).Iso Γ :=
  (Γ.componentInclusion v).toIso
    ⟨Subtype.val_injective, fun a => ⟨⟨a, Γ.preconnected_iff.mp hΓ v a⟩, rfl⟩⟩
    ⟨Subtype.val_injective, fun e => ⟨⟨e, Γ.preconnected_iff.mp hΓ v (Γ.src e)⟩, rfl⟩⟩

@[simp] theorem componentIso_equivV_apply (hΓ : Γ.Preconnected) (a : (Γ.component v).V) :
    (Γ.componentIso v hΓ).equivV a = a.1 :=
  Hom.toIso_equivV_apply _ _ _ a

@[simp] theorem componentIso_equivE_apply (hΓ : Γ.Preconnected) (e : (Γ.component v).E) :
    (Γ.componentIso v hΓ).equivE e = e.1 :=
  Hom.toIso_equivE_apply _ _ _ e

@[simp] theorem componentIso_toHom (hΓ : Γ.Preconnected) :
    (Γ.componentIso v hΓ).toHom = Γ.componentInclusion v :=
  Hom.toIso_toHom _ _ _

end TauCeti.SerreGraph
