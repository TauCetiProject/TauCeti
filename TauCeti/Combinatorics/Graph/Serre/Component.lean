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

The connected component of a vertex `v₀` in a Serre graph `Γ` is the subgraph
(`TauCeti.SerreGraph.subgraph`) consisting of the vertices reachable from `v₀` by a path of `Γ`
and the darts whose source is reachable from `v₀`. Reversing such a dart appends it to a path from
`v₀`, so the dart set is closed under reversal.

Every path starting at `v₀` lifts to `Γ.component v₀`, so `Γ.component v₀` is connected. When `Γ`
is preconnected, every vertex and dart of `Γ` lies in `Γ.component v₀`, and the inclusion
`Γ.componentInclusion v₀` upgrades to an isomorphism `(Γ.component v₀).Iso Γ`. This identifies the
quotient of a covering construction based at `v₀`, such as the Bass–Serre tree of a graph of
groups, with the connected component of `v₀` in general and with `Γ` itself when `Γ` is
preconnected.

## Main definitions

* `TauCeti.SerreGraph.componentVertices` and `TauCeti.SerreGraph.componentDarts`: the vertices and
  darts reachable from `v₀`.
* `TauCeti.SerreGraph.component`: the connected component of `v₀` as a `SerreGraph`.
* `TauCeti.SerreGraph.componentBase` and `TauCeti.SerreGraph.componentInclusion`: the base vertex
  and the inclusion morphism into `Γ`.
* `TauCeti.SerreGraph.componentIsoOfPreconnected`: the isomorphism `(Γ.component v₀).Iso Γ` when
  `Γ` is preconnected.

## Main results

* `TauCeti.SerreGraph.exists_component_path`: every path in `Γ` starting at `v₀` lifts to
  `Γ.component v₀`.
* `TauCeti.SerreGraph.component_connected`: `Γ.component v₀` is connected.

## References

* J.-P. Serre, *Trees*, Chapter I, §2.1.
-/

public section

universe u v

namespace TauCeti
namespace SerreGraph

variable (Γ : SerreGraph.{u, v}) (v₀ : Γ.V)

/-- The vertices of `Γ` reachable by a path from `v₀`. -/
@[expose] def componentVertices : Set Γ.V :=
  {v | Nonempty (Γ.Path v₀ v)}

@[simp] theorem mem_componentVertices_iff {v : Γ.V} :
    v ∈ Γ.componentVertices v₀ ↔ Nonempty (Γ.Path v₀ v) :=
  Iff.rfl

/-- The base vertex belongs to its own connected component. -/
@[simp] theorem self_mem_componentVertices : v₀ ∈ Γ.componentVertices v₀ :=
  ⟨.nil⟩

/-- The darts of `Γ` whose source is reachable by a path from `v₀`. -/
@[expose] def componentDarts : Set Γ.E :=
  {e | Nonempty (Γ.Path v₀ (Γ.src e))}

@[simp] theorem mem_componentDarts_iff {e : Γ.E} :
    e ∈ Γ.componentDarts v₀ ↔ Nonempty (Γ.Path v₀ (Γ.src e)) :=
  Iff.rfl

/-- The source of a dart in the component of `v₀` lies in the component of `v₀`. -/
theorem src_mem_componentVertices {e : Γ.E} (he : e ∈ Γ.componentDarts v₀) :
    Γ.src e ∈ Γ.componentVertices v₀ :=
  he

/-- Reversing a dart whose source is reachable from `v₀` gives a dart whose source is reachable
from `v₀`, by traversing the dart itself. -/
theorem rev_mem_componentDarts {e : Γ.E} (he : e ∈ Γ.componentDarts v₀) :
    Γ.rev e ∈ Γ.componentDarts v₀ :=
  let ⟨p⟩ := he
  ⟨p.cons (Γ.dart e)⟩

@[simp] theorem rev_mem_componentDarts_iff {e : Γ.E} :
    Γ.rev e ∈ Γ.componentDarts v₀ ↔ e ∈ Γ.componentDarts v₀ :=
  ⟨fun h => Γ.rev_rev e ▸ Γ.rev_mem_componentDarts v₀ h, Γ.rev_mem_componentDarts v₀⟩

/-- The target of a dart in the component of `v₀` lies in the component of `v₀`. -/
theorem tgt_mem_componentVertices {e : Γ.E} (he : e ∈ Γ.componentDarts v₀) :
    Γ.tgt e ∈ Γ.componentVertices v₀ :=
  Γ.src_mem_componentVertices v₀ (Γ.rev_mem_componentDarts v₀ he)

/-- Every dart traversed by a path starting at `v₀` belongs to the component of `v₀`. -/
theorem mem_componentDarts_of_mem_darts {v : Γ.V} (p : Γ.Path v₀ v) {e : Γ.E}
    (he : e ∈ Path.darts Γ p) : e ∈ Γ.componentDarts v₀ := by
  obtain ⟨q, _, _⟩ := Path.exists_eq_cons_comp_of_mem_darts Γ p he
  exact ⟨q⟩

/-- The connected component of `v₀` in `Γ`, as the subgraph of vertices and darts reachable from
`v₀`. -/
abbrev component : SerreGraph.{u, v} :=
  Γ.subgraph (Γ.componentVertices v₀) (Γ.componentDarts v₀)
    (fun _ => Γ.src_mem_componentVertices v₀) (fun _ => Γ.rev_mem_componentDarts v₀)

/-- The distinguished base vertex `v₀` inside `Γ.component v₀`. -/
@[expose] def componentBase : (Γ.component v₀).V :=
  ⟨v₀, Γ.self_mem_componentVertices v₀⟩

@[simp] theorem componentBase_val : (Γ.componentBase v₀).1 = v₀ :=
  (rfl)

/-- The inclusion morphism of `Γ.component v₀` into `Γ`. -/
abbrev componentInclusion : (Γ.component v₀).Hom Γ :=
  Γ.subgraphInclusion _ _ _ _

/-- Every path in `Γ` starting at `v₀` lifts through `Γ.componentInclusion v₀`. -/
theorem exists_component_path {v : Γ.V} (p : Γ.Path v₀ v) :
    ∃ q : (Γ.component v₀).Path (Γ.componentBase v₀) ⟨v, (Γ.mem_componentVertices_iff v₀).mpr ⟨p⟩⟩,
      (Γ.componentInclusion v₀).toPrefunctor.mapPath q = p :=
  Γ.exists_subgraph_path (Γ.componentVertices v₀) (Γ.componentDarts v₀) _ _ p
    (fun _ he => Γ.mem_componentDarts_of_mem_darts v₀ p he) _
    ((Γ.mem_componentVertices_iff v₀).mpr ⟨p⟩)

/-- Every vertex of `Γ.component v₀` is reachable in `Γ.component v₀` from `Γ.componentBase v₀`. -/
theorem component_reachable (a : (Γ.component v₀).V) :
    Nonempty ((Γ.component v₀).Path (Γ.componentBase v₀) a) := by
  obtain ⟨v, hp⟩ := a
  obtain ⟨p⟩ := (Γ.mem_componentVertices_iff v₀).mp hp
  exact ⟨(Γ.exists_component_path v₀ p).choose⟩

/-- The connected component of `v₀` is preconnected. -/
theorem component_preconnected : (Γ.component v₀).Preconnected :=
  (Γ.component v₀).preconnected_of_forall_nonempty_path (Γ.componentBase v₀)
    (Γ.component_reachable v₀)

/-- The connected component of `v₀` is connected. -/
theorem component_connected : (Γ.component v₀).Connected :=
  (Γ.component v₀).connected_iff.mpr ⟨⟨Γ.componentBase v₀⟩, Γ.component_preconnected v₀⟩

section Preconnected

variable {Γ v₀}

/-- In a preconnected graph, every vertex belongs to the component of `v₀`. -/
theorem componentVertices_eq_univ_of_preconnected (hΓ : Γ.Preconnected) :
    Γ.componentVertices v₀ = Set.univ :=
  Set.eq_univ_of_forall fun v => Γ.preconnected_iff.mp hΓ v₀ v

/-- In a preconnected graph, every dart belongs to the component of `v₀`. -/
theorem componentDarts_eq_univ_of_preconnected (hΓ : Γ.Preconnected) :
    Γ.componentDarts v₀ = Set.univ :=
  Set.eq_univ_of_forall fun e => Γ.preconnected_iff.mp hΓ v₀ (Γ.src e)

/-- When `Γ` is preconnected, the inclusion of `Γ.component v₀` is bijective on vertices. -/
theorem componentInclusion_mapV_bijective_of_preconnected (hΓ : Γ.Preconnected) :
    Function.Bijective (Γ.componentInclusion v₀).mapV :=
  ⟨Γ.subgraphInclusion_mapV_injective _ _ _ _,
    fun v => ⟨⟨v, (Γ.mem_componentVertices_iff v₀).mpr (Γ.preconnected_iff.mp hΓ v₀ v)⟩, rfl⟩⟩

/-- When `Γ` is preconnected, the inclusion of `Γ.component v₀` is bijective on darts. -/
theorem componentInclusion_mapE_bijective_of_preconnected (hΓ : Γ.Preconnected) :
    Function.Bijective (Γ.componentInclusion v₀).mapE :=
  ⟨Γ.subgraphInclusion_mapE_injective _ _ _ _,
    fun e => ⟨⟨e, (Γ.mem_componentDarts_iff v₀).mpr (Γ.preconnected_iff.mp hΓ v₀ (Γ.src e))⟩, rfl⟩⟩

variable (Γ v₀) in
/-- When `Γ` is preconnected, the inclusion of `Γ.component v₀` into `Γ` is an isomorphism of
Serre graphs. -/
noncomputable def componentIsoOfPreconnected (hΓ : Γ.Preconnected) : (Γ.component v₀).Iso Γ :=
  (Γ.componentInclusion v₀).toIso (componentInclusion_mapV_bijective_of_preconnected hΓ)
    (componentInclusion_mapE_bijective_of_preconnected hΓ)

@[simp] theorem componentIsoOfPreconnected_equivV_apply (hΓ : Γ.Preconnected)
    (a : (Γ.component v₀).V) : (Γ.componentIsoOfPreconnected v₀ hΓ).equivV a = a.1 := by
  simp [componentIsoOfPreconnected]

@[simp] theorem componentIsoOfPreconnected_equivE_apply (hΓ : Γ.Preconnected)
    (e : (Γ.component v₀).E) : (Γ.componentIsoOfPreconnected v₀ hΓ).equivE e = e.1 := by
  simp [componentIsoOfPreconnected]

@[simp] theorem componentIsoOfPreconnected_toHom (hΓ : Γ.Preconnected) :
    (Γ.componentIsoOfPreconnected v₀ hΓ).toHom = Γ.componentInclusion v₀ := by
  simp [componentIsoOfPreconnected]

end Preconnected

end SerreGraph
end TauCeti
