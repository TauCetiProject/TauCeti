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
(`SerreGraph.subgraph`) formed by the vertices reachable from `v₀` by a path and the darts whose
source is reachable from `v₀`. Since a dart can be traversed once its source is reached, the dart
set is closed under reversal and contains both endpoints of every dart it retains.

Every path starting at `v₀` lifts to the component at `v₀`, so the component is always connected.
When `Γ` is preconnected the inclusion of the component into `Γ` is bijective on vertices and on
darts, giving an isomorphism `(Γ.component v₀).Iso Γ`. When `Γ` has no darts, the component of `v₀`
consists of `v₀` alone even if `Γ` has other isolated vertices.

## Main definitions

* `TauCeti.SerreGraph.componentVertices`, `TauCeti.SerreGraph.componentDarts`: the vertices and
  darts reachable from `v₀`.
* `TauCeti.SerreGraph.component`: the connected component of `v₀` as a `SerreGraph`.
* `TauCeti.SerreGraph.componentBase`: `v₀` as a vertex of its component.
* `TauCeti.SerreGraph.componentInclusion`: the inclusion morphism `(Γ.component v₀).Hom Γ`.
* `TauCeti.SerreGraph.componentIsoOfPreconnected`: the isomorphism `(Γ.component v₀).Iso Γ` when `Γ`
  is preconnected.

## Main results

* `TauCeti.SerreGraph.exists_component_path`: every path from `v₀` lifts to `Γ.component v₀`.
* `TauCeti.SerreGraph.component_connected`: `Γ.component v₀` is connected.

## References

* J.-P. Serre, *Trees*, Chapter I, §§2.1–2.2.
-/

public section

universe u v

namespace TauCeti.SerreGraph

variable (Γ : SerreGraph.{u, v}) (v₀ : Γ.V)

/-- The vertices of `Γ` reachable from `v₀` by an edge path. -/
def componentVertices : Set Γ.V :=
  {a | Nonempty (Γ.Path v₀ a)}

theorem mem_componentVertices_iff {a : Γ.V} :
    a ∈ Γ.componentVertices v₀ ↔ Nonempty (Γ.Path v₀ a) :=
  Iff.rfl

/-- Every vertex belongs to its own connected component. -/
@[simp] theorem self_mem_componentVertices : v₀ ∈ Γ.componentVertices v₀ :=
  ⟨.nil⟩

/-- The darts of `Γ` whose source is reachable from `v₀` by an edge path. -/
def componentDarts : Set Γ.E :=
  {e | Nonempty (Γ.Path v₀ (Γ.src e))}

theorem mem_componentDarts_iff {e : Γ.E} :
    e ∈ Γ.componentDarts v₀ ↔ Nonempty (Γ.Path v₀ (Γ.src e)) :=
  Iff.rfl

/-- The source of a dart in the component of `v₀` belongs to the component of `v₀`. -/
theorem src_mem_componentVertices {e : Γ.E} (he : e ∈ Γ.componentDarts v₀) :
    Γ.src e ∈ Γ.componentVertices v₀ :=
  he

/-- A dart whose source is reachable from `v₀` has a target reachable from `v₀`, by traversing the
dart itself, so its reverse also belongs to `componentDarts`. -/
theorem rev_mem_componentDarts {e : Γ.E} (he : e ∈ Γ.componentDarts v₀) :
    Γ.rev e ∈ Γ.componentDarts v₀ :=
  he.map fun p => p.cons (Γ.dart e)

@[simp] theorem rev_mem_componentDarts_iff {e : Γ.E} :
    Γ.rev e ∈ Γ.componentDarts v₀ ↔ e ∈ Γ.componentDarts v₀ :=
  ⟨fun he => Γ.rev_rev e ▸ Γ.rev_mem_componentDarts v₀ he, Γ.rev_mem_componentDarts v₀⟩

/-- The target of a dart in the component of `v₀` belongs to the component of `v₀`. -/
theorem tgt_mem_componentVertices {e : Γ.E} (he : e ∈ Γ.componentDarts v₀) :
    Γ.tgt e ∈ Γ.componentVertices v₀ :=
  Γ.rev_mem_componentDarts v₀ he

/-- The connected component of `v₀` in `Γ`: the subgraph on the vertices and darts reachable from
`v₀`. -/
abbrev component : SerreGraph.{u, v} :=
  Γ.subgraph (Γ.componentVertices v₀) (Γ.componentDarts v₀)
    (fun _ => Γ.src_mem_componentVertices v₀)
    (fun _ => Γ.rev_mem_componentDarts v₀)

/-- The base vertex `v₀` as a vertex of its connected component. -/
abbrev componentBase : (Γ.component v₀).V :=
  ⟨v₀, Γ.self_mem_componentVertices v₀⟩

@[simp] theorem componentBase_val : (Γ.componentBase v₀).1 = v₀ :=
  (rfl)

/-- The inclusion morphism from the connected component of `v₀` into `Γ`. -/
abbrev componentInclusion : (Γ.component v₀).Hom Γ :=
  Γ.subgraphInclusion _ _ _ _

/-- Every dart traversed by a path starting at `v₀` belongs to the component of `v₀`. -/
theorem mem_componentDarts_of_mem_darts {a : Γ.V} (p : Γ.Path v₀ a) {e : Γ.E}
    (he : e ∈ Path.darts Γ p) : e ∈ Γ.componentDarts v₀ := by
  obtain ⟨q, _, _⟩ := Path.exists_eq_cons_comp_of_mem_darts Γ p he
  exact ⟨q⟩

/-- Every path starting at `v₀` lifts along `componentInclusion` to `Γ.component v₀`. -/
theorem exists_component_path {a : Γ.V} (p : Γ.Path v₀ a) :
    ∃ q : (Γ.component v₀).Path (Γ.componentBase v₀)
      ⟨a, (Γ.mem_componentVertices_iff v₀).mpr ⟨p⟩⟩,
      (Γ.componentInclusion v₀).toPrefunctor.mapPath q = p :=
  Γ.exists_subgraph_path (Γ.componentVertices v₀) (Γ.componentDarts v₀) _ _ p
    (fun _ he => Γ.mem_componentDarts_of_mem_darts v₀ p he) _ _

/-- Every vertex of `Γ.component v₀` is reachable from `componentBase` within the component. -/
theorem component_reachable (a : (Γ.component v₀).V) :
    Nonempty ((Γ.component v₀).Path (Γ.componentBase v₀) a) := by
  obtain ⟨a, ha⟩ := a
  obtain ⟨p⟩ := (Γ.mem_componentVertices_iff v₀).mp ha
  exact ⟨(Γ.exists_component_path v₀ p).choose⟩

/-- The connected component of a vertex is preconnected. -/
theorem component_preconnected : (Γ.component v₀).Preconnected :=
  preconnected_of_forall_nonempty_path _ (Γ.componentBase v₀) (Γ.component_reachable v₀)

/-- The connected component of a vertex is connected. -/
theorem component_connected : (Γ.component v₀).Connected :=
  (connected_iff _).mpr ⟨⟨Γ.componentBase v₀⟩, Γ.component_preconnected v₀⟩

section Preconnected

variable {Γ}

/-- Over a preconnected graph, the inclusion of `Γ.component v₀` is bijective on vertices. -/
theorem componentInclusion_mapV_bijective_of_preconnected (hΓ : Γ.Preconnected) :
    Function.Bijective (Γ.componentInclusion v₀).mapV :=
  ⟨Γ.subgraphInclusion_mapV_injective _ _ _ _,
    fun a => ⟨⟨a, (Γ.mem_componentVertices_iff v₀).mpr (Γ.preconnected_iff.mp hΓ v₀ a)⟩, rfl⟩⟩

/-- Over a preconnected graph, the inclusion of `Γ.component v₀` is bijective on darts. -/
theorem componentInclusion_mapE_bijective_of_preconnected (hΓ : Γ.Preconnected) :
    Function.Bijective (Γ.componentInclusion v₀).mapE :=
  ⟨Γ.subgraphInclusion_mapE_injective _ _ _ _,
    fun e => ⟨⟨e, (Γ.mem_componentDarts_iff v₀).mpr (Γ.preconnected_iff.mp hΓ v₀ (Γ.src e))⟩,
      rfl⟩⟩

/-- Over a preconnected graph, the connected component of any vertex is isomorphic to the whole
graph through `componentInclusion`. -/
noncomputable def componentIsoOfPreconnected (hΓ : Γ.Preconnected) : (Γ.component v₀).Iso Γ :=
  (Γ.componentInclusion v₀).toIso
    (componentInclusion_mapV_bijective_of_preconnected v₀ hΓ)
    (componentInclusion_mapE_bijective_of_preconnected v₀ hΓ)

@[simp] theorem componentIsoOfPreconnected_equivV_apply (hΓ : Γ.Preconnected)
    (a : (Γ.component v₀).V) :
    (componentIsoOfPreconnected v₀ hΓ).equivV a = a.1 :=
  Hom.toIso_equivV_apply ..

@[simp] theorem componentIsoOfPreconnected_equivE_apply (hΓ : Γ.Preconnected)
    (e : (Γ.component v₀).E) :
    (componentIsoOfPreconnected v₀ hΓ).equivE e = e.1 :=
  Hom.toIso_equivE_apply ..

@[simp] theorem componentIsoOfPreconnected_toHom (hΓ : Γ.Preconnected) :
    (componentIsoOfPreconnected v₀ hΓ).toHom = Γ.componentInclusion v₀ :=
  Hom.toIso_toHom ..

end Preconnected

section IsEmpty

variable [IsEmpty Γ.E]

instance : IsEmpty (Γ.component v₀).E :=
  ⟨fun e => isEmptyElim e.1⟩

instance : Unique (Γ.component v₀).V where
  default := Γ.componentBase v₀
  uniq a := Subtype.ext <| by
    obtain ⟨p⟩ := a.2
    exact (Γ.eq_of_path_of_forall_src_eq_tgt isEmptyElim p).symm

end IsEmpty

end TauCeti.SerreGraph
