/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Iso
public import TauCeti.Combinatorics.Graph.Serre.Path.Basic

/-!
# Connected components of a Serre graph

For a vertex `v₀` of a Serre graph `Γ`, the vertices reachable from `v₀` by a path and the darts
starting at a reachable vertex form a connected subgraph `Γ.component v₀`. Because reversing a dart
moves its source to its target, which is reached by appending the dart, the retained darts are
closed under reversal and coincide with the darts induced by the reachable vertices.

Every path in `Γ` starting at `v₀` lifts to `Γ.component v₀`, and when `Γ` is preconnected the
inclusion `Γ.componentInclusion v₀ : (Γ.component v₀).Hom Γ` is an isomorphism of Serre graphs
(`SerreGraph.componentInclusionIso`). Over an edgeless graph, `Γ.component v₀` consists of `v₀`
alone, even when `Γ` has other isolated vertices.

## Main declarations

* `TauCeti.SerreGraph.componentVertices`, `TauCeti.SerreGraph.componentDarts`: the vertices and
  darts reachable from a base vertex `v₀`.
* `TauCeti.SerreGraph.component`: the connected component of `v₀` as a `SerreGraph`.
* `TauCeti.SerreGraph.componentBase`, `TauCeti.SerreGraph.componentInclusion`: the base vertex in
  the component and its inclusion into `Γ`.
* `TauCeti.SerreGraph.component_connected`: `Γ.component v₀` is connected.
* `TauCeti.SerreGraph.componentInclusionIso`: for preconnected `Γ`, the inclusion of
  `Γ.component v₀` is an isomorphism onto `Γ`.

## References

* J.-P. Serre, *Trees*, Chapter I, §§2.1–2.2.
-/

public section

universe u v

namespace TauCeti.SerreGraph

variable (Γ : SerreGraph.{u, v}) (v₀ : Γ.V)

/-- The vertices of `Γ` reachable from `v₀` by a path. -/
def componentVertices : Set Γ.V :=
  {v | Nonempty (Γ.Path v₀ v)}

@[simp] theorem mem_componentVertices_iff (v : Γ.V) :
    v ∈ Γ.componentVertices v₀ ↔ Nonempty (Γ.Path v₀ v) :=
  Iff.rfl

/-- The base vertex belongs to its own connected component. -/
theorem base_mem_componentVertices : v₀ ∈ Γ.componentVertices v₀ :=
  ⟨.nil⟩

/-- The darts of `Γ` starting at a vertex reachable from `v₀`. -/
def componentDarts : Set Γ.E :=
  {e | Nonempty (Γ.Path v₀ (Γ.src e))}

@[simp] theorem mem_componentDarts_iff (e : Γ.E) :
    e ∈ Γ.componentDarts v₀ ↔ Nonempty (Γ.Path v₀ (Γ.src e)) :=
  Iff.rfl

/-- The source of a dart in the component of `v₀` lies in the component of `v₀`. -/
theorem src_mem_componentVertices {e : Γ.E} (he : e ∈ Γ.componentDarts v₀) :
    Γ.src e ∈ Γ.componentVertices v₀ :=
  he

/-- The target of a dart in the component of `v₀` lies in the component of `v₀`. -/
theorem tgt_mem_componentVertices {e : Γ.E} (he : e ∈ Γ.componentDarts v₀) :
    Γ.tgt e ∈ Γ.componentVertices v₀ :=
  he.map (·.cons (Γ.dart e))

/-- The darts of a connected component are closed under reversal. -/
theorem rev_mem_componentDarts_iff (e : Γ.E) :
    Γ.rev e ∈ Γ.componentDarts v₀ ↔ e ∈ Γ.componentDarts v₀ := by
  refine ⟨fun he => ?_, fun he => ?_⟩
  · rw [mem_componentDarts_iff]
    simpa only [mem_componentVertices_iff, Γ.tgt_rev] using Γ.tgt_mem_componentVertices v₀ he
  · rw [mem_componentDarts_iff, Γ.src_rev]
    exact (Γ.mem_componentVertices_iff v₀ _).1 (Γ.tgt_mem_componentVertices v₀ he)

/-- The darts of the component of `v₀` are the darts induced on its vertices. -/
theorem componentDarts_eq_inducedDarts :
    Γ.componentDarts v₀ = Γ.inducedDarts (Γ.componentVertices v₀) := by
  ext e
  rw [mem_inducedDarts_iff]
  exact ⟨fun he => ⟨he, Γ.tgt_mem_componentVertices v₀ he⟩, fun he => he.1⟩

/-- The connected component of `v₀` in `Γ`, as the subgraph of vertices and darts reachable from
`v₀`. -/
abbrev component : SerreGraph.{u, v} :=
  Γ.subgraph (Γ.componentVertices v₀) (Γ.componentDarts v₀)
    (fun _ => Γ.src_mem_componentVertices v₀)
    fun e => (Γ.rev_mem_componentDarts_iff v₀ e).mpr

/-- The base vertex `v₀` viewed inside its connected component. -/
abbrev componentBase : (Γ.component v₀).V :=
  ⟨v₀, Γ.base_mem_componentVertices v₀⟩

@[simp] theorem componentBase_val : (Γ.componentBase v₀).1 = v₀ :=
  (rfl)

/-- The connected component of a vertex contains that vertex. -/
instance : Nonempty (Γ.component v₀).V :=
  ⟨Γ.componentBase v₀⟩

/-- Inclusion of the connected component of `v₀` into the ambient graph. -/
abbrev componentInclusion : (Γ.component v₀).Hom Γ :=
  Γ.subgraphInclusion _ _ _ _

/-- Every dart traversed by a path starting at `v₀` belongs to `Γ.componentDarts v₀`. -/
theorem mem_componentDarts_of_mem_darts {a : Γ.V} (p : Γ.Path v₀ a) {e : Γ.E}
    (he : e ∈ Path.darts Γ p) : e ∈ Γ.componentDarts v₀ := by
  induction p with
  | nil => simp at he
  | cons p f ih =>
    simp only [Path.darts_cons, List.mem_append, List.mem_singleton] at he
    rcases he with he | rfl
    · exact ih he
    · rw [mem_componentDarts_iff, f.2.1]
      exact ⟨p⟩

/-- Every path in `Γ` starting at `v₀` lifts through the inclusion of `Γ.component v₀`. -/
theorem exists_component_path {a : Γ.V} (p : Γ.Path v₀ a) :
    ∃ q : (Γ.component v₀).Path (Γ.componentBase v₀)
        ⟨a, (Γ.mem_componentVertices_iff v₀ a).2 ⟨p⟩⟩,
      (Γ.componentInclusion v₀).toPrefunctor.mapPath q = p :=
  Γ.exists_subgraph_path _ _ _ _ p (fun _ => Γ.mem_componentDarts_of_mem_darts v₀ p) _ _

/-- Every vertex of `Γ.component v₀` is joined to `componentBase v₀` by a path inside the
component. -/
theorem component_reachable (a : (Γ.component v₀).V) :
    Nonempty ((Γ.component v₀).Path (Γ.componentBase v₀) a) := by
  obtain ⟨a, ha⟩ := a
  obtain ⟨p⟩ := (Γ.mem_componentVertices_iff v₀ a).1 ha
  obtain ⟨q, -⟩ := Γ.exists_component_path v₀ p
  exact ⟨q⟩

/-- The connected component of a vertex is preconnected. -/
theorem component_preconnected : (Γ.component v₀).Preconnected :=
  (Γ.component v₀).preconnected_of_forall_nonempty_path (Γ.componentBase v₀)
    (Γ.component_reachable v₀)

/-- The connected component of a vertex is connected. -/
theorem component_connected : (Γ.component v₀).Connected :=
  ((Γ.component v₀).connected_iff).2 ⟨⟨Γ.componentBase v₀⟩, Γ.component_preconnected v₀⟩

section Preconnected

variable {Γ}

/-- In a preconnected graph, every vertex lies in the component of `v₀`. -/
theorem componentInclusion_mapV_bijective (hΓ : Γ.Preconnected) :
    Function.Bijective (Γ.componentInclusion v₀).mapV :=
  ⟨Γ.subgraphInclusion_mapV_injective _ _ _ _,
    fun a => ⟨⟨a, (Γ.mem_componentVertices_iff v₀ a).2 (Γ.preconnected_iff.1 hΓ v₀ a)⟩, rfl⟩⟩

/-- In a preconnected graph, every dart lies in the component of `v₀`. -/
theorem componentInclusion_mapE_bijective (hΓ : Γ.Preconnected) :
    Function.Bijective (Γ.componentInclusion v₀).mapE :=
  ⟨Γ.subgraphInclusion_mapE_injective _ _ _ _,
    fun e => ⟨⟨e, (Γ.mem_componentDarts_iff v₀ e).2 (Γ.preconnected_iff.1 hΓ v₀ (Γ.src e))⟩,
      rfl⟩⟩

/-- When `Γ` is preconnected, the connected component of `v₀` is isomorphic to `Γ` via the
subgraph inclusion. -/
noncomputable def componentInclusionIso (hΓ : Γ.Preconnected) : (Γ.component v₀).Iso Γ :=
  (Γ.componentInclusion v₀).toIso (Γ.componentInclusion_mapV_bijective v₀ hΓ)
    (Γ.componentInclusion_mapE_bijective v₀ hΓ)

@[simp] theorem componentInclusionIso_equivV_apply (hΓ : Γ.Preconnected)
    (a : (Γ.component v₀).V) : (Γ.componentInclusionIso v₀ hΓ).equivV a = a.1 :=
  Hom.toIso_equivV_apply ..

@[simp] theorem componentInclusionIso_equivE_apply (hΓ : Γ.Preconnected)
    (e : (Γ.component v₀).E) : (Γ.componentInclusionIso v₀ hΓ).equivE e = e.1 :=
  Hom.toIso_equivE_apply ..

end Preconnected

section IsEmpty

variable [IsEmpty Γ.E]

/-- Over a graph without edges, the connected component of `v₀` has no darts. -/
instance : IsEmpty (Γ.component v₀).E :=
  ⟨fun e => isEmptyElim e.1⟩

/-- Over a graph without edges, the connected component of `v₀` has `v₀` as its unique vertex. -/
instance : Unique (Γ.component v₀).V where
  default := Γ.componentBase v₀
  uniq a := Subtype.ext <|
    (Γ.eq_of_path_of_forall_src_eq_tgt isEmptyElim
      ((Γ.mem_componentVertices_iff v₀ a.1).1 a.2).some).symm

end IsEmpty

end TauCeti.SerreGraph
