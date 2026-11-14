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

The connected component of a vertex `v` in a Serre graph `Γ` is the subgraph `Γ.component v`
(`SerreGraph.subgraph`) spanned by the vertices reachable from `v` by a path and the darts issuing
from them. Because paths can be extended by a dart and reversed, the dart set is closed under
reversal, every path starting at `v` lifts to `Γ.component v`, and `Γ.component v` is connected.

When `Γ` is preconnected, every vertex and dart lies in `Γ.component v`, so the subgraph inclusion
is an isomorphism (`SerreGraph.componentIsoOfPreconnected`). Over a graph without darts, no path
leaves `v`, so `Γ.component v` has `v` as its unique vertex even when `Γ` has other isolated
vertices.

## Main declarations

* `TauCeti.SerreGraph.component`: the connected component of a vertex `v` as a `SerreGraph`.
* `TauCeti.SerreGraph.componentBase`, `TauCeti.SerreGraph.componentInclusion`: the base vertex and
  the inclusion into the ambient graph.
* `TauCeti.SerreGraph.component_connected`: the connected component of a vertex is connected.
* `TauCeti.SerreGraph.componentIsoOfPreconnected`: when `Γ` is preconnected, `Γ.component v` is
  isomorphic to `Γ` via the subgraph inclusion.

## References

* J.-P. Serre, *Trees*, Chapter I, §2.1.
-/

public section

universe u v

namespace TauCeti
namespace SerreGraph

variable (Γ : SerreGraph.{u, v}) (v : Γ.V)

/-- The vertices of `Γ` reachable from `v` by a path. -/
def componentVertices : Set Γ.V :=
  {a | Nonempty (Γ.Path v a)}

@[simp] theorem mem_componentVertices_iff {a : Γ.V} :
    a ∈ Γ.componentVertices v ↔ Nonempty (Γ.Path v a) :=
  Iff.rfl

/-- The base vertex belongs to its own connected component. -/
theorem self_mem_componentVertices : v ∈ Γ.componentVertices v :=
  ⟨.nil⟩

/-- The darts of `Γ` whose source lies in the connected component of `v`. -/
def componentDarts : Set Γ.E :=
  {e | Γ.src e ∈ Γ.componentVertices v}

@[simp] theorem mem_componentDarts_iff {e : Γ.E} :
    e ∈ Γ.componentDarts v ↔ Nonempty (Γ.Path v (Γ.src e)) :=
  Iff.rfl

/-- The darts of a connected component are closed under reversal: appending `e` to a path from `v`
to `src e` reaches `tgt e = src (rev e)`. -/
theorem rev_mem_componentDarts {e : Γ.E} (he : e ∈ Γ.componentDarts v) :
    Γ.rev e ∈ Γ.componentDarts v := by
  obtain ⟨p⟩ := he
  exact ⟨p.cons (Γ.dart e)⟩

theorem rev_mem_componentDarts_iff {e : Γ.E} :
    Γ.rev e ∈ Γ.componentDarts v ↔ e ∈ Γ.componentDarts v :=
  ⟨fun h => Γ.rev_rev e ▸ Γ.rev_mem_componentDarts v h, Γ.rev_mem_componentDarts v⟩

/-- Both endpoints of a dart in the connected component of `v` lie in that component. -/
theorem src_mem_componentVertices {e : Γ.E} (he : e ∈ Γ.componentDarts v) :
    Γ.src e ∈ Γ.componentVertices v :=
  he

theorem tgt_mem_componentVertices {e : Γ.E} (he : e ∈ Γ.componentDarts v) :
    Γ.tgt e ∈ Γ.componentVertices v :=
  Γ.rev_mem_componentDarts v he

/-- The connected component of a vertex `v` in `Γ`: the subgraph on the vertices reachable from
`v` and the darts issuing from them. -/
abbrev component : SerreGraph.{u, v} :=
  Γ.subgraph (Γ.componentVertices v) (Γ.componentDarts v) (fun _ => Γ.src_mem_componentVertices v)
    fun _ => Γ.rev_mem_componentDarts v

/-- The base vertex `v` as a vertex of `Γ.component v`. -/
@[expose] def componentBase : (Γ.component v).V :=
  ⟨v, Γ.self_mem_componentVertices v⟩

@[simp] theorem componentBase_val : (Γ.componentBase v).1 = v := (rfl)

/-- Inclusion of `Γ.component v` into `Γ`. -/
abbrev componentInclusion : (Γ.component v).Hom Γ :=
  Γ.subgraphInclusion _ _ _ _

instance : Inhabited (Γ.component v).V :=
  ⟨Γ.componentBase v⟩

instance [IsEmpty Γ.E] : IsEmpty (Γ.component v).E :=
  ⟨fun e => isEmptyElim e.1⟩

/-- In a graph without darts, the connected component of `v` has `v` as its unique vertex. -/
instance [IsEmpty Γ.E] : Unique (Γ.component v).V where
  default := Γ.componentBase v
  uniq a := Subtype.ext
    (Γ.eq_of_path_of_forall_src_eq_tgt isEmptyElim
      ((Γ.mem_componentVertices_iff v).mp a.2).some).symm

/-- Every path in `Γ` starting at `v` lifts to `Γ.component v`. -/
theorem exists_component_path {a : Γ.V} (p : Γ.Path v a) :
    ∃ q : (Γ.component v).Path (Γ.componentBase v) ⟨a, (Γ.mem_componentVertices_iff v).mpr ⟨p⟩⟩,
      (Γ.componentInclusion v).toPrefunctor.mapPath q = p :=
  Γ.exists_subgraph_path _ _ _ _ p
    (fun _ he => by
      obtain ⟨q, _, _⟩ := Path.exists_eq_cons_comp_of_mem_darts Γ p he
      exact (Γ.mem_componentDarts_iff v).mpr ⟨q⟩)
    (Γ.self_mem_componentVertices v) ((Γ.mem_componentVertices_iff v).mpr ⟨p⟩)

/-- Every vertex of `Γ.component v` is reachable from `componentBase` within `Γ.component v`. -/
theorem component_reachable (a : (Γ.component v).V) :
    Nonempty ((Γ.component v).Path (Γ.componentBase v) a) := by
  rcases a with ⟨a, ha⟩
  obtain ⟨p⟩ := (Γ.mem_componentVertices_iff v).mp ha
  exact ⟨(Γ.exists_component_path v p).choose⟩

/-- The connected component of any vertex is connected. -/
theorem component_connected : (Γ.component v).Connected :=
  (Γ.component v).connected_iff.mpr
    ⟨⟨Γ.componentBase v⟩,
      (Γ.component v).preconnected_of_forall_nonempty_path (Γ.componentBase v)
        (Γ.component_reachable v)⟩

/-- When `Γ` is preconnected, the connected component of `v` is isomorphic to `Γ` via the subgraph
inclusion. -/
@[expose] def componentIsoOfPreconnected (hΓ : Γ.Preconnected) : (Γ.component v).Iso Γ where
  equivV :=
    { toFun := Subtype.val
      invFun := fun a => ⟨a, (Γ.mem_componentVertices_iff v).mpr (Γ.preconnected_iff.mp hΓ v a)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  equivE :=
    { toFun := Subtype.val
      invFun := fun e =>
        ⟨e, (Γ.mem_componentDarts_iff v).mpr (Γ.preconnected_iff.mp hΓ v (Γ.src e))⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  map_src _ := rfl
  map_rev _ := rfl

@[simp] theorem componentIsoOfPreconnected_toHom (hΓ : Γ.Preconnected) :
    (Γ.componentIsoOfPreconnected v hΓ).toHom = Γ.componentInclusion v := (rfl)

@[simp] theorem componentIsoOfPreconnected_equivV_apply (hΓ : Γ.Preconnected)
    (a : (Γ.component v).V) : (Γ.componentIsoOfPreconnected v hΓ).equivV a = a.1 := (rfl)

@[simp] theorem componentIsoOfPreconnected_equivE_apply (hΓ : Γ.Preconnected)
    (e : (Γ.component v).E) : (Γ.componentIsoOfPreconnected v hΓ).equivE e = e.1 := (rfl)

end SerreGraph
end TauCeti
