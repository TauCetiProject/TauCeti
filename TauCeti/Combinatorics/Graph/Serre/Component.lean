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

The connected component `Γ.component v` of a vertex `v` in a Serre graph `Γ` is the subgraph
consisting of the vertices reachable from `v` by a path of `Γ` and the darts whose source is
reachable from `v`. Because extending a path from `v` to `src e` by `e` reaches `tgt e`, a dart
has reachable source if and only if its reverse does, so `componentDarts` is closed under reversal
and contains every dart with an endpoint in `componentVertices`.

Every path of `Γ` starting in the component of `v` stays in it and lifts through the inclusion
`Γ.componentInclusion v`, so `Γ.component v` is always connected. When `Γ` is preconnected every
vertex and dart belongs to the component of `v`, and `Γ.componentIsoOfPreconnected` identifies
`Γ.component v` with `Γ`.

In Bass–Serre theory, the quotient of the Bass–Serre tree `X(𝔸, v₀)` of a graph of groups `𝔸` by
`π₁(𝔸, v₀)` is isomorphic to `Γ.component v₀`, and hence to `Γ` itself when `Γ` is preconnected.

## Main definitions

* `TauCeti.SerreGraph.componentVertices`, `TauCeti.SerreGraph.componentDarts`: the vertices and
  darts of `Γ` reachable from `v`.
* `TauCeti.SerreGraph.component`: the connected component of `v` as a `SerreGraph`.
* `TauCeti.SerreGraph.componentBase`: `v` as a vertex of `Γ.component v`.
* `TauCeti.SerreGraph.componentInclusion`: the inclusion morphism `(Γ.component v).Hom Γ`.
* `TauCeti.SerreGraph.componentIsoOfPreconnected`: the isomorphism `(Γ.component v).Iso Γ` when
  `Γ` is preconnected.

## Main results

* `TauCeti.SerreGraph.exists_component_path`: every path of `Γ` starting in the component of `v`
  lifts to `Γ.component v`.
* `TauCeti.SerreGraph.component_connected`: `Γ.component v` is connected.

## References

* J.-P. Serre, *Trees*, Chapter I, §2.1–§2.2.
-/

public section

universe u v

namespace TauCeti.SerreGraph

variable (Γ : SerreGraph.{u, v}) (v : Γ.V)

/-- The vertices of `Γ` reachable from `v` by an edge path. -/
def componentVertices : Set Γ.V :=
  {a | Nonempty (Γ.Path v a)}

theorem mem_componentVertices_iff (a : Γ.V) :
    a ∈ Γ.componentVertices v ↔ Nonempty (Γ.Path v a) :=
  Iff.rfl

/-- The base vertex `v` belongs to its own connected component. -/
@[simp] theorem self_mem_componentVertices : v ∈ Γ.componentVertices v :=
  ⟨.nil⟩

/-- If the source of a dart lies in the component of `v`, so does its target. -/
theorem tgt_mem_componentVertices_of_src_mem {e : Γ.E} (he : Γ.src e ∈ Γ.componentVertices v) :
    Γ.tgt e ∈ Γ.componentVertices v :=
  he.map (·.cons (Γ.dart e))

/-- The target of a dart lies in the component of `v` if and only if its source does. -/
theorem tgt_mem_componentVertices_iff (e : Γ.E) :
    Γ.tgt e ∈ Γ.componentVertices v ↔ Γ.src e ∈ Γ.componentVertices v :=
  ⟨fun h => by
    have hrev : Γ.src (Γ.rev e) ∈ Γ.componentVertices v := by rwa [Γ.src_rev]
    simpa only [Γ.tgt_rev] using Γ.tgt_mem_componentVertices_of_src_mem v hrev,
    Γ.tgt_mem_componentVertices_of_src_mem v⟩

/-- Reachability from a vertex in the component of `v` implies membership in the component. -/
theorem mem_componentVertices_of_path {a b : Γ.V} (ha : a ∈ Γ.componentVertices v)
    (p : Γ.Path a b) : b ∈ Γ.componentVertices v :=
  ha.map (·.comp p)

/-- The darts of `Γ` whose source lies in the connected component of `v`. -/
def componentDarts : Set Γ.E :=
  {e | Γ.src e ∈ Γ.componentVertices v}

theorem mem_componentDarts_iff (e : Γ.E) :
    e ∈ Γ.componentDarts v ↔ Nonempty (Γ.Path v (Γ.src e)) :=
  Iff.rfl

/-- The dart set of a connected component is closed under reversal. -/
@[simp] theorem rev_mem_componentDarts_iff (e : Γ.E) :
    Γ.rev e ∈ Γ.componentDarts v ↔ e ∈ Γ.componentDarts v :=
  (Γ.tgt_mem_componentVertices_iff v e).trans Iff.rfl

/-- Both endpoints of a dart in the component lie in the component. -/
theorem src_mem_componentVertices {e : Γ.E} (he : e ∈ Γ.componentDarts v) :
    Γ.src e ∈ Γ.componentVertices v :=
  he

/-- Both endpoints of a dart in the component lie in the component. -/
theorem tgt_mem_componentVertices {e : Γ.E} (he : e ∈ Γ.componentDarts v) :
    Γ.tgt e ∈ Γ.componentVertices v :=
  Γ.tgt_mem_componentVertices_of_src_mem v he

/-- The connected component of `v` in `Γ`, as a Serre graph. -/
@[expose] def component : SerreGraph.{u, v} where
  V := Γ.componentVertices v
  E := Γ.componentDarts v
  src e := ⟨Γ.src e.1, Γ.src_mem_componentVertices v e.2⟩
  rev e := ⟨Γ.rev e.1, (Γ.rev_mem_componentDarts_iff v e.1).mpr e.2⟩
  rev_rev e := Subtype.ext (Γ.rev_rev e.1)
  rev_ne e he := Γ.rev_ne e.1 (congrArg Subtype.val he)

/-- The base vertex `v` as a vertex of `Γ.component v`. -/
@[expose] def componentBase : (Γ.component v).V :=
  ⟨v, Γ.self_mem_componentVertices v⟩

/-- The inclusion morphism from `Γ.component v` into `Γ`. -/
@[expose] def componentInclusion : (Γ.component v).Hom Γ where
  mapV := Subtype.val
  mapE := Subtype.val
  map_src _ := rfl
  map_rev _ := rfl

@[simp] theorem componentInclusion_mapV (a : (Γ.component v).V) :
    (Γ.componentInclusion v).mapV a = a.1 := (rfl)

@[simp] theorem componentInclusion_mapE (e : (Γ.component v).E) :
    (Γ.componentInclusion v).mapE e = e.1 := (rfl)

@[simp] theorem componentBase_val : (Γ.componentBase v).1 = v := (rfl)

@[simp] theorem component_src_val (e : (Γ.component v).E) :
    ((Γ.component v).src e).1 = Γ.src e.1 := (rfl)

@[simp] theorem component_rev_val (e : (Γ.component v).E) :
    ((Γ.component v).rev e).1 = Γ.rev e.1 := (rfl)

@[simp] theorem component_tgt_val (e : (Γ.component v).E) :
    ((Γ.component v).tgt e).1 = Γ.tgt e.1 := (rfl)

theorem componentInclusion_mapV_injective : Function.Injective (Γ.componentInclusion v).mapV :=
  Subtype.val_injective

theorem componentInclusion_mapE_injective : Function.Injective (Γ.componentInclusion v).mapE :=
  Subtype.val_injective

instance [Finite Γ.V] : Finite (Γ.component v).V :=
  inferInstanceAs (Finite (Γ.componentVertices v))

instance [Finite Γ.E] : Finite (Γ.component v).E :=
  inferInstanceAs (Finite (Γ.componentDarts v))

instance : Nonempty (Γ.component v).V :=
  ⟨Γ.componentBase v⟩

instance [IsEmpty Γ.E] : IsEmpty (Γ.component v).E :=
  ⟨fun e => isEmptyElim e.1⟩

/-- Over an edgeless graph, the connected component of `v` consists solely of `v`. -/
instance [IsEmpty Γ.E] : Unique (Γ.component v).V where
  default := Γ.componentBase v
  uniq a := by
    obtain ⟨a, ha⟩ := a
    obtain ⟨p⟩ := (Γ.mem_componentVertices_iff v a).mp ha
    refine Subtype.ext (p.eq_of_length_zero ?_).symm
    cases p with
    | nil => rfl
    | cons _ e => exact isEmptyElim e.1

/-- Every path in `Γ` starting at a vertex in the component of `v` lifts to `Γ.component v`. -/
theorem exists_component_path {a b : Γ.V} (p : Γ.Path a b) (ha : a ∈ Γ.componentVertices v) :
    ∃ q : (Γ.component v).Path ⟨a, ha⟩ ⟨b, Γ.mem_componentVertices_of_path v ha p⟩,
      (Γ.componentInclusion v).toPrefunctor.mapPath q = p := by
  induction p with
  | nil => exact ⟨.nil, rfl⟩
  | @cons b c p e ih =>
    have hb : b ∈ Γ.componentVertices v := Γ.mem_componentVertices_of_path v ha p
    have he : e.1 ∈ Γ.componentDarts v :=
      (Γ.mem_componentDarts_iff v e.1).mpr (e.2.1.symm ▸ (Γ.mem_componentVertices_iff v b).mp hb)
    obtain ⟨q, hq⟩ := ih
    let f : @Quiver.Hom (Γ.component v).V (Γ.component v).toQuiver
        ⟨b, hb⟩ ⟨c, Γ.mem_componentVertices_of_path v ha (p.cons e)⟩ :=
      ⟨⟨e.1, he⟩, Subtype.ext e.2.1, Subtype.ext e.2.2⟩
    exact ⟨q.cons f, congrArg (·.cons e) hq⟩

/-- Every vertex of `Γ.component v` is reachable from `Γ.componentBase v` within `Γ.component v`. -/
theorem component_reachable (a : (Γ.component v).V) :
    Nonempty ((Γ.component v).Path (Γ.componentBase v) a) := by
  obtain ⟨a, ha⟩ := a
  obtain ⟨p⟩ := (Γ.mem_componentVertices_iff v a).mp ha
  obtain ⟨q, -⟩ := Γ.exists_component_path v p (Γ.self_mem_componentVertices v)
  exact ⟨q⟩

/-- The connected component of any vertex is preconnected. -/
theorem component_preconnected : (Γ.component v).Preconnected :=
  (Γ.component v).preconnected_of_forall_nonempty_path (Γ.componentBase v) (Γ.component_reachable v)

/-- The connected component of any vertex is connected. -/
theorem component_connected : (Γ.component v).Connected :=
  ((Γ.component v).connected_iff).mpr ⟨⟨Γ.componentBase v⟩, Γ.component_preconnected v⟩

variable {v} in
/-- When `Γ` is preconnected, the inclusion of `Γ.component v` is an isomorphism onto `Γ`. -/
@[expose] def componentIsoOfPreconnected (hΓ : Γ.Preconnected) : (Γ.component v).Iso Γ where
  equivV := Equiv.subtypeUnivEquiv fun a =>
    (Γ.mem_componentVertices_iff v a).mpr (Γ.preconnected_iff.mp hΓ v a)
  equivE := Equiv.subtypeUnivEquiv fun e =>
    (Γ.mem_componentDarts_iff v e).mpr (Γ.preconnected_iff.mp hΓ v (Γ.src e))
  map_src _ := rfl
  map_rev _ := rfl

@[simp] theorem componentIsoOfPreconnected_equivV_apply {v : Γ.V} (hΓ : Γ.Preconnected)
    (a : (Γ.component v).V) : (Γ.componentIsoOfPreconnected hΓ).equivV a = a.1 := (rfl)

@[simp] theorem componentIsoOfPreconnected_equivE_apply {v : Γ.V} (hΓ : Γ.Preconnected)
    (e : (Γ.component v).E) : (Γ.componentIsoOfPreconnected hΓ).equivE e = e.1 := (rfl)

@[simp] theorem componentIsoOfPreconnected_toHom {v : Γ.V} (hΓ : Γ.Preconnected) :
    (Γ.componentIsoOfPreconnected hΓ).toHom = Γ.componentInclusion v := (rfl)

end TauCeti.SerreGraph
