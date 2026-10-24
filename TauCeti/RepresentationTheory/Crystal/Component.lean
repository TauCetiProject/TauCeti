/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import TauCeti.RepresentationTheory.Crystal.Basic

/-!
# Connected components of a normal crystal

For a normal crystal `c` over a root datum with a base, two elements are **adjacent** when one is
obtained from the other by a raising or a lowering operator; the adjacency relation is the
(crystal) graph of `c`, and its connected components are the **components** of `c`. Each component
carries the restriction of the weight and of the root operators, which stay inside the component,
and `TauCeti.NormalCrystal.componentCrystal` shows that this restriction is again a normal crystal;
the inclusion of a component is a strict morphism.

The adjacency relation is the unlabelled adjacency of the crystal graph: the simple root is
existentially quantified and forgotten. The graph itself is `TauCeti.NormalCrystal.crystalGraph`,
whose `SimpleGraph.reachableSetoid` is the component setoid, and
`TauCeti.NormalCrystal.componentSetoid_apply` identifies it with the reachability relation
`Relation.ReflTransGen c.Adj`
(`SimpleGraph.reachable_fromEdgeSet_fromRel_eq_reflTransGen`). The neighbouring API is
`SimpleGraph.Reachable`, `SimpleGraph.reachableSetoid` and `SimpleGraph.ConnectedComponent`, with
`SimpleGraph.ConnectedComponent.supp` the vertex set of a component: the component of `x` is the
supp of the connected component of `x` in the crystal graph.

A component is closed under the root operators, so it is the restriction of `c` to a subset closed
under them. Restriction itself is `TauCeti.NormalCrystal.restrict`, constructed in
`TauCeti.RepresentationTheory.Crystal.Basic` together with the strict morphism
`TauCeti.NormalCrystal.StrictHom.restrictIncl` that includes a closed subset into the ambient
crystal; this file applies it to components, which gives the crystal structure on a component and
the strict morphism of its inclusion.

Transport of a normal crystal along a bijection is constructed in
`TauCeti.RepresentationTheory.Crystal.Basic`. The results here relate that transport to the
components: it is an isomorphism of crystal graphs
(`TauCeti.NormalCrystal.crystalGraphCongr`), it conjugates the component equivalence relations
(`TauCeti.NormalCrystal.componentSetoid_congr`) and it carries the component of `x` to the
component of its image (`TauCeti.NormalCrystal.component_congr`).

## Main definitions

* `TauCeti.NormalCrystal.Adj`: adjacency in the crystal graph.
* `TauCeti.NormalCrystal.crystalGraph`: the simple graph whose reachability relation is the
  component equivalence relation.
* `TauCeti.NormalCrystal.componentSetoid`, `TauCeti.NormalCrystal.component`: connected
  components, as an equivalence relation and as the vertex set of a component.
* `TauCeti.NormalCrystal.componentCrystal`: the normal crystal structure on a component, obtained
  by restricting `c` to the component.
* `TauCeti.NormalCrystal.StrictHom.componentIncl`: the inclusion of a component is a strict
  morphism.
* `TauCeti.NormalCrystal.crystalGraphCongr`: transport along a bijection, as an isomorphism of
  crystal graphs.

## Main results

* `TauCeti.NormalCrystal.adj_comm`: the crystal graph is undirected.
* `TauCeti.NormalCrystal.crystalGraph_adj`: the edges of the crystal graph are the adjacency
  relation on distinct vertices.
* `TauCeti.NormalCrystal.componentSetoid_iff_reachable`,
  `TauCeti.NormalCrystal.componentSetoid_apply`: the component equivalence relation is graph
  reachability, equivalently reachability in the adjacency relation.
* `TauCeti.NormalCrystal.mem_component_iff`, `TauCeti.NormalCrystal.mem_component_self`:
  membership in a component, and `TauCeti.NormalCrystal.component_eq_iff` its characteristic
  equality criterion: two elements have the same component exactly when they are related by the
  component equivalence relation.
* `TauCeti.NormalCrystal.component_eq_of_adj`,
  `TauCeti.NormalCrystal.component_eq_of_e_eq_some`,
  `TauCeti.NormalCrystal.component_eq_of_f_eq_some`: adjacent elements, in particular the root
  operators, stay inside a component.
* `TauCeti.NormalCrystal.congr_adj`,
  `TauCeti.NormalCrystal.componentSetoid_congr`,
  `TauCeti.NormalCrystal.mem_component_congr_iff`,
  `TauCeti.NormalCrystal.component_congr`: transport along a bijection carries components to
  components.

## References

* M. Kashiwara, *On crystal bases*, CMS Conf. Proc. 16 (1995), §7.
* D. Bump and A. Schilling, *Crystal bases: representations and combinatorics*, World Scientific
  (2017), Ch. 2.
-/

public section

namespace TauCeti

universe u v w x₁ x₂

variable {ι : Type u} {X : Type v} {Y : Type w} [AddCommGroup X] [AddCommGroup Y]
  {P : RootDatum ι X Y} {b : P.Base}

namespace NormalCrystal

variable {B : Type x₁} {B' : Type x₂}

/-! ### Connected components -/

section Component

variable (c : NormalCrystal P b B)

/-- Elements of a normal crystal are **adjacent** when one is obtained from the other by a
raising or a lowering operator, that is, when they are joined by an arrow of the crystal graph. -/
def Adj (x y : B) : Prop :=
  ∃ i : b.support, c.e i x = some y ∨ c.f i x = some y

/-- The defining characterization of adjacency: `x` and `y` are adjacent when a raising or a
lowering operator sends one to the other. -/
theorem adj_iff {x y : B} :
    c.Adj x y ↔ ∃ i : b.support, c.e i x = some y ∨ c.f i x = some y :=
  (Iff.rfl)

/-- Adjacency in the crystal graph is symmetric. -/
theorem adj_comm {x y : B} : c.Adj x y ↔ c.Adj y x := by
  rw [adj_iff, adj_iff]
  constructor <;> rintro ⟨i, h | h⟩
  · exact ⟨i, Or.inr (c.f_eq_some_iff.2 h)⟩
  · exact ⟨i, Or.inl (c.e_eq_some_iff.2 h)⟩
  · exact ⟨i, Or.inr (c.f_eq_some_iff.2 h)⟩
  · exact ⟨i, Or.inl (c.e_eq_some_iff.2 h)⟩

instance instSymmAdj : Std.Symm c.Adj :=
  ⟨fun _ _ h => c.adj_comm.1 h⟩

/-- The simple graph underlying the component decomposition: `x` and `y` are adjacent when a
raising or lowering operator sends one to the other. The simple root is forgotten. -/
def crystalGraph : SimpleGraph B :=
  SimpleGraph.fromEdgeSet (Sym2.fromRel c.instSymmAdj)

/-- Adjacency in the crystal graph is adjacency in the crystal with distinct vertices. -/
@[simp]
theorem crystalGraph_adj {x y : B} :
    c.crystalGraph.Adj x y ↔ x ≠ y ∧ c.Adj x y := by
  rw [crystalGraph, SimpleGraph.fromEdgeSet_adj, Sym2.fromRel_prop]
  exact and_comm

/-- The equivalence relation of lying in the same connected component of the crystal graph: the
`SimpleGraph.reachableSetoid` of the crystal graph. -/
def componentSetoid : Setoid B :=
  c.crystalGraph.reachableSetoid

/-- The component equivalence relation is reachability in the crystal graph. -/
theorem componentSetoid_iff_reachable {x y : B} :
    c.componentSetoid x y ↔ c.crystalGraph.Reachable x y :=
  Iff.rfl

/-- The component equivalence relation is the reachability relation of the crystal graph. -/
@[simp]
theorem componentSetoid_apply {x y : B} :
    c.componentSetoid x y ↔ Relation.ReflTransGen c.Adj x y := by
  rw [componentSetoid_iff_reachable, crystalGraph,
    SimpleGraph.reachable_fromEdgeSet_fromRel_eq_reflTransGen]

/-- The connected **component** of `x`: the vertex set of the connected component of `x` in the
crystal graph, that is, the set of elements joined to `x` by a chain of arrows. -/
def component (x : B) : Set B :=
  (c.crystalGraph.connectedComponentMk x).supp

/-- An element lies in the component of `x` exactly when it is reachable from `x` in the crystal
graph. -/
@[simp]
theorem mem_component_iff {x y : B} :
    y ∈ c.component x ↔ Relation.ReflTransGen c.Adj x y := by
  rw [component, SimpleGraph.ConnectedComponent.mem_supp_iff, SimpleGraph.ConnectedComponent.eq,
    SimpleGraph.reachable_comm, ← componentSetoid_iff_reachable, componentSetoid_apply]

/-- Every element lies in its own component. -/
theorem mem_component_self (x : B) : x ∈ c.component x := by
  rw [mem_component_iff]

/-- Two elements have the same component exactly when they are related by the component
equivalence relation, that is, when they are joined by a chain of arrows. -/
theorem component_eq_iff {x y : B} : c.component x = c.component y ↔ c.componentSetoid x y := by
  rw [component, component, SimpleGraph.ConnectedComponent.supp_inj,
    SimpleGraph.ConnectedComponent.eq, componentSetoid_iff_reachable]

/-- Adjacent elements lie in the same component. -/
theorem component_eq_of_adj {x y : B} (h : c.Adj x y) : c.component x = c.component y := by
  rw [component_eq_iff, componentSetoid_apply]
  exact Relation.ReflTransGen.single h

/-- A component is closed under adjacency in the crystal graph. -/
theorem mem_component_of_adj {x y z : B} (hx : y ∈ c.component x) (h : c.Adj y z) :
    z ∈ c.component x := by
  rcases eq_or_ne y z with rfl | hne
  · exact hx
  · exact SimpleGraph.ConnectedComponent.mem_supp_of_adj_mem_supp _
      hx ((c.crystalGraph_adj).2 ⟨hne, h⟩)

/-- A component is closed under the raising operators. -/
theorem mem_component_of_e_eq_some {i : b.support} {x y z : B} (hx : y ∈ c.component x)
    (h : c.e i y = some z) : z ∈ c.component x :=
  c.mem_component_of_adj hx ⟨i, Or.inl h⟩

/-- A component is closed under the lowering operators. -/
theorem mem_component_of_f_eq_some {i : b.support} {x y z : B} (hx : y ∈ c.component x)
    (h : c.f i y = some z) : z ∈ c.component x :=
  c.mem_component_of_adj hx ⟨i, Or.inr h⟩

/-- Raising preserves the component. -/
theorem component_eq_of_e_eq_some {i : b.support} {x y : B} (h : c.e i x = some y) :
    c.component x = c.component y :=
  c.component_eq_of_adj ⟨i, Or.inl h⟩

/-- Lowering preserves the component. -/
theorem component_eq_of_f_eq_some {i : b.support} {x y : B} (h : c.f i x = some y) :
    c.component x = c.component y :=
  c.component_eq_of_adj ⟨i, Or.inr h⟩

end Component

/-! ### The crystal structure on a component -/

section ComponentCrystal

variable (c : NormalCrystal P b B) (x : B)

/-- The **component crystal**: the restriction of `c` to the connected component of `x`. The
weight and the string lengths are inherited, and the root operators are those of `c`, which stay
inside the component. -/
def componentCrystal : NormalCrystal P b (c.component x) :=
  c.restrict (c.component x)
    (fun _ _ hy _ hz => c.mem_component_of_e_eq_some hy hz)
    (fun _ _ hy _ hz => c.mem_component_of_f_eq_some hy hz)

@[simp]
theorem componentCrystal_wt (y : c.component x) :
    (c.componentCrystal x).wt y = c.wt y.1 := by
  simp only [componentCrystal, restrict_wt]

@[simp]
theorem componentCrystal_ε (i : b.support) (y : c.component x) :
    (c.componentCrystal x).ε i y = c.ε i y.1 := by
  simp only [componentCrystal, restrict_ε]

@[simp]
theorem componentCrystal_φ (i : b.support) (y : c.component x) :
    (c.componentCrystal x).φ i y = c.φ i y.1 := by
  simp only [componentCrystal, restrict_φ]

@[simp]
theorem componentCrystal_e_eq_some_iff {i : b.support} {y z : c.component x} :
    (c.componentCrystal x).e i y = some z ↔ c.e i y.1 = some z.1 := by
  simp only [componentCrystal, restrict_e_eq_some_iff]

@[simp]
theorem componentCrystal_f_eq_some_iff {i : b.support} {y z : c.component x} :
    (c.componentCrystal x).f i y = some z ↔ c.f i y.1 = some z.1 := by
  simp only [componentCrystal, restrict_f_eq_some_iff]

@[simp]
theorem componentCrystal_e_eq_none_iff {i : b.support} {y : c.component x} :
    (c.componentCrystal x).e i y = none ↔ c.e i y.1 = none := by
  simp only [componentCrystal, restrict_e_eq_none_iff]

@[simp]
theorem componentCrystal_f_eq_none_iff {i : b.support} {y : c.component x} :
    (c.componentCrystal x).f i y = none ↔ c.f i y.1 = none := by
  simp only [componentCrystal, restrict_f_eq_none_iff]

/-- The crystal graph of a component is the restriction of the crystal graph of the ambient
crystal. -/
@[simp]
theorem componentCrystal_adj {y z : c.component x} :
    (c.componentCrystal x).Adj y z ↔ c.Adj y.1 z.1 := by
  simp [Adj, componentCrystal_e_eq_some_iff, componentCrystal_f_eq_some_iff]

/-- The inclusion of a component into the ambient crystal is a strict morphism. -/
def StrictHom.componentIncl : StrictHom (c.componentCrystal x) c :=
  StrictHom.restrictIncl c (c.component x)
    (fun _ _ hy _ hz => c.mem_component_of_e_eq_some hy hz)
    (fun _ _ hy _ hz => c.mem_component_of_f_eq_some hy hz)

@[simp]
theorem StrictHom.componentIncl_apply (y : c.component x) :
    StrictHom.componentIncl c x y = y.1 :=
  StrictHom.restrictIncl_apply c (c.component x) _ _ y

end ComponentCrystal

/-! ### Components and transport -/

section Bridge

variable (c : NormalCrystal P b B) (e : B ≃ B')

/-- Transport along a bijection relates the crystal graphs through the bijection. -/
@[simp]
theorem congr_adj (x y : B') :
    (c.congr e).Adj x y ↔ c.Adj (e.symm x) (e.symm y) := by
  simp only [Adj, congr_e_eq_some_iff, congr_f_eq_some_iff]

/-- Transport along a bijection is an isomorphism of the crystal graphs. -/
def crystalGraphCongr : c.crystalGraph ≃g (c.congr e).crystalGraph where
  toEquiv := e
  map_rel_iff' := by
    intro x y
    simp [crystalGraph_adj, congr_adj]

/-- The graph isomorphism underlying the transport sends a vertex to its image. -/
@[simp]
theorem crystalGraphCongr_apply (x : B) : c.crystalGraphCongr e x = e x := (rfl)

/-- The inverse of the graph isomorphism underlying the transport sends a vertex to its
preimage. -/
@[simp]
theorem crystalGraphCongr_symm_apply (y : B') : (c.crystalGraphCongr e).symm y = e.symm y := (rfl)

/-- Transport along a bijection conjugates the component equivalence relations. -/
theorem componentSetoid_congr :
    (c.congr e).componentSetoid = c.componentSetoid.comap ⇑e.symm := by
  refine Setoid.ext fun x y => ?_
  rw [componentSetoid_iff_reachable, Setoid.comap_rel, componentSetoid_iff_reachable]
  simpa only [crystalGraphCongr_symm_apply] using
    (SimpleGraph.Iso.reachable_iff (φ := (c.crystalGraphCongr e).symm) (u := x) (v := y)).symm

/-- Transport along a bijection carries the component of `x` to the component of `e x`. -/
-- Not `@[simp]`: the membership lemma `mem_component_iff` rewrites the left-hand side, which
-- `simpNF` rejects.
theorem mem_component_congr_iff {x : B} {y : B'} :
    y ∈ (c.congr e).component (e x) ↔ e.symm y ∈ c.component x := by
  rw [mem_component_iff, mem_component_iff, ← componentSetoid_apply, ← componentSetoid_apply,
    componentSetoid_congr, Setoid.comap_rel, Equiv.symm_apply_apply]

/-- Transport along a bijection carries the component of `x` to the image of the component of
`x`. -/
theorem component_congr (x : B) :
    (c.congr e).component (e x) = e '' c.component x := by
  ext y
  rw [Set.mem_image, mem_component_congr_iff]
  exact ⟨fun hy => ⟨e.symm y, hy, Equiv.apply_symm_apply e y⟩,
    fun ⟨w, hw, hwe⟩ => by rw [← hwe, Equiv.symm_apply_apply]; exact hw⟩

end Bridge

end NormalCrystal

end TauCeti
