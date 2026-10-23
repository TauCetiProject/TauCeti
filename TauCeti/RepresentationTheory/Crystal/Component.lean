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

Restricting a normal crystal to a subset closed under the root operators is
`TauCeti.NormalCrystal.restrict`. A component is such a subset, which gives the crystal structure
on a component and the strict morphism of its inclusion.

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
* `TauCeti.NormalCrystal.restrict`: the restriction of a normal crystal to a subset closed under
  the root operators.
* `TauCeti.NormalCrystal.componentCrystal`: the normal crystal structure on a component.
* `TauCeti.NormalCrystal.StrictHom.restrictIncl`,
  `TauCeti.NormalCrystal.StrictHom.componentIncl`: the inclusions of a closed subset and of a
  component are strict morphisms.
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
  membership in a component.
* `TauCeti.NormalCrystal.component_eq_of_e_eq_some`,
  `TauCeti.NormalCrystal.component_eq_of_f_eq_some`: the root operators stay inside a component.
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
  Iff.rfl

/-- Adjacency in the crystal graph is symmetric. -/
theorem adj_comm {x y : B} : c.Adj x y ↔ c.Adj y x := by
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
    c.componentSetoid x y ↔ Relation.ReflTransGen c.Adj x y :=
  Iff.of_eq (congrFun (congrFun
    (SimpleGraph.reachable_fromEdgeSet_fromRel_eq_reflTransGen (r := c.Adj)
      (inferInstance : Std.Symm c.Adj)) x) y)

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
    c.component x = c.component y := by
  have hy : y ∈ c.component x := c.mem_component_of_e_eq_some (c.mem_component_self x) h
  rw [component, SimpleGraph.ConnectedComponent.mem_supp_iff] at hy
  simp only [component, ← hy]

/-- Lowering preserves the component. -/
theorem component_eq_of_f_eq_some {i : b.support} {x y : B} (h : c.f i x = some y) :
    c.component x = c.component y := by
  have hy : y ∈ c.component x := c.mem_component_of_f_eq_some (c.mem_component_self x) h
  rw [component, SimpleGraph.ConnectedComponent.mem_supp_iff] at hy
  simp only [component, ← hy]

end Component

/-! ### Restriction to a closed subset -/

section Restrict

variable (c : NormalCrystal P b B)

/-- The **restriction of a normal crystal** to a subset `s` closed under the root operators: the
weight and the string lengths are those of `c`, and the root operators are those of `c`
corestricted to `s`. -/
def restrict (s : Set B)
    (he : ∀ (i : b.support) (y : B), y ∈ s → ∀ z, c.e i y = some z → z ∈ s)
    (hf : ∀ (i : b.support) (y : B), y ∈ s → ∀ z, c.f i y = some z → z ∈ s) :
    NormalCrystal P b s where
  wt y := c.wt y.1
  e i y := (c.e i y.1).pmap Subtype.mk fun z hz => he i y.1 y.2 z hz
  f i y := (c.f i y.1).pmap Subtype.mk fun z hz => hf i y.1 y.2 z hz
  ε i y := c.ε i y.1
  φ i y := c.φ i y.1
  f_eq_some_iff := by
    intro i y z
    rw [Option.pmap_eq_some_iff, Option.pmap_eq_some_iff]
    constructor
    · rintro ⟨a, _ha, hfa, rfl⟩
      exact ⟨y.1, y.2, c.f_eq_some_iff.1 hfa, rfl⟩
    · rintro ⟨a, _ha, hea, rfl⟩
      exact ⟨z.1, z.2, c.f_eq_some_iff.2 hea, rfl⟩
  wt_of_e_eq_some := by
    intro i y z h
    rw [Option.pmap_eq_some_iff] at h
    obtain ⟨a, _ha, ho, rfl⟩ := h
    exact c.wt_of_e_eq_some ho
  ε_eq_zero_iff := by
    intro i y
    rw [Option.pmap_eq_none_iff, c.ε_eq_zero_iff]
  ε_of_e_eq_some := by
    intro i y z h
    rw [Option.pmap_eq_some_iff] at h
    obtain ⟨a, _ha, ho, rfl⟩ := h
    exact c.ε_of_e_eq_some ho
  φ_eq_zero_iff := by
    intro i y
    rw [Option.pmap_eq_none_iff, c.φ_eq_zero_iff]
  φ_sub_ε := fun i y => c.φ_sub_ε i y.1

@[simp]
theorem restrict_wt {s : Set B}
    {he : ∀ (i : b.support) (y : B), y ∈ s → ∀ z, c.e i y = some z → z ∈ s}
    {hf : ∀ (i : b.support) (y : B), y ∈ s → ∀ z, c.f i y = some z → z ∈ s} (y : s) :
    (c.restrict s he hf).wt y = c.wt y.1 := (rfl)

@[simp]
theorem restrict_ε {s : Set B}
    {he : ∀ (i : b.support) (y : B), y ∈ s → ∀ z, c.e i y = some z → z ∈ s}
    {hf : ∀ (i : b.support) (y : B), y ∈ s → ∀ z, c.f i y = some z → z ∈ s}
    (i : b.support) (y : s) :
    (c.restrict s he hf).ε i y = c.ε i y.1 := (rfl)

@[simp]
theorem restrict_φ {s : Set B}
    {he : ∀ (i : b.support) (y : B), y ∈ s → ∀ z, c.e i y = some z → z ∈ s}
    {hf : ∀ (i : b.support) (y : B), y ∈ s → ∀ z, c.f i y = some z → z ∈ s}
    (i : b.support) (y : s) :
    (c.restrict s he hf).φ i y = c.φ i y.1 := (rfl)

@[simp]
theorem restrict_e_eq_some_iff {s : Set B}
    {he : ∀ (i : b.support) (y : B), y ∈ s → ∀ z, c.e i y = some z → z ∈ s}
    {hf : ∀ (i : b.support) (y : B), y ∈ s → ∀ z, c.f i y = some z → z ∈ s}
    {i : b.support} {y z : s} :
    (c.restrict s he hf).e i y = some z ↔ c.e i y.1 = some z.1 := by
  simp only [restrict, Option.pmap_eq_some_iff]
  constructor
  · rintro ⟨a, _ha, ho, rfl⟩
    exact ho
  · intro ho
    exact ⟨z.1, he i y.1 y.2 z.1 ho, ho, Subtype.ext rfl⟩

@[simp]
theorem restrict_f_eq_some_iff {s : Set B}
    {he : ∀ (i : b.support) (y : B), y ∈ s → ∀ z, c.e i y = some z → z ∈ s}
    {hf : ∀ (i : b.support) (y : B), y ∈ s → ∀ z, c.f i y = some z → z ∈ s}
    {i : b.support} {y z : s} :
    (c.restrict s he hf).f i y = some z ↔ c.f i y.1 = some z.1 := by
  simp only [restrict, Option.pmap_eq_some_iff]
  constructor
  · rintro ⟨a, _ha, ho, rfl⟩
    exact ho
  · intro ho
    exact ⟨z.1, hf i y.1 y.2 z.1 ho, ho, Subtype.ext rfl⟩

@[simp]
theorem restrict_e_eq_none_iff {s : Set B}
    {he : ∀ (i : b.support) (y : B), y ∈ s → ∀ z, c.e i y = some z → z ∈ s}
    {hf : ∀ (i : b.support) (y : B), y ∈ s → ∀ z, c.f i y = some z → z ∈ s}
    {i : b.support} {y : s} :
    (c.restrict s he hf).e i y = none ↔ c.e i y.1 = none := by
  simp only [restrict, Option.pmap_eq_none_iff]

@[simp]
theorem restrict_f_eq_none_iff {s : Set B}
    {he : ∀ (i : b.support) (y : B), y ∈ s → ∀ z, c.e i y = some z → z ∈ s}
    {hf : ∀ (i : b.support) (y : B), y ∈ s → ∀ z, c.f i y = some z → z ∈ s}
    {i : b.support} {y : s} :
    (c.restrict s he hf).f i y = none ↔ c.f i y.1 = none := by
  simp only [restrict, Option.pmap_eq_none_iff]

/-- The inclusion of a subset closed under the root operators is a strict morphism. -/
def StrictHom.restrictIncl (s : Set B)
    (he : ∀ (i : b.support) (y : B), y ∈ s → ∀ z, c.e i y = some z → z ∈ s)
    (hf : ∀ (i : b.support) (y : B), y ∈ s → ∀ z, c.f i y = some z → z ∈ s) :
    StrictHom (c.restrict s he hf) c where
  toFun y := y.1
  wt_toFun _ := rfl
  e_toFun i y := by
    cases h : c.e i y.1 with
    | none =>
      have hz : (c.restrict s he hf).e i y = none := c.restrict_e_eq_none_iff.mpr h
      rw [hz, Option.map_none]
    | some z =>
      have hz : (c.restrict s he hf).e i y = some ⟨z, he i y.1 y.2 z h⟩ :=
        c.restrict_e_eq_some_iff.mpr h
      rw [hz, Option.map_some]

@[simp]
theorem StrictHom.restrictIncl_apply (s : Set B)
    (he : ∀ (i : b.support) (y : B), y ∈ s → ∀ z, c.e i y = some z → z ∈ s)
    (hf : ∀ (i : b.support) (y : B), y ∈ s → ∀ z, c.f i y = some z → z ∈ s) (y : s) :
    StrictHom.restrictIncl c s he hf y = y.1 := (rfl)

end Restrict

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
    (c.componentCrystal x).wt y = c.wt y.1 := (rfl)

@[simp]
theorem componentCrystal_ε (i : b.support) (y : c.component x) :
    (c.componentCrystal x).ε i y = c.ε i y.1 := (rfl)

@[simp]
theorem componentCrystal_φ (i : b.support) (y : c.component x) :
    (c.componentCrystal x).φ i y = c.φ i y.1 := (rfl)

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

/-- Transport along a bijection conjugates the component equivalence relations. -/
theorem componentSetoid_congr :
    (c.congr e).componentSetoid = c.componentSetoid.comap ⇑e.symm := by
  refine Setoid.ext fun x y => ?_
  rw [componentSetoid_iff_reachable, Setoid.comap_rel, componentSetoid_iff_reachable]
  have h := SimpleGraph.Iso.reachable_iff (φ := c.crystalGraphCongr e) (u := e.symm x)
    (v := e.symm y)
  simpa [crystalGraphCongr] using h

/-- Transport along a bijection carries the component of `x` to the component of `e x`. -/
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
