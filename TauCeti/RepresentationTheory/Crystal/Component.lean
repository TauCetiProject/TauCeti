/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Logic.Equiv.Option
public import Mathlib.Logic.Relation
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
`SimpleGraph.ConnectedComponent.supp` the vertex set of a component.

Transport of a normal crystal along a bijection is constructed in
`TauCeti.RepresentationTheory.Crystal.Basic`. The results here relate that transport to the
components: it conjugates the component equivalence relations
(`TauCeti.NormalCrystal.componentSetoid_congr`) and carries the component of `x` to the component
of its image (`TauCeti.NormalCrystal.component_congr`).

## Main definitions

* `TauCeti.NormalCrystal.Adj`: adjacency in the crystal graph.
* `TauCeti.NormalCrystal.crystalGraph`: the simple graph whose reachability relation is the
  component equivalence relation.
* `TauCeti.NormalCrystal.componentSetoid`, `TauCeti.NormalCrystal.component`: connected
  components, as an equivalence relation and as a set.
* `TauCeti.NormalCrystal.componentCrystal`: the normal crystal structure on a component.
* `TauCeti.NormalCrystal.StrictHom.componentIncl`: the inclusion of a component.

## Main results

* `TauCeti.NormalCrystal.adj_comm`: the crystal graph is undirected.
* `TauCeti.NormalCrystal.crystalGraph_adj`: the edges of the crystal graph are the adjacency
  relation on distinct vertices.
* `TauCeti.NormalCrystal.mem_component_iff`: membership in a component is reachability in the
  crystal graph.
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

/-- The component equivalence relation is the reachability relation of the crystal graph. -/
@[simp]
theorem componentSetoid_apply {x y : B} :
    c.componentSetoid x y ↔ Relation.ReflTransGen c.Adj x y :=
  Iff.of_eq (congrFun (congrFun
    (SimpleGraph.reachable_fromEdgeSet_fromRel_eq_reflTransGen (r := c.Adj)
      (inferInstance : Std.Symm c.Adj)) x) y)

/-- The connected **component** of `x`: the set of elements joined to `x` by a chain of arrows of
the crystal graph. -/
def component (x : B) : Set B :=
  {y | c.componentSetoid x y}

/-- An element lies in the component of `x` exactly when it is reachable from `x` in the crystal
graph. -/
@[simp]
theorem mem_component_iff {x y : B} :
    y ∈ c.component x ↔ Relation.ReflTransGen c.Adj x y :=
  c.componentSetoid_apply

/-- Two elements have the same component exactly when they lie in the same class of the
component equivalence relation. -/
theorem component_eq_iff {x y : B} :
    c.component x = c.component y ↔ c.componentSetoid x y := by
  constructor
  · intro h
    have hx : x ∈ c.component x := c.componentSetoid.refl x
    rw [h] at hx
    exact c.componentSetoid.symm hx
  · intro h
    ext z
    exact ⟨fun hz => c.componentSetoid.trans (c.componentSetoid.symm h) hz,
      fun hz => c.componentSetoid.trans h hz⟩

/-- A component is closed under the raising operators. -/
theorem mem_component_of_e_eq_some {i : b.support} {x y z : B} (hx : y ∈ c.component x)
    (h : c.e i y = some z) : z ∈ c.component x := by
  rw [mem_component_iff] at hx ⊢
  exact hx.tail ⟨i, Or.inl h⟩

/-- A component is closed under the lowering operators. -/
theorem mem_component_of_f_eq_some {i : b.support} {x y z : B} (hx : y ∈ c.component x)
    (h : c.f i y = some z) : z ∈ c.component x := by
  rw [mem_component_iff] at hx ⊢
  exact hx.tail ⟨i, Or.inr h⟩

/-- Raising preserves the component. -/
theorem component_eq_of_e_eq_some {i : b.support} {x y : B} (h : c.e i x = some y) :
    c.component x = c.component y :=
  c.component_eq_iff.2 (c.mem_component_of_e_eq_some (c.componentSetoid.refl x) h)

/-- Lowering preserves the component. -/
theorem component_eq_of_f_eq_some {i : b.support} {x y : B} (h : c.f i x = some y) :
    c.component x = c.component y :=
  c.component_eq_iff.2 (c.mem_component_of_f_eq_some (c.componentSetoid.refl x) h)

end Component

/-! ### The crystal structure on a component -/

section ComponentCrystal

variable (c : NormalCrystal P b B) (x : B)

private def restrictOption (o : Option B) (h : ∀ z, o = some z → z ∈ c.component x) :
    Option (c.component x) :=
  match o with
  | none => none
  | some z => some ⟨z, h z rfl⟩

private theorem restrictOption_eq_some_iff {o : Option B}
    {h : ∀ z, o = some z → z ∈ c.component x} {z : c.component x} :
    restrictOption c x o h = some z ↔ o = some z.1 := by
  unfold restrictOption
  cases o <;> simp [Subtype.ext_iff]

private theorem restrictOption_eq_none_iff {o : Option B}
    {h : ∀ z, o = some z → z ∈ c.component x} :
    restrictOption c x o h = none ↔ o = none := by
  unfold restrictOption
  cases o <;> simp

private abbrev componentE (i : b.support) (y : c.component x) : Option (c.component x) :=
  restrictOption c x (c.e i y.1) fun _ h => c.mem_component_of_e_eq_some y.2 h

private abbrev componentF (i : b.support) (y : c.component x) : Option (c.component x) :=
  restrictOption c x (c.f i y.1) fun _ h => c.mem_component_of_f_eq_some y.2 h

/-- The **component crystal**: the restriction of `c` to the connected component of `x`. The
weight and the string lengths are inherited, and the root operators are those of `c`, which stay
inside the component. -/
def componentCrystal : NormalCrystal P b (c.component x) where
  wt y := c.wt y.1
  e := c.componentE x
  f := c.componentF x
  ε i y := c.ε i y.1
  φ i y := c.φ i y.1
  f_eq_some_iff := by
    intro i y z
    have hF : c.componentF x i y = some z ↔ c.f i y.1 = some z.1 := restrictOption_eq_some_iff c x
    have hE : c.componentE x i z = some y ↔ c.e i z.1 = some y.1 := restrictOption_eq_some_iff c x
    rw [hF, hE]
    exact c.f_eq_some_iff
  wt_of_e_eq_some := by
    intro i y z h
    have hE : c.componentE x i y = some z ↔ c.e i y.1 = some z.1 := restrictOption_eq_some_iff c x
    rw [hE] at h
    exact c.wt_of_e_eq_some h
  ε_eq_zero_iff := by
    intro i y
    have hE : c.componentE x i y = none ↔ c.e i y.1 = none := restrictOption_eq_none_iff c x
    rw [hE]
    exact c.ε_eq_zero_iff
  ε_of_e_eq_some := by
    intro i y z h
    have hE : c.componentE x i y = some z ↔ c.e i y.1 = some z.1 := restrictOption_eq_some_iff c x
    rw [hE] at h
    exact c.ε_of_e_eq_some h
  φ_eq_zero_iff := by
    intro i y
    have hF : c.componentF x i y = none ↔ c.f i y.1 = none := restrictOption_eq_none_iff c x
    rw [hF]
    exact c.φ_eq_zero_iff
  φ_sub_ε := fun i y => c.φ_sub_ε i y.1

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
  -- the projection of the structure literal does not reduce under `exact`
  change c.componentE x i y = some z ↔ c.e i y.1 = some z.1
  exact restrictOption_eq_some_iff c x

@[simp]
theorem componentCrystal_f_eq_some_iff {i : b.support} {y z : c.component x} :
    (c.componentCrystal x).f i y = some z ↔ c.f i y.1 = some z.1 := by
  -- the projection of the structure literal does not reduce under `exact`
  change c.componentF x i y = some z ↔ c.f i y.1 = some z.1
  exact restrictOption_eq_some_iff c x

@[simp]
theorem componentCrystal_e_eq_none_iff {i : b.support} {y : c.component x} :
    (c.componentCrystal x).e i y = none ↔ c.e i y.1 = none := by
  -- the projection of the structure literal does not reduce under `exact`
  change c.componentE x i y = none ↔ c.e i y.1 = none
  exact restrictOption_eq_none_iff c x

@[simp]
theorem componentCrystal_f_eq_none_iff {i : b.support} {y : c.component x} :
    (c.componentCrystal x).f i y = none ↔ c.f i y.1 = none := by
  -- the projection of the structure literal does not reduce under `exact`
  change c.componentF x i y = none ↔ c.f i y.1 = none
  exact restrictOption_eq_none_iff c x

/-- The crystal graph of a component is the restriction of the crystal graph of the ambient
crystal. -/
@[simp]
theorem componentCrystal_adj_iff {y z : c.component x} :
    (c.componentCrystal x).Adj y z ↔ c.Adj y.1 z.1 := by
  simp [Adj, componentCrystal_e_eq_some_iff, componentCrystal_f_eq_some_iff]

/-- The inclusion of a component into the ambient crystal is a strict morphism. -/
def StrictHom.componentIncl : StrictHom (c.componentCrystal x) c where
  toFun y := y.1
  wt_toFun y := (rfl)
  e_toFun i y := by
    cases h : c.e i y.1 with
    | none =>
      have hz : (c.componentCrystal x).e i y = none :=
        (c.componentCrystal_e_eq_none_iff x).mpr h
      rw [hz, Option.map_none]
    | some z =>
      have hz : (c.componentCrystal x).e i y =
          some ⟨z, c.mem_component_of_e_eq_some y.2 h⟩ :=
        (c.componentCrystal_e_eq_some_iff x).mpr h
      rw [hz, Option.map_some]

@[simp]
theorem StrictHom.componentIncl_apply (y : c.component x) :
    StrictHom.componentIncl c x y = y.1 := (rfl)

end ComponentCrystal

/-! ### Components and transport -/

section Bridge

variable (c : NormalCrystal P b B) (e : B ≃ B')

/-- Transport along a bijection relates the crystal graphs through the bijection. -/
@[simp]
theorem congr_adj (x y : B') :
    (c.congr e).Adj x y ↔ c.Adj (e.symm x) (e.symm y) := by
  simp only [Adj, congr_e, congr_f]
  constructor
  · rintro ⟨i, h | h⟩
    · exact ⟨i, Or.inl ((Equiv.eq_symm_apply (Equiv.optionCongr e) (x := some y)
        (y := c.e i (e.symm x))).2 h)⟩
    · exact ⟨i, Or.inr ((Equiv.eq_symm_apply (Equiv.optionCongr e) (x := some y)
        (y := c.f i (e.symm x))).2 h)⟩
  · rintro ⟨i, h | h⟩
    · exact ⟨i, Or.inl ((Equiv.eq_symm_apply (Equiv.optionCongr e) (x := some y)
        (y := c.e i (e.symm x))).1 h)⟩
    · exact ⟨i, Or.inr ((Equiv.eq_symm_apply (Equiv.optionCongr e) (x := some y)
        (y := c.f i (e.symm x))).1 h)⟩

/-- Transport along a bijection conjugates the component equivalence relations. -/
theorem componentSetoid_congr :
    (c.congr e).componentSetoid = c.componentSetoid.comap ⇑e.symm := by
  refine Setoid.ext fun x y => ?_
  rw [componentSetoid_apply, Setoid.comap_rel, componentSetoid_apply]
  exact ⟨fun h => Relation.ReflTransGen.lift ⇑e.symm
      (fun a b => (c.congr_adj e a b).1) x y h,
    fun h => by
      have key := Relation.ReflTransGen.lift ⇑e
        (fun a b hab => (c.congr_adj e (e a) (e b)).2 (by simpa using hab))
        (e.symm x) (e.symm y) h
      simp only [Function.onFun, Equiv.apply_symm_apply] at key ⊢
      exact key⟩

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
