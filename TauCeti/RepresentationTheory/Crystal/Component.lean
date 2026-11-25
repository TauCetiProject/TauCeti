/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import TauCeti.Data.Set.OptionRestrict
public import TauCeti.RepresentationTheory.Crystal.Sigma
public import TauCeti.RepresentationTheory.Crystal.Word
import TauCeti.Data.Option.Basic

/-!
# Connected components of normal crystals

The *crystal graph* of a normal crystal `c` on `B` has an edge between `x` and `y` whenever some
raising operator sends one of them to the other. Its connected components are the *connected
components* of the crystal: each of them is closed under all root operators, hence is again a
normal crystal, and the crystal is the direct sum of its components. For crystals of integrable
modules, or of Littelmann paths, the components are the crystals of the irreducible summands, and
the component of a dominant straight path is the path crystal `B(λ)`.

This file sets up this decomposition, using Mathlib's connected components of simple graphs and
the direct sums `TauCeti.NormalCrystal.sigma` of `TauCeti.RepresentationTheory.Crystal.Sigma`.

Strict morphisms and strict isomorphisms of crystals are homomorphisms and isomorphisms of crystal
graphs (`TauCeti.NormalCrystal.StrictHom.toGraphHom`,
`TauCeti.NormalCrystal.StrictIso.toGraphIso`), so a strict isomorphism `ψ` acts on connected
components, through `SimpleGraph.Iso.connectedComponentEquiv`, carrying the component of a vertex
`x` to the component of `ψ x`. Restricting `ψ` to these two components is again a strict
isomorphism (`TauCeti.NormalCrystal.StrictIso.componentIso`): components transport, as crystals.

## Main definitions

* `TauCeti.NormalCrystal.graph`: the undirected, uncoloured crystal graph.
* `TauCeti.NormalCrystal.restrict`: the normal crystal on a set of elements closed under the
  root operators, with its inclusion `TauCeti.NormalCrystal.restrictHom`.
* `TauCeti.NormalCrystal.component`: a connected component of the crystal graph as a normal
  crystal.
* `TauCeti.NormalCrystal.StrictHom.toGraphHom`, `TauCeti.NormalCrystal.StrictIso.toGraphIso`:
  strict morphisms and strict isomorphisms of crystals as maps of crystal graphs, so that they act
  on connected components.
* `TauCeti.NormalCrystal.StrictIso.componentIso`: the strict isomorphism of two components
  induced by a strict isomorphism of the ambient crystals.

## Main results

* `TauCeti.NormalCrystal.reachable_of_eWord_eq_some` and
  `TauCeti.NormalCrystal.reachable_of_fWord_eq_some`: elements related by a raising or lowering
  word are reachable in the crystal graph.
* `TauCeti.NormalCrystal.connected_component_graph`: each component is a connected crystal.
* `TauCeti.NormalCrystal.sigmaComponentsIso`: a normal crystal is strictly isomorphic to the
  direct sum of its connected components.

## References

* M. Kashiwara, *On crystal bases*, CMS Conf. Proc. 16 (1995), §7.
* D. Bump and A. Schilling, *Crystal bases: representations and combinatorics*, World Scientific
  (2017), Ch. 2.
* P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math. 142 (1995).
-/

public section

namespace TauCeti

namespace NormalCrystal

universe u v w x₁ x₂ x₃

variable {ι : Type u} {X : Type v} {Y : Type w} [AddCommGroup X] [AddCommGroup Y]
  {P : RootDatum ι X Y} {b : P.Base} {B : Type x₁} {B' : Type x₂}

/-! ### The crystal graph -/

section Graph

variable (c : NormalCrystal P b B) {i : b.support} {x y : B}

/-- The **crystal graph**: `x` and `y` are adjacent when a raising operator sends one of them to the
other. It forgets the colours and the orientation of the edges of the crystal. -/
def graph : SimpleGraph B :=
  SimpleGraph.fromRel fun x y => ∃ i, c.e i x = some y

theorem graph_adj_iff : c.graph.Adj x y ↔ ∃ i, c.e i x = some y ∨ c.e i y = some x := by
  simp only [graph, SimpleGraph.fromRel_adj, ← exists_or, and_iff_right_iff_imp]
  rintro ⟨i, h | h⟩ rfl <;> exact c.e_ne_some_self h

theorem graph_adj_of_e_eq_some (h : c.e i x = some y) : c.graph.Adj x y :=
  c.graph_adj_iff.2 ⟨i, Or.inl h⟩

theorem graph_adj_of_f_eq_some (h : c.f i x = some y) : c.graph.Adj x y :=
  c.graph_adj_iff.2 ⟨i, Or.inr (c.f_eq_some_iff.1 h)⟩

/-- Lowering operators also define the crystal graph. -/
theorem graph_adj_iff_f : c.graph.Adj x y ↔ ∃ i, c.f i x = some y ∨ c.f i y = some x := by
  simp only [graph_adj_iff, c.f_eq_some_iff, or_comm]

@[simp]
theorem dual_graph : c.dual.graph = c.graph := by
  ext x y
  rw [graph_adj_iff, dual_e, ← graph_adj_iff_f]

/-- Elements connected by a word of raising operators lie in the same connected component of the
crystal graph. -/
theorem reachable_of_eWord_eq_some {w : List b.support} (h : c.eWord w x = some y) :
    c.graph.Reachable x y := by
  induction w generalizing x with
  | nil =>
    simp only [eWord_nil, Option.some.injEq] at h
    exact h ▸ SimpleGraph.Reachable.refl _
  | cons i w ih =>
    obtain ⟨z, hz, hy⟩ := Option.bind_eq_some_iff.mp (c.eWord_cons i w x ▸ h)
    exact (c.graph_adj_of_e_eq_some hz).reachable.trans (ih hy)

/-- Elements connected by an iterated raising operator lie in the same connected component of the
crystal graph. -/
theorem reachable_of_eIter_eq_some {n : ℕ} (h : c.eIter i n x = some y) :
    c.graph.Reachable x y :=
  c.reachable_of_eWord_eq_some (w := List.replicate n i) (by rwa [eWord_replicate])

/-- Elements connected by an iterated lowering operator lie in the same connected component of the
crystal graph. -/
theorem reachable_of_fIter_eq_some {n : ℕ} (h : c.fIter i n x = some y) : c.graph.Reachable x y :=
  (c.reachable_of_eIter_eq_some (c.fIter_eq_some_iff.mp h)).symm

/-- Elements connected by a word of lowering operators lie in the same connected component of the
crystal graph. -/
theorem reachable_of_fWord_eq_some {w : List b.support} (h : c.fWord w x = some y) :
    c.graph.Reachable x y :=
  (c.reachable_of_eWord_eq_some (c.fWord_eq_some_iff.mp h)).symm

/-- A normal crystal generated by lowering words from a single element has a connected crystal
graph. -/
theorem connected_graph_of_forall_exists_fWord_eq_some {h : B}
    (hgen : ∀ x, ∃ w : List b.support, c.fWord w h = some x) : c.graph.Connected := by
  refine c.graph.connected_iff_exists_forall_reachable.mpr ⟨h, fun x ↦ ?_⟩
  obtain ⟨w, hw⟩ := hgen x
  exact c.reachable_of_fWord_eq_some hw

end Graph

/-! ### Restriction to a union of components -/

section Restrict

variable (c : NormalCrystal P b B) (S : Set B)
  (hS : ∀ ⦃x y⦄, c.graph.Adj x y → x ∈ S → y ∈ S)

/-- The **restriction** of a normal crystal to a set `S` of elements closed under adjacency in the
crystal graph, i.e. a union of connected components: the root operators preserve `S`. -/
def restrict : NormalCrystal P b S where
  wt x := c.wt x
  e i := S.optionRestrict S (c.e i) fun _ _ h => hS (c.graph_adj_of_e_eq_some h)
  f i := S.optionRestrict S (c.f i) fun _ _ h => hS (c.graph_adj_of_f_eq_some h)
  ε i x := c.ε i x
  φ i x := c.φ i x
  f_eq_some_iff {i x y} := by simp only [Set.optionRestrict_eq_some_iff, c.f_eq_some_iff]
  wt_of_e_eq_some h := c.wt_of_e_eq_some (Set.optionRestrict_eq_some_iff.1 h)
  ε_eq_zero_iff {i x} := by simp only [Set.optionRestrict_eq_none_iff, c.ε_eq_zero_iff]
  ε_of_e_eq_some h := c.ε_of_e_eq_some (Set.optionRestrict_eq_some_iff.1 h)
  φ_eq_zero_iff {i x} := by simp only [Set.optionRestrict_eq_none_iff, c.φ_eq_zero_iff]
  φ_sub_ε i x := c.φ_sub_ε i x

variable {c S hS} {i : b.support}

@[simp]
theorem restrict_wt (x : S) : (c.restrict S hS).wt x = c.wt x := (rfl)

@[simp]
theorem restrict_ε (x : S) : (c.restrict S hS).ε i x = c.ε i x := (rfl)

@[simp]
theorem restrict_φ (x : S) : (c.restrict S hS).φ i x = c.φ i x := (rfl)

@[simp]
theorem restrict_e_eq_some_iff {x y : S} :
    (c.restrict S hS).e i x = some y ↔ c.e i x = some y.val :=
  Set.optionRestrict_eq_some_iff (hg := fun _ _ h => hS (c.graph_adj_of_e_eq_some h))

@[simp]
theorem restrict_f_eq_some_iff {x y : S} :
    (c.restrict S hS).f i x = some y ↔ c.f i x = some y.val :=
  Set.optionRestrict_eq_some_iff (hg := fun _ _ h => hS (c.graph_adj_of_f_eq_some h))

@[simp]
theorem unattach_restrict_e (x : S) : ((c.restrict S hS).e i x).unattach = c.e i x :=
  Set.unattach_optionRestrict (hg := fun _ _ h => hS (c.graph_adj_of_e_eq_some h)) x

@[simp]
theorem unattach_restrict_f (x : S) : ((c.restrict S hS).f i x).unattach = c.f i x :=
  Set.unattach_optionRestrict (hg := fun _ _ h => hS (c.graph_adj_of_f_eq_some h)) x

@[simp]
theorem unattach_restrict_eIter (n : ℕ) (x : S) :
    ((c.restrict S hS).eIter i n x).unattach = c.eIter i n x.val := by
  induction n generalizing x with
  | zero => simp
  | succ n ih => simp [eIter_succ, ih]

@[simp]
theorem unattach_restrict_fIter (n : ℕ) (x : S) :
    ((c.restrict S hS).fIter i n x).unattach = c.fIter i n x.val := by
  induction n generalizing x with
  | zero => simp
  | succ n ih => simp [fIter_succ, ih]

/-- The crystal graph of a restriction is the induced subgraph. -/
theorem restrict_graph : (c.restrict S hS).graph = c.graph.induce S := by
  ext x y
  simp [graph_adj_iff]

variable (c S hS) in
/-- The inclusion of a restriction as a strict morphism. -/
def restrictHom : StrictHom (c.restrict S hS) c where
  toFun := Subtype.val
  wt_toFun _ := rfl
  e_toFun _ x := (unattach_restrict_e x).symm

@[simp]
theorem coe_restrictHom : ⇑(c.restrictHom S hS) = Subtype.val := (rfl)

end Restrict

/-! ### Connected components -/

section Component

variable (c : NormalCrystal P b B)

/-- A **connected component** of a normal crystal, as a normal crystal: the restriction to the
vertices of a connected component of the crystal graph. -/
def component (C : c.graph.ConnectedComponent) : NormalCrystal P b C :=
  c.restrict C.supp fun _ _ h hx => C.mem_supp_of_adj_mem_supp hx h

theorem component_eq_restrict (C : c.graph.ConnectedComponent) :
    c.component C = c.restrict C.supp fun _ _ h hx => C.mem_supp_of_adj_mem_supp hx h := (rfl)

section

variable {c} {C : c.graph.ConnectedComponent} {i : b.support}

@[simp]
theorem component_wt (x : C) : (c.component C).wt x = c.wt x.val := (rfl)

@[simp]
theorem component_ε (x : C) : (c.component C).ε i x = c.ε i x.val := (rfl)

@[simp]
theorem component_φ (x : C) : (c.component C).φ i x = c.φ i x.val := (rfl)

@[simp]
theorem component_e_eq_some_iff {x y : C} :
    (c.component C).e i x = some y ↔ c.e i x.val = some y.val :=
  restrict_e_eq_some_iff

@[simp]
theorem component_f_eq_some_iff {x y : C} :
    (c.component C).f i x = some y ↔ c.f i x.val = some y.val :=
  restrict_f_eq_some_iff

@[simp]
theorem unattach_component_e (x : C) : ((c.component C).e i x).unattach = c.e i x.val :=
  unattach_restrict_e x

@[simp]
theorem unattach_component_f (x : C) : ((c.component C).f i x).unattach = c.f i x.val :=
  unattach_restrict_f x

@[simp]
theorem unattach_component_eIter (n : ℕ) (x : C) :
    ((c.component C).eIter i n x).unattach = c.eIter i n x.val :=
  unattach_restrict_eIter n x

@[simp]
theorem unattach_component_fIter (n : ℕ) (x : C) :
    ((c.component C).fIter i n x).unattach = c.fIter i n x.val :=
  unattach_restrict_fIter n x

end

/-- The crystal graph of a component is the induced graph on that component. -/
theorem component_graph (C : c.graph.ConnectedComponent) :
    (c.component C).graph = C.toSimpleGraph :=
  restrict_graph

/-- **Each component is a connected crystal.** -/
theorem connected_component_graph (C : c.graph.ConnectedComponent) :
    (c.component C).graph.Connected := by
  rw [component_graph]
  exact C.connected_toSimpleGraph

/-- The inclusion of a connected component as a strict morphism. -/
def componentHom (C : c.graph.ConnectedComponent) : StrictHom (c.component C) c :=
  c.restrictHom _ _

@[simp]
theorem componentHom_apply (C : c.graph.ConnectedComponent) (x : C) : c.componentHom C x = x.val :=
  (rfl)

end Component

/-! ### Strict morphisms act on components -/

section Maps

variable {c : NormalCrystal P b B} {d : NormalCrystal P b B'}

/-- A strict morphism of normal crystals is a homomorphism of crystal graphs. -/
def StrictHom.toGraphHom (ψ : StrictHom c d) : c.graph →g d.graph where
  toFun := ψ
  map_rel' {x y} h := by
    obtain ⟨i, h | h⟩ := c.graph_adj_iff.1 h
    · exact d.graph_adj_of_e_eq_some (by rw [ψ.e_apply, h, Option.map_some])
    · exact (d.graph_adj_of_e_eq_some (by rw [ψ.e_apply, h, Option.map_some])).symm

@[simp]
theorem StrictHom.coe_toGraphHom (ψ : StrictHom c d) : ⇑ψ.toGraphHom = ψ := (rfl)

/-- A strict isomorphism of normal crystals is an isomorphism of crystal graphs; in particular it
induces a bijection of connected components (`SimpleGraph.Iso.connectedComponentEquiv`). -/
def StrictIso.toGraphIso (ψ : StrictIso c d) : c.graph ≃g d.graph where
  toEquiv := ψ.toEquiv
  map_rel_iff' {x y} := by
    refine ⟨fun h => ?_, fun h => ?_⟩
    · simpa using ψ.symm.toStrictHom.toGraphHom.map_rel h
    · simpa using ψ.toStrictHom.toGraphHom.map_rel h

@[simp]
theorem StrictIso.coe_toGraphIso (ψ : StrictIso c d) : ⇑ψ.toGraphIso = ψ := (rfl)

end Maps

/-! ### Components of a strict isomorphism -/

section Iso

variable {c : NormalCrystal P b B} {d : NormalCrystal P b B'} (ψ : StrictIso c d)

/-- **A strict isomorphism restricts to its components**: for every connected component `C` of
`c.graph`, the component crystals `c.component C` and
`d.component (ψ.toGraphIso.connectedComponentEquiv C)` are strictly isomorphic, through Mathlib's
equivalence `SimpleGraph.ConnectedComponent.isoEquivSupp` of their vertex sets. -/
def StrictIso.componentIso (C : c.graph.ConnectedComponent) :
    StrictIso (c.component C) (d.component (ψ.toGraphIso.connectedComponentEquiv C)) where
  toEquiv := SimpleGraph.ConnectedComponent.isoEquivSupp ψ.toGraphIso C
  wt_toFun x := ψ.wt_apply x.val
  e_toFun i x := by
    -- `isoEquivSupp` acts on vertices as `ψ`, so pushing `Subtype.val` through the required
    -- equality leaves the ambient compatibility `ψ.e_apply`.
    have hΦ : ∀ y : ↥C, ((SimpleGraph.ConnectedComponent.isoEquivSupp ψ.toGraphIso C).toFun y).val
        = ψ y.val := fun _ => rfl
    apply Option.map_injective Subtype.val_injective
    rw [Option.map_map]
    conv_rhs => rw [Option.map_subtype (g := ψ) (fun x _ => rfl)]
    change ((d.component (ψ.toGraphIso.connectedComponentEquiv C)).e i
        ((SimpleGraph.ConnectedComponent.isoEquivSupp ψ.toGraphIso C).toFun x)).unattach
      = Option.map ψ ((c.component C).e i x).unattach
    rw [component_eq_restrict, component_eq_restrict, unattach_restrict_e, unattach_restrict_e, hΦ,
      ψ.e_apply]

/-- The underlying map of `StrictIso.componentIso` sends a vertex `x` of `C` to `ψ x.1`. -/
@[simp]
theorem StrictIso.componentIso_apply (C : c.graph.ConnectedComponent) (x : C) :
    (ψ.componentIso C x).val = ψ x.val := (rfl)

/-- The underlying map of the inverse of `StrictIso.componentIso` sends a vertex `y` of the target
component to `ψ.symm y.1`. -/
@[simp]
theorem StrictIso.componentIso_symm_apply (C : c.graph.ConnectedComponent)
    (y : (ψ.toGraphIso.connectedComponentEquiv C)) :
    ((ψ.componentIso C).symm y).val = ψ.symm y.val := by
  apply EquivLike.injective ψ
  rw [← StrictIso.componentIso_apply, StrictIso.apply_symm_apply, StrictIso.apply_symm_apply]

end Iso

/-! ### Decomposition into components -/

section Decomposition

variable (c : NormalCrystal P b B)

/-- Every element lies in exactly one connected component: the strict morphism out of the direct
sum of the components induced by their inclusions is bijective. -/
theorem bijective_sigmaElim_componentHom :
    Function.Bijective (StrictHom.sigmaElim c.componentHom) := by
  convert c.graph.verticesEquivSigmaConnectedComponent.symm.bijective
  ext ⟨C, x⟩
  exact StrictHom.sigmaElim_apply (c := c.component) x c.componentHom

/-- **A normal crystal is the direct sum of its connected components.** Its underlying bijection is
Mathlib's partition `SimpleGraph.verticesEquivSigmaConnectedComponent` of the vertices. -/
def sigmaComponentsIso : StrictIso (sigma c.component) c where
  toEquiv := c.graph.verticesEquivSigmaConnectedComponent.symm
  wt_toFun := fun ⟨C, x⟩ => by rw [sigma_wt]; exact (c.componentHom C).wt_apply x
  e_toFun i := fun ⟨C, x⟩ => by
    rw [sigma_e, Option.map_map]; exact (c.componentHom C).e_apply i x

@[simp]
theorem sigmaComponentsIso_apply (C : c.graph.ConnectedComponent) (x : C) :
    c.sigmaComponentsIso ⟨C, x⟩ = x.val := (rfl)

@[simp]
theorem sigmaComponentsIso_symm_apply (x : B) :
    c.sigmaComponentsIso.symm x = ⟨c.graph.connectedComponentMk x, x, rfl⟩ :=
  EquivLike.injective c.sigmaComponentsIso (by simp)

end Decomposition

end NormalCrystal

end TauCeti
