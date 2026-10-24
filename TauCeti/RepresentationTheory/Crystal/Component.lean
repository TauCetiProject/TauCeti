/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import TauCeti.RepresentationTheory.Crystal.Basic

/-!
# Connected components of normal crystals

The *crystal graph* of a normal crystal `c` on `B` has an edge between `x` and `y` whenever some
raising operator sends one of them to the other. Its connected components are the *connected
components* of the crystal: each of them is closed under all root operators, hence is again a
normal crystal, and the crystal is the direct sum of its components. For crystals of integrable
modules, or of Littelmann paths, the components are the crystals of the irreducible summands, and
the component of a dominant straight path is the path crystal `B(λ)`.

This file sets up this decomposition, using Mathlib's connected components of simple graphs.

## Main definitions

* `TauCeti.NormalCrystal.graph`: the undirected, uncoloured crystal graph.
* `TauCeti.NormalCrystal.restrict`: the normal crystal on a set of elements closed under the
  root operators, with its inclusion `TauCeti.NormalCrystal.restrictHom`.
* `TauCeti.NormalCrystal.component`: a connected component of the crystal graph as a normal
  crystal.
* `TauCeti.NormalCrystal.sigma`: the direct sum of a family of normal crystals, with the
  inclusions `TauCeti.NormalCrystal.StrictHom.sigmaMk` of the summands and the induced strict
  morphism `TauCeti.NormalCrystal.StrictHom.sigmaElim` out of the sum.
* `TauCeti.NormalCrystal.StrictHom.toGraphHom`, `TauCeti.NormalCrystal.StrictIso.toGraphIso`:
  strict morphisms and strict isomorphisms of crystals as maps of crystal graphs, so that they act
  on connected components.

## Main results

* `TauCeti.NormalCrystal.e_ne_some_self`: the crystal graph has no loops.
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

/-- No raising operator fixes an element, since it changes the weight by a simple root. -/
theorem e_ne_some_self : c.e i x ≠ some x := by
  intro h
  have hwt := c.wt_of_e_eq_some h
  have h0 : P.root i = 0 := by simpa using hwt
  have h2 := P.root_coroot_two i
  rw [h0, map_zero, LinearMap.zero_apply] at h2
  exact two_ne_zero h2.symm

/-- No lowering operator fixes an element. -/
theorem f_ne_some_self : c.f i x ≠ some x :=
  fun h => c.e_ne_some_self (c.f_eq_some_iff.1 h)

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

end Graph

/-! ### Restriction to a union of components -/

section Restrict

variable (c : NormalCrystal P b B) (S : Set B)
  (hS : ∀ ⦃x y⦄, c.graph.Adj x y → x ∈ S → y ∈ S)

/-- A partial map on `B` that preserves `S`, as a partial map on `S`. -/
private def restrictOp (g : B → Option B) (hg : ∀ ⦃x y⦄, g x = some y → x ∈ S → y ∈ S)
    (x : S) : Option S :=
  (g x).pmap (fun y hy => ⟨y, hg hy x.2⟩) fun _ h => h

private theorem restrictOp_eq_some_iff {g : B → Option B}
    {hg : ∀ ⦃x y⦄, g x = some y → x ∈ S → y ∈ S} {x y : S} :
    restrictOp S g hg x = some y ↔ g x = some y.1 := by
  simp [restrictOp, Subtype.ext_iff, eq_comm (a := y.1)]

private theorem restrictOp_eq_none_iff {g : B → Option B}
    {hg : ∀ ⦃x y⦄, g x = some y → x ∈ S → y ∈ S} {x : S} :
    restrictOp S g hg x = none ↔ g x = none := by
  simp [restrictOp]

private theorem unattach_restrictOp {g : B → Option B}
    {hg : ∀ ⦃x y⦄, g x = some y → x ∈ S → y ∈ S} (x : S) :
    (restrictOp S g hg x).unattach = g x := by
  cases h : g x with
  | none => rw [(restrictOp_eq_none_iff S).2 h, Option.unattach_none]
  | some y =>
    rw [(restrictOp_eq_some_iff S (y := ⟨y, hg h x.2⟩)).2 h, Option.unattach_some]

/-- The **restriction** of a normal crystal to a set `S` of elements closed under adjacency in the
crystal graph, i.e. a union of connected components: the root operators preserve `S`. -/
def restrict : NormalCrystal P b S where
  wt x := c.wt x
  e i := restrictOp S (c.e i) fun _ _ h => hS (c.graph_adj_of_e_eq_some h)
  f i := restrictOp S (c.f i) fun _ _ h => hS (c.graph_adj_of_f_eq_some h)
  ε i x := c.ε i x
  φ i x := c.φ i x
  f_eq_some_iff {i x y} := by simp only [restrictOp_eq_some_iff, c.f_eq_some_iff]
  wt_of_e_eq_some h := c.wt_of_e_eq_some ((restrictOp_eq_some_iff S).1 h)
  ε_eq_zero_iff {i x} := by simp only [restrictOp_eq_none_iff, c.ε_eq_zero_iff]
  ε_of_e_eq_some h := c.ε_of_e_eq_some ((restrictOp_eq_some_iff S).1 h)
  φ_eq_zero_iff {i x} := by simp only [restrictOp_eq_none_iff, c.φ_eq_zero_iff]
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
    (c.restrict S hS).e i x = some y ↔ c.e i x = some y.1 :=
  restrictOp_eq_some_iff S (hg := fun _ _ h => hS (c.graph_adj_of_e_eq_some h))

@[simp]
theorem restrict_f_eq_some_iff {x y : S} :
    (c.restrict S hS).f i x = some y ↔ c.f i x = some y.1 :=
  restrictOp_eq_some_iff S (hg := fun _ _ h => hS (c.graph_adj_of_f_eq_some h))

@[simp]
theorem unattach_restrict_e (x : S) : ((c.restrict S hS).e i x).unattach = c.e i x :=
  unattach_restrictOp S (hg := fun _ _ h => hS (c.graph_adj_of_e_eq_some h)) x

@[simp]
theorem unattach_restrict_f (x : S) : ((c.restrict S hS).f i x).unattach = c.f i x :=
  unattach_restrictOp S (hg := fun _ _ h => hS (c.graph_adj_of_f_eq_some h)) x

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
theorem componentHom_apply (C : c.graph.ConnectedComponent) (x : C) : c.componentHom C x = x.1 :=
  (rfl)

end Component

/-! ### Direct sums -/

section Sigma

variable {κ : Type*} {β : κ → Type*} (c : ∀ k, NormalCrystal P b (β k))

/-- The **direct sum** of a family of normal crystals: the disjoint union of the underlying types,
on which the root operators act within each summand. -/
def sigma : NormalCrystal P b (Σ k, β k) where
  wt x := (c x.1).wt x.2
  e i x := ((c x.1).e i x.2).map (Sigma.mk x.1)
  f i x := ((c x.1).f i x.2).map (Sigma.mk x.1)
  ε i x := (c x.1).ε i x.2
  φ i x := (c x.1).φ i x.2
  f_eq_some_iff {i x y} := by
    obtain ⟨k, x⟩ := x
    obtain ⟨l, y⟩ := y
    simp only [Option.map_eq_some_iff, Sigma.mk.injEq]
    constructor
    · rintro ⟨z, hz, rfl, hzy⟩
      obtain rfl := eq_of_heq hzy
      exact ⟨x, (c k).f_eq_some_iff.1 hz, rfl, .rfl⟩
    · rintro ⟨z, hz, rfl, hzy⟩
      obtain rfl := eq_of_heq hzy
      exact ⟨y, (c l).f_eq_some_iff.2 hz, rfl, .rfl⟩
  wt_of_e_eq_some {i x y} h := by
    obtain ⟨z, hz, rfl⟩ := Option.map_eq_some_iff.1 h
    exact (c x.1).wt_of_e_eq_some hz
  ε_eq_zero_iff := by simp [(c _).ε_eq_zero_iff]
  ε_of_e_eq_some {i x y} h := by
    obtain ⟨z, hz, rfl⟩ := Option.map_eq_some_iff.1 h
    exact (c x.1).ε_of_e_eq_some hz
  φ_eq_zero_iff := by simp [(c _).φ_eq_zero_iff]
  φ_sub_ε i x := (c x.1).φ_sub_ε i x.2

variable {c} {i : b.support} {k : κ} (x : β k)

@[simp]
theorem sigma_wt : (sigma c).wt ⟨k, x⟩ = (c k).wt x := (rfl)

@[simp]
theorem sigma_e : (sigma c).e i ⟨k, x⟩ = ((c k).e i x).map (Sigma.mk k) := (rfl)

@[simp]
theorem sigma_f : (sigma c).f i ⟨k, x⟩ = ((c k).f i x).map (Sigma.mk k) := (rfl)

@[simp]
theorem sigma_ε : (sigma c).ε i ⟨k, x⟩ = (c k).ε i x := (rfl)

@[simp]
theorem sigma_φ : (sigma c).φ i ⟨k, x⟩ = (c k).φ i x := (rfl)

namespace StrictHom

variable (c) in
/-- The inclusion of a summand into a direct sum. -/
def sigmaMk (k : κ) : StrictHom (c k) (sigma c) where
  toFun := Sigma.mk k
  wt_toFun _ := rfl
  e_toFun _ _ := rfl

@[simp]
theorem sigmaMk_apply : sigmaMk c k x = ⟨k, x⟩ := (rfl)

variable {d : NormalCrystal P b B'}

/-- The strict morphism out of a direct sum induced by strict morphisms out of the summands. -/
def sigmaElim (ψ : ∀ k, StrictHom (c k) d) : StrictHom (sigma c) d where
  toFun x := ψ x.1 x.2
  wt_toFun x := (ψ x.1).wt_apply x.2
  e_toFun i := fun ⟨k, x⟩ => by simp [Option.map_map, Function.comp_def]

@[simp]
theorem sigmaElim_apply (ψ : ∀ k, StrictHom (c k) d) : sigmaElim ψ ⟨k, x⟩ = ψ k x := (rfl)

@[simp]
theorem sigmaElim_comp_sigmaMk (ψ : ∀ k, StrictHom (c k) d) (k : κ) :
    (sigmaElim ψ).comp (sigmaMk c k) = ψ k :=
  ext fun _ => by simp

/-- Strict morphisms out of a direct sum are determined by their restrictions to the summands. -/
theorem sigma_ext {ψ χ : StrictHom (sigma c) d}
    (h : ∀ k, ψ.comp (sigmaMk c k) = χ.comp (sigmaMk c k)) : ψ = χ :=
  ext fun ⟨k, x⟩ => by simpa using DFunLike.congr_fun (h k) x

end StrictHom

end Sigma

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

/-! ### Decomposition into components -/

section Decomposition

variable (c : NormalCrystal P b B)

/-- Every element lies in exactly one connected component: the strict morphism out of the direct
sum of the components induced by their inclusions is bijective. -/
theorem bijective_sigmaElim_componentHom :
    Function.Bijective (StrictHom.sigmaElim c.componentHom) := by
  refine ⟨?_, fun x => ⟨⟨c.graph.connectedComponentMk x, x, rfl⟩, rfl⟩⟩
  rintro ⟨C, x, hx⟩ ⟨D, y, hy⟩ (h : x = y)
  subst h
  obtain rfl := SimpleGraph.ConnectedComponent.eq_of_common_vertex hx hy
  rfl

/-- **A normal crystal is the direct sum of its connected components.** -/
noncomputable def sigmaComponentsIso : StrictIso (sigma c.component) c :=
  StrictIso.ofBijective _ c.bijective_sigmaElim_componentHom

@[simp]
theorem sigmaComponentsIso_apply (C : c.graph.ConnectedComponent) (x : C) :
    c.sigmaComponentsIso ⟨C, x⟩ = x.1 := by
  simp [sigmaComponentsIso]

@[simp]
theorem sigmaComponentsIso_symm_apply (x : B) :
    c.sigmaComponentsIso.symm x = ⟨c.graph.connectedComponentMk x, x, rfl⟩ :=
  EquivLike.injective c.sigmaComponentsIso (by simp)

end Decomposition

end NormalCrystal

end TauCeti
