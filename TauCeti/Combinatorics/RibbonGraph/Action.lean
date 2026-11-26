/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.RibbonGraph.OfPermutationTriple
public import Mathlib.CategoryTheory.Action.Concrete
public import Mathlib.GroupTheory.FreeGroup.Basic

/-!
# Ribbon graphs are finite sets with two permutations

Finite bipartite ribbon graphs and their morphisms form a category
(`TauCeti.BipartiteRibbonGraph.instCategory`). The generators `0` and `1` of `FreeGroup (Fin 2)`
act on the edges of a graph `Γ` by its rotations `rotB` and `rotW`, and the **edge functor**
`TauCeti.BipartiteRibbonGraph.edgeFunctor` sends `Γ` to its edges with this action, an object of
Mathlib's `Action FintypeCat (FreeGroup (Fin 2))`.

The edge functor is an equivalence of categories (`TauCeti.BipartiteRibbonGraph.edgeEquivalence`):

* it is faithful, since a morphism is determined by its edge map
  (`TauCeti.BipartiteRibbonGraph.Hom.ext`);
* it is full, since the vertices are the cycles of the rotations
  (`TauCeti.BipartiteRibbonGraph.blackEnd_eq_blackEnd_iff`,
  `TauCeti.BipartiteRibbonGraph.whiteEnd_eq_whiteEnd_iff`), so an equivariant map of edges
  induces the maps of vertices;
* it is essentially surjective, since every finite set with two permutations is the edge set of
  the ribbon graph whose vertices are the cycles of those permutations
  (`TauCeti.BipartiteRibbonGraph.ofPerms`), the empty set included.

The requirement that every vertex is the end of an edge is what makes the functor full: a graph
with no edges and one black vertex has the same, empty, edge set as the empty graph but no
morphism to it.

## Main definitions

* `TauCeti.BipartiteRibbonGraph.edgeAction`: the action of `FreeGroup (Fin 2)` on the edges.
* `TauCeti.BipartiteRibbonGraph.edgeFunctor`: the edge functor.
* `TauCeti.BipartiteRibbonGraph.edgeEquivalence`: **finite bipartite ribbon graphs are finite
  `FreeGroup (Fin 2)`-sets.**

## References

* S. K. Lando, A. K. Zvonkin, *Graphs on Surfaces and Their Applications*, Encyclopaedia of
  Mathematical Sciences 141, Springer 2004, §1.3 and §1.5.
-/

public section

noncomputable section

universe u

open CategoryTheory Equiv

namespace TauCeti

namespace BipartiteRibbonGraph

/-- Finite bipartite ribbon graphs form a category, with the morphisms `Hom`. -/
instance instCategory : Category BipartiteRibbonGraph.{u} where
  Hom := Hom
  id := Hom.id
  comp f g := g.comp f
  id_comp := Hom.comp_id
  comp_id := Hom.id_comp
  assoc f g h := Hom.comp_assoc h g f

/-- The categorical identity of a ribbon graph is `BipartiteRibbonGraph.Hom.id`. -/
@[simp]
theorem id_eq_id (Γ : BipartiteRibbonGraph.{u}) : 𝟙 Γ = Hom.id Γ :=
  (rfl)

/-- Categorical composition of ribbon-graph morphisms is `BipartiteRibbonGraph.Hom.comp`, in the
opposite order. -/
@[simp]
theorem comp_eq_comp {Γ Δ Θ : BipartiteRibbonGraph.{u}} (f : Γ ⟶ Δ) (g : Δ ⟶ Θ) :
    f ≫ g = g.comp f :=
  (rfl)

/-- Morphisms of ribbon graphs in the category are equal when their edge maps are. -/
@[ext]
theorem hom_ext {Γ Δ : BipartiteRibbonGraph.{u}} {f g : Γ ⟶ Δ} (h : f.edge = g.edge) : f = g :=
  Hom.ext h

variable (Γ : BipartiteRibbonGraph.{u})

/-- The action of `FreeGroup (Fin 2)` on the edges of a ribbon graph: the generator `0` acts by the
black rotation and `1` by the white rotation. -/
def edgeAction : FreeGroup (Fin 2) →* Perm Γ.E :=
  FreeGroup.lift ![Γ.rotB, Γ.rotW]

@[simp]
theorem edgeAction_of_zero : Γ.edgeAction (FreeGroup.of 0) = Γ.rotB := by
  simp [edgeAction]

@[simp]
theorem edgeAction_of_one : Γ.edgeAction (FreeGroup.of 1) = Γ.rotW := by
  simp [edgeAction]

/-- The edges of a ribbon graph, with the action of `FreeGroup (Fin 2)` by the rotations. -/
@[expose] def edges : Action FintypeCat.{u} (FreeGroup (Fin 2)) :=
  letI : MulAction (FreeGroup (Fin 2)) Γ.E := MulAction.compHom Γ.E Γ.edgeAction
  Action.FintypeCat.ofMulAction (FreeGroup (Fin 2)) (FintypeCat.of Γ.E)

variable {Γ} {Δ : BipartiteRibbonGraph.{u}}

/-- A map of edges which intertwines both rotations intertwines the whole action. -/
theorem edgeAction_semiconj {φ : Γ.E → Δ.E} (hB : Function.Semiconj φ Γ.rotB Δ.rotB)
    (hW : Function.Semiconj φ Γ.rotW Δ.rotW) (g : FreeGroup (Fin 2)) :
    Function.Semiconj φ (Γ.edgeAction g) (Δ.edgeAction g) := by
  induction g using FreeGroup.induction_on with
  | one => exact fun _ ↦ by simp
  | of i =>
    fin_cases i
    · simpa using hB
    · simpa using hW
  | inv_of i ih =>
    simp only [map_inv]
    exact ih.inverses_right (fun x ↦ by simp) (fun x ↦ by simp)
  | mul g h ihg ihh =>
    simp only [map_mul, Perm.coe_mul]
    exact ihg.comp_right ihh

/-- The equivariant map of edges induced by a morphism of ribbon graphs. -/
@[expose] def edgesMap (f : Γ ⟶ Δ) : Γ.edges ⟶ Δ.edges where
  hom := FintypeCat.homMk f.edge
  comm g := FintypeCat.hom_ext _ _ fun e ↦ by
    change f.edge (Γ.edgeAction g e) = Δ.edgeAction g (f.edge e)
    exact edgeAction_semiconj f.map_rotB f.map_rotW g e

@[simp]
theorem edgesMap_hom_apply (f : Γ ⟶ Δ) (e : Γ.E) : (edgesMap f).hom e = f.edge e :=
  (rfl)

variable (Γ Δ) in
/-- A map of edges which intertwines the action is a morphism of ribbon graphs: the vertices are
the cycles of the rotations, so the map of edges induces the maps of vertices. -/
def homOfEdgesMap (φ : Γ.edges ⟶ Δ.edges) : Γ ⟶ Δ :=
  have hφ (g : FreeGroup (Fin 2)) (e : Γ.E) :
      φ.hom (Γ.edgeAction g e) = Δ.edgeAction g (φ.hom e) :=
    congrArg (fun k ↦ k e) (congrArg (⇑) (φ.comm g))
  have hB : Function.Semiconj φ.hom Γ.rotB Δ.rotB := fun e ↦ by
    simpa using hφ (FreeGroup.of 0) e
  have hW : Function.Semiconj φ.hom Γ.rotW Δ.rotW := fun e ↦ by
    simpa using hφ (FreeGroup.of 1) e
  { edge := φ.hom
    black := fun b ↦ Δ.blackEnd (φ.hom (Function.surjInv Γ.blackEnd_surjective b))
    white := fun w ↦ Δ.whiteEnd (φ.hom (Function.surjInv Γ.whiteEnd_surjective w))
    map_blackEnd := fun e ↦ by
      refine (Δ.blackEnd_eq_blackEnd_iff.mpr ?_)
      have h := Γ.blackEnd_eq_blackEnd_iff.mp
        (Function.surjInv_eq Γ.blackEnd_surjective (Γ.blackEnd e)).symm
      exact h.map hB
    map_whiteEnd := fun e ↦ by
      refine (Δ.whiteEnd_eq_whiteEnd_iff.mpr ?_)
      have h := Γ.whiteEnd_eq_whiteEnd_iff.mp
        (Function.surjInv_eq Γ.whiteEnd_surjective (Γ.whiteEnd e)).symm
      exact h.map hW
    map_rotB := hB
    map_rotW := hW }

@[simp]
theorem homOfEdgesMap_edge (φ : Γ.edges ⟶ Δ.edges) : (homOfEdgesMap Γ Δ φ).edge = φ.hom :=
  (rfl)

/-- The **edge functor**: a ribbon graph goes to its edges, with the action of `FreeGroup (Fin 2)`
by the black and white rotations. -/
@[expose] def edgeFunctor :
    BipartiteRibbonGraph.{u} ⥤ Action FintypeCat.{u} (FreeGroup (Fin 2)) where
  obj := edges
  map := edgesMap
  map_id Γ := Action.Hom.ext (FintypeCat.hom_ext _ _ fun e ↦ Hom.id_edge_apply (Γ := Γ) e)
  map_comp f g := Action.Hom.ext (FintypeCat.hom_ext _ _ fun e ↦ Hom.comp_edge_apply g f e)

/-- The edge functor is fully faithful. -/
def edgeFunctorFullyFaithful : edgeFunctor.{u}.FullyFaithful where
  preimage {Γ Δ} φ := homOfEdgesMap Γ Δ φ
  map_preimage _ := Action.Hom.ext (FintypeCat.hom_ext _ _ fun _ ↦ rfl)
  preimage_map _ := hom_ext rfl

instance : edgeFunctor.{u}.Full := edgeFunctorFullyFaithful.full

instance : edgeFunctor.{u}.Faithful := edgeFunctorFullyFaithful.faithful

/-- The ribbon graph of a finite `FreeGroup (Fin 2)`-set: its edges are the points, and its black
and white vertices are the cycles of the generators `0` and `1`. -/
def ofAction (A : Action FintypeCat.{u} (FreeGroup (Fin 2))) : BipartiteRibbonGraph.{u} :=
  letI := Fintype.ofFinite A.V
  letI := Classical.decEq A.V
  ofPerms A.V (MulAction.toPerm (FreeGroup.of 0 : FreeGroup (Fin 2)))
    (MulAction.toPerm (FreeGroup.of 1 : FreeGroup (Fin 2)))

/-- The edges of the ribbon graph of a finite `FreeGroup (Fin 2)`-set are that set. -/
def edgesOfActionIso (A : Action FintypeCat.{u} (FreeGroup (Fin 2))) : (ofAction A).edges ≅ A :=
  Action.mkIso (FintypeCat.equivEquivIso (Equiv.refl A.V)) fun g ↦
    FintypeCat.hom_ext _ _ fun e ↦ by
      -- The action on the edges is the lift of the two generators, which is the given action.
      have h : (ofAction A).edgeAction = MulAction.toPermHom (FreeGroup (Fin 2)) A.V :=
        FreeGroup.ext_hom _ _ fun i ↦ by
          fin_cases i
          · exact (edgeAction_of_zero _).trans rfl
          · exact (edgeAction_of_one _).trans rfl
      exact congrArg (fun k : FreeGroup (Fin 2) →* Perm A.V ↦ k g e) h

instance : edgeFunctor.{u}.EssSurj where
  mem_essImage A := ⟨ofAction A, ⟨edgesOfActionIso A⟩⟩

instance : edgeFunctor.{u}.IsEquivalence where

/-- **Finite bipartite ribbon graphs are finite `FreeGroup (Fin 2)`-sets**: the edge functor is an
equivalence of categories. -/
def edgeEquivalence : BipartiteRibbonGraph.{u} ≌ Action FintypeCat.{u} (FreeGroup (Fin 2)) :=
  edgeFunctor.asEquivalence

end BipartiteRibbonGraph

end TauCeti
