/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.RibbonGraph.Category
public import Mathlib.CategoryTheory.Action.Concrete
public import Mathlib.GroupTheory.FreeGroup.Basic
import TauCeti.GroupTheory.Perm.PermCongr

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
* it is essentially surjective, since every finite `FreeGroup (Fin 2)`-set `A` is the edge set of
  the ribbon graph `TauCeti.BipartiteRibbonGraph.ofAction A` whose vertices are the cycles of the
  two generators (`TauCeti.BipartiteRibbonGraph.edgesOfActionIso`), the empty set included.

The requirement that every vertex is the end of an edge is what makes the functor full: a graph
with no edges and one black vertex has the same, empty, edge set as the empty graph but no
morphism to it.

The inverse functor `Action.toBipartiteRibbonGraphFunctor` takes equivariant maps to the
induced graph maps. The edge action of a connected graph is nonempty and transitive, and
conversely, by `isConnected_iff_nonempty_and_isPretransitive_edgeFunctor_obj`.

## Main definitions

* `TauCeti.BipartiteRibbonGraph.edgeAction`: the action of `FreeGroup (Fin 2)` on the edges.
* `TauCeti.BipartiteRibbonGraph.edgeFunctor`: the edge functor.
* `TauCeti.BipartiteRibbonGraph.ofAction`: the ribbon graph of a finite `FreeGroup (Fin 2)`-set,
  built by `TauCeti.BipartiteRibbonGraph.ofPerms` from the two generators.
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
-- Exposed so that the underlying finite set of `Γ.edges` is `Γ.E` by definition: the statements
-- of `edges_ρ_apply`, `edgesMap_hom_apply` and `homOfEdgesMap_edge` need it.
@[expose] def edges : Action FintypeCat.{u} (FreeGroup (Fin 2)) :=
  letI : MulAction (FreeGroup (Fin 2)) Γ.E := MulAction.compHom Γ.E Γ.edgeAction
  Action.FintypeCat.ofMulAction (FreeGroup (Fin 2)) (FintypeCat.of Γ.E)

/-- A group element acts on the edges through `edgeAction`. -/
@[simp]
theorem edges_ρ_apply (g : FreeGroup (Fin 2)) (e : Γ.edges.V) :
    ConcreteCategory.hom (Γ.edges.ρ g).asHom e = Γ.edgeAction g e :=
  (rfl)

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
-- Exposed, like `edgeFunctor` which is built from it, so that `edgeFunctor_map` holds by `rfl`.
@[expose] def edgesMap (f : Γ ⟶ Δ) : Γ.edges ⟶ Δ.edges where
  hom := FintypeCat.homMk f.edge
  comm g := FintypeCat.hom_ext _ _ fun e ↦ by
    simp only [ConcreteCategory.comp_apply, edges_ρ_apply]
    exact edgeAction_semiconj f.map_rotB f.map_rotW g e

@[simp]
theorem edgesMap_hom_apply (f : Γ ⟶ Δ) (e : Γ.E) : (edgesMap f).hom e = f.edge e :=
  (rfl)

variable (Γ Δ) in
/-- A map of edges which intertwines the action is a morphism of ribbon graphs: the vertices are
the cycles of the rotations, so the map of edges induces the maps of vertices. -/
def homOfEdgesMap (φ : Γ.edges ⟶ Δ.edges) : Γ ⟶ Δ :=
  have hφ (g : FreeGroup (Fin 2)) (e : Γ.E) :
      φ.hom (Γ.edgeAction g e) = Δ.edgeAction g (φ.hom e) := by
    -- `φ.comm g` evaluated at `e`: each side's action is `edgeAction` by `edges_ρ_apply`, which
    -- holds by definition. It cannot be rewritten here, since `Γ.E` and the carrier of `Γ.edges`
    -- agree only up to unfolding `edges`.
    exact ConcreteCategory.congr_hom (φ.comm g) e
  have hB : Function.Semiconj φ.hom Γ.rotB Δ.rotB := fun e ↦ by
    simpa using hφ (FreeGroup.of 0) e
  have hW : Function.Semiconj φ.hom Γ.rotW Δ.rotW := fun e ↦ by
    simpa using hφ (FreeGroup.of 1) e
  Hom.ofEdge φ.hom hB hW

@[simp]
theorem homOfEdgesMap_edge (φ : Γ.edges ⟶ Δ.edges) : (homOfEdgesMap Γ Δ φ).edge = φ.hom :=
  Hom.ofEdge_edge _ _ _

/-- The **edge functor**: a ribbon graph goes to its edges, with the action of `FreeGroup (Fin 2)`
by the black and white rotations. -/
-- Exposed so that the values of the functor are `edges` and `edgesMap` by definition: the
-- statements of `edgeFunctor_obj` and `edgeFunctor_map` need it.
@[expose] def edgeFunctor :
    BipartiteRibbonGraph.{u} ⥤ Action FintypeCat.{u} (FreeGroup (Fin 2)) where
  obj := edges
  map := edgesMap
  map_id Γ := Action.Hom.ext (FintypeCat.hom_ext _ _ fun e ↦ Hom.id_edge_apply (Γ := Γ) e)
  map_comp f g := Action.Hom.ext (FintypeCat.hom_ext _ _ fun e ↦ Hom.comp_edge_apply g f e)

@[simp] theorem edgeFunctor_obj (Γ : BipartiteRibbonGraph.{u}) : edgeFunctor.obj Γ = Γ.edges :=
  (rfl)

@[simp] theorem edgeFunctor_map (f : Γ ⟶ Δ) : edgeFunctor.map f = edgesMap f :=
  (rfl)

/-- The edge functor is fully faithful. -/
def edgeFunctorFullyFaithful : edgeFunctor.{u}.FullyFaithful where
  preimage {Γ Δ} φ := homOfEdgesMap Γ Δ φ
  map_preimage φ := Action.Hom.ext (FintypeCat.hom_ext _ _ fun x ↦
    congrFun (homOfEdgesMap_edge φ) x)
  preimage_map f := hom_ext ((homOfEdgesMap_edge (edgesMap f)).trans rfl)

instance : edgeFunctor.{u}.Full := edgeFunctorFullyFaithful.full

instance : edgeFunctor.{u}.Faithful := edgeFunctorFullyFaithful.faithful

/-- The ribbon graph of a finite `FreeGroup (Fin 2)`-set: its edges are the points, and its black
and white vertices are the cycles of the generators `0` and `1`. -/
-- Exposed so that the edges of `ofAction A` are the points of `A` by definition: the statements
-- of `edgeAction_ofAction` and `edgesOfActionIso_hom_hom_apply` need it.
@[expose] def ofAction (A : Action FintypeCat.{u} (FreeGroup (Fin 2))) :
    BipartiteRibbonGraph.{u} :=
  letI := Fintype.ofFinite A.V
  letI := Classical.decEq A.V
  ofPerms A.V (MulAction.toPerm (FreeGroup.of 0 : FreeGroup (Fin 2)))
    (MulAction.toPerm (FreeGroup.of 1 : FreeGroup (Fin 2)))

variable (A : Action FintypeCat.{u} (FreeGroup (Fin 2)))

/-- The edges of the ribbon graph of a finite `FreeGroup (Fin 2)`-set are its points. -/
theorem ofAction_E : (ofAction A).E = A.V :=
  (rfl)

/-- The black rotation of the ribbon graph of a finite `FreeGroup (Fin 2)`-set is the action of
the generator `0`. -/
@[simp] theorem rotB_ofAction :
    (ofAction A).rotB = (MulAction.toPerm (FreeGroup.of 0 : FreeGroup (Fin 2)) : Perm A.V) :=
  (rfl)

/-- The white rotation of the ribbon graph of a finite `FreeGroup (Fin 2)`-set is the action of
the generator `1`. -/
@[simp] theorem rotW_ofAction :
    (ofAction A).rotW = (MulAction.toPerm (FreeGroup.of 1 : FreeGroup (Fin 2)) : Perm A.V) :=
  (rfl)

/-- The action on the edges of the ribbon graph of a finite `FreeGroup (Fin 2)`-set is the given
action. -/
@[simp] theorem edgeAction_ofAction :
    (ofAction A).edgeAction = MulAction.toPermHom (FreeGroup (Fin 2)) A.V :=
  FreeGroup.ext_hom _ _ fun i ↦ by
    fin_cases i
    · exact (edgeAction_of_zero _).trans ((rotB_ofAction A).trans
        (MulAction.toPermHom_apply _ _ _).symm)
    · exact (edgeAction_of_one _).trans ((rotW_ofAction A).trans
        (MulAction.toPermHom_apply _ _ _).symm)

/-- The black vertices of the reconstructed graph are the cycles of generator `0`. -/
def _root_.Action.bipartiteRibbonGraphBlackEquiv
    (A : Action FintypeCat.{u} (FreeGroup (Fin 2))) :
    (ofAction A).B ≃ Quotient (Perm.SameCycle.setoid
      (MulAction.toPermHom (FreeGroup (Fin 2)) A.V (FreeGroup.of 0))) :=
  Equiv.refl _

/-- The white vertices of the reconstructed graph are the cycles of generator `1`. -/
def _root_.Action.bipartiteRibbonGraphWhiteEquiv
    (A : Action FintypeCat.{u} (FreeGroup (Fin 2))) :
    (ofAction A).W ≃ Quotient (Perm.SameCycle.setoid
      (MulAction.toPermHom (FreeGroup (Fin 2)) A.V (FreeGroup.of 1))) :=
  Equiv.refl _

/-- The black endpoint is the cycle of the edge under generator `0`. -/
@[simp] theorem _root_.Action.bipartiteRibbonGraphBlackEquiv_blackEnd
    (A : Action FintypeCat.{u} (FreeGroup (Fin 2))) (x : A.V) :
    A.bipartiteRibbonGraphBlackEquiv ((ofAction A).blackEnd x) = Quotient.mk _ x := (rfl)

/-- The white endpoint is the cycle of the edge under generator `1`. -/
@[simp] theorem _root_.Action.bipartiteRibbonGraphWhiteEquiv_whiteEnd
    (A : Action FintypeCat.{u} (FreeGroup (Fin 2))) (x : A.V) :
    A.bipartiteRibbonGraphWhiteEquiv ((ofAction A).whiteEnd x) = Quotient.mk _ x := (rfl)

/-- The edges of the ribbon graph of a finite `FreeGroup (Fin 2)`-set are that set. -/
def edgesOfActionIso : edgeFunctor.obj (ofAction A) ≅ A :=
  -- The forward functor has object projection `edges`.
  have e : (ofAction A).edges ≅ A :=
    Action.mkIso (FintypeCat.equivEquivIso (Equiv.refl A.V)) fun g ↦
      FintypeCat.hom_ext _ _ fun e ↦ by
        simp only [ConcreteCategory.comp_apply, edges_ρ_apply, edgeAction_ofAction]
        -- The comparison map is the identity and both actions are `g • e` definitionally.
        rfl
  e

/-- The isomorphism `edgesOfActionIso` is the identity on points. -/
@[simp] theorem edgesOfActionIso_hom_hom_apply (e : A.V) :
    ConcreteCategory.hom (edgesOfActionIso A).hom.hom e = e :=
  (rfl)

instance : edgeFunctor.{u}.EssSurj where
  mem_essImage A := ⟨ofAction A, ⟨edgesOfActionIso A⟩⟩

instance : edgeFunctor.{u}.IsEquivalence where

/-- The inverse comparison is the identity on points. -/
@[simp] theorem edgesOfActionIso_inv_hom_apply (e : A.V) :
    (edgesOfActionIso A).inv.hom e = e := (rfl)

/-- Reconstruct the ribbon graph from the cycles of the two generators. An equivariant map of
finite actions induces the corresponding graph morphism on edges. -/
def _root_.Action.toBipartiteRibbonGraphFunctor :
    Action FintypeCat.{u} (FreeGroup (Fin 2)) ⥤ BipartiteRibbonGraph.{u} where
  obj := ofAction
  map {A B} f := edgeFunctorFullyFaithful.preimage
    ((edgesOfActionIso A).hom ≫ f ≫ (edgesOfActionIso B).inv)
  map_id A := by
    rw [Category.id_comp, Iso.hom_inv_id, Functor.FullyFaithful.preimage_id]
  map_comp f g := by
    rw [← Functor.FullyFaithful.preimage_comp]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- The reconstruction functor takes a finite action to the graph of its two generators. -/
@[simp] theorem _root_.Action.toBipartiteRibbonGraphFunctor_obj
    (A : Action FintypeCat.{u} (FreeGroup (Fin 2))) :
    Action.toBipartiteRibbonGraphFunctor.obj A = ofAction A := (rfl)

/-- The edges of the functor's image are the points of the action. -/
def _root_.Action.toBipartiteRibbonGraphFunctorEdgeEquiv
    (A : Action FintypeCat.{u} (FreeGroup (Fin 2))) :
    (Action.toBipartiteRibbonGraphFunctor.obj A).E ≃ A.V :=
  Equiv.cast (congrArg BipartiteRibbonGraph.E A.toBipartiteRibbonGraphFunctor_obj |>.trans
    (ofAction_E A))

/-- On edges the reconstruction functor acts by the underlying map of the action morphism. -/
@[simp] theorem _root_.Action.toBipartiteRibbonGraphFunctor_map_edge_apply
    {A B : Action FintypeCat.{u} (FreeGroup (Fin 2))} (f : A ⟶ B)
    (x : (Action.toBipartiteRibbonGraphFunctor.obj A).E) :
    B.toBipartiteRibbonGraphFunctorEdgeEquiv ((Action.toBipartiteRibbonGraphFunctor.map f).edge x) =
      f.hom (A.toBipartiteRibbonGraphFunctorEdgeEquiv x) := by
  -- The object projection identifies the edges of the reconstructed graph with the carrier.
  let y : A.V := x
  let k := (edgesOfActionIso A).hom ≫ f ≫ (edgesOfActionIso B).inv
  -- Both comparison isomorphisms are the identity on carriers.
  have h : k.hom y = f.hom y := rfl
  exact (congrFun (homOfEdgesMap_edge k) y).trans h

/-- Finite bipartite ribbon graphs are equivalent to finite `FreeGroup (Fin 2)`-sets,
with inverse given by the cycle-quotient reconstruction functor. -/
def edgeEquivalence : BipartiteRibbonGraph.{u} ≌ Action FintypeCat.{u} (FreeGroup (Fin 2)) where
  functor := edgeFunctor
  inverse := Action.toBipartiteRibbonGraphFunctor
  unitIso := NatIso.ofComponents (fun Γ ↦ edgeFunctorFullyFaithful.preimageIso
    (edgesOfActionIso (edgeFunctor.obj Γ)).symm) (by
    intro Γ Δ f
    apply edgeFunctorFullyFaithful.map_injective
    dsimp only [Functor.id_map, Functor.comp_map, Action.toBipartiteRibbonGraphFunctor]
    simp only [Functor.map_comp, Functor.FullyFaithful.preimageIso_hom, Iso.symm_hom,
      Functor.FullyFaithful.map_preimage, Iso.inv_hom_id_assoc])
  counitIso := NatIso.ofComponents (fun A ↦ edgesOfActionIso A) (by
    intro A B f
    dsimp only [Functor.comp_map, Functor.id_map, Action.toBipartiteRibbonGraphFunctor]
    simp only [Functor.FullyFaithful.map_preimage, Category.assoc, Iso.inv_hom_id,
      Category.comp_id])
  functor_unitIso_comp Γ := by
    dsimp only [NatIso.ofComponents, Functor.id_obj, Functor.comp_obj]
    let e := edgesOfActionIso (edgeFunctor.obj Γ)
    have h : edgeFunctor.map (edgeFunctorFullyFaithful.preimageIso e.symm).hom ≫ e.hom = 𝟙 _ := by
      rw [Functor.FullyFaithful.preimageIso_hom, Functor.FullyFaithful.map_preimage,
        Iso.symm_hom, Iso.inv_hom_id]
    exact h

@[simp] theorem edgeEquivalence_functor : edgeEquivalence.{u}.functor = edgeFunctor := (rfl)

/-- The inverse of the edge equivalence is the cycle-quotient reconstruction functor. -/
@[simp] theorem edgeEquivalence_inverse :
    edgeEquivalence.{u}.inverse = Action.toBipartiteRibbonGraphFunctor := (rfl)

/-- The counit identifies the edge action of the reconstructed graph with the original action. -/
@[simp] theorem _root_.Action.edgeEquivalence_counitIso_app
    (A : Action FintypeCat.{u} (FreeGroup (Fin 2))) :
    edgeEquivalence.counitIso.app A = eqToIso (by
      rw [Functor.comp_obj, edgeEquivalence_functor, edgeEquivalence_inverse,
        Action.toBipartiteRibbonGraphFunctor_obj]) ≪≫ edgesOfActionIso A := (rfl)

/-- The unit lifts the inverse of the action comparison to an isomorphism of graphs. -/
@[simp] theorem edgeEquivalence_unitIso_app (Γ : BipartiteRibbonGraph.{u}) :
    edgeEquivalence.unitIso.app Γ =
      edgeFunctorFullyFaithful.preimageIso (edgesOfActionIso (edgeFunctor.obj Γ)).symm ≪≫
        eqToIso (by
          rw [Functor.comp_obj, edgeEquivalence_functor, edgeEquivalence_inverse,
            Action.toBipartiteRibbonGraphFunctor_obj]) :=
  (CategoryTheory.Iso.trans_refl
    (edgeFunctorFullyFaithful.preimageIso (edgesOfActionIso (edgeFunctor.obj Γ)).symm)).symm

/-- A ribbon graph is connected exactly when its edge action is nonempty and transitive. -/
theorem isConnected_iff_nonempty_and_isPretransitive_edgeFunctor_obj
    {Γ : BipartiteRibbonGraph.{u}} : Γ.IsConnected ↔ Nonempty (edgeFunctor.obj Γ).V ∧
      MulAction.IsPretransitive (FreeGroup (Fin 2)) (edgeFunctor.obj Γ).V := by
  have hρ : MulAction.toPermHom (FreeGroup (Fin 2)) Γ.edges.V = Γ.edgeAction := by
    refine MonoidHom.ext fun g ↦ Equiv.ext fun x ↦ ?_
    rw [MulAction.toPermHom_apply, MulAction.toPerm_apply, ← Action.ρ_apply_eq_smul]
    exact edges_ρ_apply Γ g x
  have hr : Γ.edgeAction.range = Γ.rotationGroup := by
    rw [edgeAction, FreeGroup.range_lift_eq_closure, Matrix.range_cons_cons_empty,
      Γ.closure_pair_eq_rotationGroup]
  have h := MulAction.isPretransitive_range_toPermHom_iff
    (FreeGroup (Fin 2)) Γ.edges.V
  rw [hρ] at h
  have h' : MulAction.IsPretransitive Γ.edgeAction.range Γ.E ↔
      MulAction.IsPretransitive (FreeGroup (Fin 2)) Γ.edges.V := h
  rw [hr] at h'
  exact Γ.isConnected_def.trans (and_congr_right fun _ ↦ h')

end BipartiteRibbonGraph

end TauCeti
