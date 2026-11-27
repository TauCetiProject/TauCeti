/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Action.Concrete
public import Mathlib.GroupTheory.FreeGroup.Basic
public import TauCeti.Combinatorics.RibbonGraph.Category
import TauCeti.GroupTheory.Perm.PermCongr

/-!
# Bipartite ribbon graphs as finite group actions

The category of finite bipartite ribbon graphs is equivalent to
`Action FintypeCat (FreeGroup (Fin 2))` by `TauCeti.BipartiteRibbonGraph.edgeEquivalence`.
Its forward functor `TauCeti.BipartiteRibbonGraph.edgeFunctor` acts on the edges, with free
generators `0` and `1` acting by the black and white rotations. This classifies bipartite
ribbon graphs, including dessins d'enfants, by pairs of permutations. The graph is connected
exactly when the edge action is nonempty and transitive, as stated in
`TauCeti.BipartiteRibbonGraph.isConnected_iff_nonempty_and_isPretransitive_edgeFunctor_obj`.

## References

* S. K. Lando and A. K. Zvonkin, *Graphs on Surfaces and Their Applications*, Encyclopaedia of
  Mathematical Sciences 141, Springer, 2004, §1.3 and §1.5.
-/

public section

open CategoryTheory

namespace TauCeti.BipartiteRibbonGraph

universe u

private def edgeRepresentation (Γ : BipartiteRibbonGraph.{u}) :
    FreeGroup (Fin 2) →* Equiv.Perm Γ.E := FreeGroup.lift ![Γ.rotB, Γ.rotW]

private abbrev edgeAction (Γ : BipartiteRibbonGraph.{u}) :
    Action FintypeCat.{u} (FreeGroup (Fin 2)) :=
  letI := MulAction.compHom Γ.E (edgeRepresentation Γ)
  Action.FintypeCat.ofMulAction _ (FintypeCat.of Γ.E)

/-- The representation evaluates a free generator by the corresponding vertex rotation. -/
private theorem edgeRepresentation_of_apply (Γ : BipartiteRibbonGraph.{u}) (i : Fin 2) (x : Γ.E) :
    edgeRepresentation Γ (FreeGroup.of i) x = (![Γ.rotB, Γ.rotW] i) x := by
  rw [edgeRepresentation, FreeGroup.lift_apply_of]

private theorem edgeRepresentation_comm {Γ Δ : BipartiteRibbonGraph.{u}} (f : Γ.Hom Δ)
    (g : FreeGroup (Fin 2)) (x : Γ.E) :
    f.edge (edgeRepresentation Γ g x) = edgeRepresentation Δ g (f.edge x) := by
  induction g using FreeGroup.induction_on generalizing x with
  | one => simp
  | of i =>
    simp only [edgeRepresentation_of_apply]
    revert i
    simp only [Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    exact ⟨f.map_rotB x, f.map_rotW x⟩
  | inv_of i ih =>
    simpa only [map_inv, Equiv.Perm.inv_def] using
      Function.Semiconj.inverses_right ih (Equiv.apply_symm_apply _) (Equiv.symm_apply_apply _) x
  | mul g h hg hh => simp only [map_mul, Equiv.Perm.mul_apply, hg, hh]

/-- The edge functor sends the two free generators to the black and white rotations. -/
def edgeFunctor :
    BipartiteRibbonGraph.{u} ⥤ Action FintypeCat.{u} (FreeGroup (Fin 2)) where
  obj := edgeAction
  map {Γ Δ} f :=
    ⟨FintypeCat.homMk (X := FintypeCat.of Γ.E) (Y := FintypeCat.of Δ.E) f.edge,
      fun g ↦ FintypeCat.hom_ext _ _ (edgeRepresentation_comm f g)⟩
  map_id _ := Action.hom_ext _ _ (FintypeCat.hom_ext _ _ id_edge_apply)
  map_comp f g := Action.hom_ext _ _ (FintypeCat.hom_ext _ _ (comp_edge_apply f g))

private theorem edgeFunctor_obj_ρ_apply (Γ : BipartiteRibbonGraph.{u})
    (g : FreeGroup (Fin 2)) (x : Γ.E) :
    ((edgeFunctor.obj Γ).ρ g).asHom x = edgeRepresentation Γ g x := by
  let := MulAction.compHom Γ.E (edgeRepresentation Γ)
  exact (Action.FintypeCat.ofMulAction_apply (H := FintypeCat.of Γ.E) g x).trans
    ((MulAction.compHom_smul_def (edgeRepresentation Γ) g x).trans (Equiv.Perm.smul_def _ _))

/-- Identify the finite carrier of the edge action with the graph's edge type for transport. -/
@[simp] theorem edgeFunctor_obj_V (Γ : BipartiteRibbonGraph.{u}) :
    (edgeFunctor.obj Γ).V = FintypeCat.of Γ.E := (rfl)

/-- Identify the underlying type of the edge action with the edge type of the graph. -/
def edgeEquiv (Γ : BipartiteRibbonGraph.{u}) : (edgeFunctor.obj Γ).V ≃ Γ.E :=
  -- The carrier is definitionally `Γ.E`, as `edgeFunctor_obj_V` records.
  Equiv.refl _

/-- The generators act on the graph's edges by the black and white rotations, respectively. -/
@[simp] theorem edgeEquiv_edgeFunctor_obj_ρ_of_apply (Γ : BipartiteRibbonGraph.{u})
    (i : Fin 2) (x : Γ.E) :
    Γ.edgeEquiv (((edgeFunctor.obj Γ).ρ (FreeGroup.of i)).asHom (Γ.edgeEquiv.symm x)) =
      (![Γ.rotB, Γ.rotW] i) x := by
  exact (edgeFunctor_obj_ρ_apply Γ _ x).trans (edgeRepresentation_of_apply Γ i x)

/-- The edge functor acts on morphisms by their edge maps. -/
@[simp] theorem edgeEquiv_edgeFunctor_map_hom_apply {Γ Δ : BipartiteRibbonGraph.{u}}
    (f : Γ ⟶ Δ) (x : Γ.E) :
    Δ.edgeEquiv ((edgeFunctor.map f).hom (Γ.edgeEquiv.symm x)) = f.edge x := by
  exact FintypeCat.homMk_apply (X := FintypeCat.of Γ.E) (Y := FintypeCat.of Δ.E) f.edge x

/-- The edge functor is fully faithful. An equivariant edge map extends uniquely to a graph
morphism, with vertex maps induced through the endpoint maps. -/
noncomputable def fullyFaithfulEdgeFunctor : edgeFunctor.{u}.FullyFaithful where
  preimage {Γ Δ} f := by
    -- The carrier identifications in `edgeEquiv` are reflexive.
    let e : Γ.E → Δ.E := f.hom
    have h (i : Fin 2) (x : Γ.E) : e ((![Γ.rotB, Γ.rotW] i) x) =
        (![Δ.rotB, Δ.rotW] i) (e x) := by
      have hc : e (((edgeFunctor.obj Γ).ρ (FreeGroup.of i)).asHom x) =
          ((edgeFunctor.obj Δ).ρ (FreeGroup.of i)).asHom (e x) := by
        have hcomp := FintypeCat.comp_apply ((edgeFunctor.obj Γ).ρ (FreeGroup.of i)).asHom f.hom x
        exact hcomp.symm.trans
          ((ConcreteCategory.congr_hom (f.comm (FreeGroup.of i)) x).trans
            (FintypeCat.comp_apply f.hom _ x))
      rw [edgeFunctor_obj_ρ_apply Γ _ x, edgeFunctor_obj_ρ_apply Δ _ (e x),
        edgeRepresentation_of_apply, edgeRepresentation_of_apply] at hc
      exact hc
    exact Hom.ofEdge e (fun x ↦ by simpa only [Matrix.cons_val_zero] using h 0 x)
      (fun x ↦ by simpa only [Matrix.cons_val_one, Matrix.cons_val_zero] using h 1 x)
  map_preimage {Γ Δ} f := by
    refine Action.hom_ext _ _ (FintypeCat.hom_ext _ _ fun x ↦ ?_)
    exact congrFun (Hom.ofEdge_edge (Γ := Γ) (Δ := Δ) _ _ _) x
  preimage_map {Γ Δ} f := by
    refine hom_ext (funext fun x ↦ ?_)
    exact (congrFun (Hom.ofEdge_edge (Γ := Γ) (Δ := Δ) _ _ _) x).trans
      (edgeEquiv_edgeFunctor_map_hom_apply f x)

/-- The preimage of an action morphism has the same underlying edge map. -/
@[simp] theorem fullyFaithfulEdgeFunctor_preimage_edge_apply {Γ Δ : BipartiteRibbonGraph.{u}}
    (f : edgeFunctor.obj Γ ⟶ edgeFunctor.obj Δ) (x : Γ.E) :
    (fullyFaithfulEdgeFunctor.preimage f).edge x = Δ.edgeEquiv (f.hom (Γ.edgeEquiv.symm x)) := by
  -- The preimage is built with `Hom.ofEdge` and the carrier identifications are reflexive.
  exact congrFun (Hom.ofEdge_edge (Γ := Γ) (Δ := Δ) _ _ _) x

instance : edgeFunctor.{u}.IsEquivalence where
  faithful := fullyFaithfulEdgeFunctor.faithful
  full := fullyFaithfulEdgeFunctor.full
  essSurj.mem_essImage A := by
    classical
    let := FintypeCat.fintype (X := A.V)
    let ρ := MulAction.toPermHom (FreeGroup (Fin 2)) A.V
    let Γ := (ρ (FreeGroup.of 0)).bipartiteRibbonGraph (ρ (FreeGroup.of 1))
    have hperm : edgeRepresentation Γ = ρ := by
      apply FreeGroup.ext_hom
      intro i
      rw [edgeRepresentation, FreeGroup.lift_apply_of]
      revert i
      simp only [Fin.forall_fin_two, Γ,
        Equiv.Perm.rotB_bipartiteRibbonGraph, Equiv.Perm.rotW_bipartiteRibbonGraph]
      exact ⟨Matrix.cons_val_zero _ _, (Matrix.cons_val_one _ _).trans (Matrix.cons_val_zero _ _)⟩
    -- Rebundling `A.V` with its own fintype instance gives the same finite carrier.
    have hρ (g : FreeGroup (Fin 2)) :
        ((edgeFunctor.obj Γ).ρ g).asHom = (A.ρ g).asHom := by
      refine FintypeCat.hom_ext _ _ fun x ↦ ?_
      have happly : ρ g x = (A.ρ g).asHom x := by
        dsimp only [ρ]
        rw [MulAction.toPermHom_apply]
        exact (MulAction.toPerm_apply (β := A.V) g x).trans (Action.ρ_apply_eq_smul A g x).symm
      have heq := congrArg (fun p : FreeGroup (Fin 2) →* Equiv.Perm A.V ↦ p g x) hperm
      exact (edgeFunctor_obj_ρ_apply Γ g x).trans (heq.trans happly)
    exact ⟨Γ, ⟨Action.mkIso (CategoryTheory.Iso.refl A.V) (fun g ↦ by
      exact (Category.comp_id _).trans ((hρ g).trans (Category.id_comp _).symm))⟩⟩

/-- Bipartite ribbon graphs are equivalent to finite actions of the free group on two generators. -/
noncomputable def edgeEquivalence :
    BipartiteRibbonGraph.{u} ≌ Action FintypeCat.{u} (FreeGroup (Fin 2)) :=
  edgeFunctor.asEquivalence

/-- The forward functor of the equivalence is the edge functor. -/
@[simp] theorem edgeEquivalence_functor : edgeEquivalence.{u}.functor = edgeFunctor := (rfl)

/-- A graph is connected exactly when its edge action is nonempty and transitive. -/
theorem isConnected_iff_nonempty_and_isPretransitive_edgeFunctor_obj
    {Γ : BipartiteRibbonGraph.{u}} :
    Γ.IsConnected ↔ Nonempty (edgeFunctor.obj Γ).V ∧
      MulAction.IsPretransitive (FreeGroup (Fin 2)) (edgeFunctor.obj Γ).V := by
  have hρ : MulAction.toPermHom (FreeGroup (Fin 2)) (edgeFunctor.obj Γ).V =
      edgeRepresentation Γ := by
    refine MonoidHom.ext fun g ↦ Equiv.ext fun x ↦ ?_
    rw [MulAction.toPermHom_apply]
    exact (MulAction.toPerm_apply g x).trans
      ((Action.ρ_apply_eq_smul (edgeFunctor.obj Γ) g x).symm.trans (edgeFunctor_obj_ρ_apply Γ g x))
  have hr : (edgeRepresentation Γ).range = Γ.rotationGroup := by
    rw [edgeRepresentation, FreeGroup.range_lift_eq_closure, Matrix.range_cons_cons_empty,
      Γ.closure_pair_eq_rotationGroup]
  have h : MulAction.IsPretransitive (edgeRepresentation Γ).range Γ.E ↔
      MulAction.IsPretransitive (FreeGroup (Fin 2)) (edgeFunctor.obj Γ).V :=
    hρ ▸ MulAction.isPretransitive_range_toPermHom_iff (FreeGroup (Fin 2)) (edgeFunctor.obj Γ).V
  rw [hr] at h
  exact Γ.isConnected_def.trans (and_congr_right fun _ ↦ h)

end TauCeti.BipartiteRibbonGraph
