/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Action.Concrete
public import Mathlib.GroupTheory.FreeGroup.Basic
public import TauCeti.Combinatorics.RibbonGraph.Basic
import TauCeti.GroupTheory.Perm.PermCongr

/-!
# Bipartite ribbon graphs as finite group actions

`TauCeti.BipartiteRibbonGraph.edgeFunctor` uses `FreeGroup.lift` on the two rotations.
`TauCeti.BipartiteRibbonGraph.edgeEquivalence` recovers the graph, including the empty graph,
by applying `Equiv.Perm.bipartiteRibbonGraph` to the generator permutations.

## References

* S. K. Lando and A. K. Zvonkin, *Graphs on Surfaces and Their Applications*, Encyclopaedia of
  Mathematical Sciences 141, Springer, 2004, §1.3 and §1.5.
-/

public section

open CategoryTheory

namespace TauCeti.BipartiteRibbonGraph

universe u

/-- The category of bipartite ribbon graphs and maps preserving incidences and rotations. -/
instance : Category BipartiteRibbonGraph.{u} where
  Hom := Hom
  id := Hom.id
  comp f g := g.comp f
  id_comp := Hom.comp_id
  comp_id := Hom.id_comp
  assoc f g h := Hom.comp_assoc h g f

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
    fin_cases i
    · exact f.map_rotB x
    · exact f.map_rotW x
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
  map_id _ := Action.hom_ext _ _ (FintypeCat.hom_ext _ _ Hom.id_edge_apply)
  map_comp f g := Action.hom_ext _ _ (FintypeCat.hom_ext _ _ (Hom.comp_edge_apply g f))

/-- Identify the finite carrier of the edge action with the graph's edge type for transport. -/
@[simp] theorem edgeFunctor_obj_V (Γ : BipartiteRibbonGraph.{u}) :
    (edgeFunctor.obj Γ).V = FintypeCat.of Γ.E := (rfl)

/-- Identify the underlying type of the edge action with the edge type of the graph. -/
def edgeEquiv (Γ : BipartiteRibbonGraph.{u}) : (edgeFunctor.obj Γ).V ≃ Γ.E :=
  Equiv.cast (congrArg (fun X : FintypeCat.{u} ↦ (X : Type u)) (edgeFunctor_obj_V Γ))

/-- The generators act on the graph's edges by the black and white rotations, respectively. -/
@[simp] theorem edgeFunctor_obj_ρ_of_apply (Γ : BipartiteRibbonGraph.{u}) (i : Fin 2) (x : Γ.E) :
    Γ.edgeEquiv (((edgeFunctor.obj Γ).ρ (FreeGroup.of i)).asHom (Γ.edgeEquiv.symm x)) =
      (![Γ.rotB, Γ.rotW] i) x :=
  edgeRepresentation_of_apply Γ i x

/-- The edge functor acts on morphisms by their edge maps. -/
@[simp] theorem edgeEquiv_map_hom_apply {Γ Δ : BipartiteRibbonGraph.{u}} (f : Γ.Hom Δ) (x : Γ.E) :
    Δ.edgeEquiv ((edgeFunctor.map f).hom (Γ.edgeEquiv.symm x)) = f.edge x := (rfl)

/-- The edge functor is fully faithful since each vertex is the endpoint of an edge. -/
noncomputable def fullyFaithfulEdgeFunctor : edgeFunctor.{u}.FullyFaithful where
  preimage {Γ Δ} f := by
    let e : Γ.E → Δ.E := f.hom
    have h (i : Fin 2) (x : Γ.E) : e ((![Γ.rotB, Γ.rotW] i) x) =
        (![Δ.rotB, Δ.rotW] i) (e x) := by
      have hi : e (edgeRepresentation Γ (FreeGroup.of i) x) =
          edgeRepresentation Δ (FreeGroup.of i) (e x) :=
        ConcreteCategory.congr_hom (f.comm (FreeGroup.of i)) x
      simpa only [edgeRepresentation_of_apply] using hi
    have hB : Function.Semiconj e Γ.rotB Δ.rotB := h 0
    have hW : Function.Semiconj e Γ.rotW Δ.rotW := h 1
    refine ⟨e, Δ.blackEnd ∘ e ∘ Function.surjInv Γ.blackEnd_surjective,
      Δ.whiteEnd ∘ e ∘ Function.surjInv Γ.whiteEnd_surjective, ?_, ?_, hB, hW⟩
    · intro x
      apply Δ.blackEnd_eq_blackEnd_iff.mpr
      apply Equiv.Perm.SameCycle.map _ hB
      exact Γ.blackEnd_eq_blackEnd_iff.mp
        ((Function.rightInverse_surjInv Γ.blackEnd_surjective (Γ.blackEnd x)).symm)
    · intro x
      apply Δ.whiteEnd_eq_whiteEnd_iff.mpr
      apply Equiv.Perm.SameCycle.map _ hW
      exact Γ.whiteEnd_eq_whiteEnd_iff.mp
        ((Function.rightInverse_surjInv Γ.whiteEnd_surjective (Γ.whiteEnd x)).symm)
  map_preimage _ := Action.hom_ext _ _ (FintypeCat.hom_ext _ _ fun _ ↦ rfl)
  preimage_map _ := Hom.ext (rfl)

/-- The preimage of an action morphism has the same underlying edge map. -/
@[simp] theorem fullyFaithfulEdgeFunctor_preimage_edge_apply {Γ Δ : BipartiteRibbonGraph.{u}}
    (f : edgeFunctor.obj Γ ⟶ edgeFunctor.obj Δ) (x : Γ.E) :
    (fullyFaithfulEdgeFunctor.preimage f).edge x = Δ.edgeEquiv (f.hom (Γ.edgeEquiv.symm x)) := (rfl)

instance : edgeFunctor.{u}.IsEquivalence where
  faithful := fullyFaithfulEdgeFunctor.faithful
  full := fullyFaithfulEdgeFunctor.full
  essSurj := Functor.essSurj_of_surj fun A ↦ by
    classical
    let := FintypeCat.fintype (X := A.V)
    let ρ := MulAction.toPermHom (FreeGroup (Fin 2)) A.V
    let Γ := (ρ (FreeGroup.of 0)).bipartiteRibbonGraph (ρ (FreeGroup.of 1))
    have hρ : (edgeAction Γ).ρ = A.ρ := by
      apply FreeGroup.ext_hom
      intro i
      refine End.ext (FintypeCat.hom_ext _ _ fun x ↦ ?_)
      fin_cases i
      · exact edgeRepresentation_of_apply Γ 0 x
      · exact edgeRepresentation_of_apply Γ 1 x
    refine ⟨Γ, ?_⟩
    cases A
    exact congrArg (Action.mk _) hρ

/-- Bipartite ribbon graphs are equivalent to finite actions of the free group on two generators. -/
noncomputable def edgeEquivalence :
    BipartiteRibbonGraph.{u} ≌ Action FintypeCat.{u} (FreeGroup (Fin 2)) :=
  edgeFunctor.asEquivalence

/-- The forward functor of the equivalence is the edge functor. -/
@[simp] theorem edgeEquivalence_functor : edgeEquivalence.{u}.functor = edgeFunctor := (rfl)

/-- A graph is connected exactly when its edge action is nonempty and transitive. -/
theorem isConnected_iff_edgeFunctor_obj {Γ : BipartiteRibbonGraph.{u}} :
    Γ.IsConnected ↔ Nonempty (edgeFunctor.obj Γ).V ∧
      MulAction.IsPretransitive (FreeGroup (Fin 2)) (edgeFunctor.obj Γ).V := by
  have hρ : MulAction.toPermHom (FreeGroup (Fin 2)) (edgeAction Γ).V = edgeRepresentation Γ :=
    MonoidHom.ext fun _ ↦ Equiv.ext fun _ ↦ rfl
  have hr : (edgeRepresentation Γ).range = Γ.rotationGroup := by
    rw [edgeRepresentation, FreeGroup.range_lift_eq_closure, Matrix.range_cons_cons_empty,
      Γ.closure_pair_eq_rotationGroup]
  have h : MulAction.IsPretransitive (edgeRepresentation Γ).range Γ.E ↔
      MulAction.IsPretransitive (FreeGroup (Fin 2)) (edgeAction Γ).V :=
    hρ ▸ MulAction.isPretransitive_range_toPermHom_iff (FreeGroup (Fin 2)) (edgeAction Γ).V
  rw [hr] at h
  exact Γ.isConnected_def.trans (and_congr_right fun _ ↦ h)

end TauCeti.BipartiteRibbonGraph
