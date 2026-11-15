/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.RingTheory.FilteredAlgebra.Action.Basic
public import TauCeti.RingTheory.FilteredAlgebra.Algebra
public import Mathlib.Algebra.Ring.Action.End

/-!
# Compatible actions on filtered algebra completions

Compatible actions of a group tower on the finite-order quotient algebras induce an action
of its completed group on the completed algebra. The action is a homomorphism to algebra
automorphisms, characterized by its projections. Every induced filtration ideal is invariant,
and a group element vanishing at an order acts trivially at that order.

The construction upgrades `AlgFiltration.completedAction` using `AlgEquiv.ofRingEquiv`. It needs no
surjectivity of the group transitions, separatedness of the original algebra, or assumption
that the actions arise from exponentials.

Adapted from `Mei/RingTheory/FilteredAlgebra/Action.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei),
commit `a79c57178cc83666fc244ca6e6eeaa722e9b8bc7` (Apache 2.0).
-/

public section

open CategoryTheory Opposite

universe u

namespace TauCeti.AlgFiltration

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
  (F : AlgFiltration A) {G : ℕᵒᵖ ⥤ GrpCat.{u}}
  (ρ : ∀ k : ℕ, G.obj (op k) →* ((A ⧸ F.ideal (k + 1)) ≃ₐ[R]
    (A ⧸ F.ideal (k + 1))))
  (hρ : ∀ {k l : ℕ} (h : k ≤ l) (g : G.obj (op l)) (x : A ⧸ F.ideal (l + 1)),
    Ideal.Quotient.factor (F.antitone (Nat.add_le_add_right h 1)) (ρ l g x) =
      ρ k (G.map (homOfLE h).op g)
        (Ideal.Quotient.factor (F.antitone (Nat.add_le_add_right h 1)) x))

include hρ in
private theorem ringRepresentation_compatible {k l : ℕ} (h : k ≤ l)
    (g : G.obj (op l)) (x : A ⧸ F.ideal (l + 1)) :
    Ideal.Quotient.factor (F.antitone (Nat.add_le_add_right h 1))
        (((MulSemiringAction.toRingAut _ _).comp (ρ l)) g x) =
      ((MulSemiringAction.toRingAut _ _).comp (ρ k)) (G.map (homOfLE h).op g)
        (Ideal.Quotient.factor (F.antitone (Nat.add_le_add_right h 1)) x) := by
  simpa only [MonoidHom.comp_apply, MulSemiringAction.toRingAut_apply,
    MulSemiringAction.toRingEquiv_apply_apply, AlgEquiv.smul_def] using hρ h g x

/-- Extend compatible quotient-algebra actions to algebra automorphisms of the completion. -/
def completedAlgebraAction : completedGroup G →* (F.completion ≃ₐ[R] F.completion) where
  toFun g := AlgEquiv.ofRingEquiv
    (f := F.completedAction (fun k => (MulSemiringAction.toRingAut _ _).comp (ρ k))
        (F.ringRepresentation_compatible ρ hρ) g) (fun r => by
      apply F.completion_ext
      intro k
      rw [F.projection_completedAction, F.projection_algebraMap]
      simpa only [MonoidHom.comp_apply, MulSemiringAction.toRingAut_apply,
        MulSemiringAction.toRingEquiv_apply_apply, AlgEquiv.smul_def] using
          (ρ k (CompletedGroup.projection k g)).commutes r)
  map_one' := by
    apply AlgEquiv.toRingEquiv_injective
    exact (F.completedAction (fun k => (MulSemiringAction.toRingAut _ _).comp (ρ k))
      (F.ringRepresentation_compatible ρ hρ)).map_one
  map_mul' g g' := by
    apply AlgEquiv.toRingEquiv_injective
    exact (F.completedAction (fun k => (MulSemiringAction.toRingAut _ _).comp (ρ k))
      (F.ringRepresentation_compatible ρ hρ)).map_mul g g'

/-- The action at order `k` depends only on the order-`k` group and algebra components. -/
@[simp]
theorem projection_completedAlgebraAction (g : completedGroup G) (x : F.completion) (k : ℕ) :
    F.projection k (F.completedAlgebraAction ρ hρ g x) =
      ρ k (CompletedGroup.projection k g) (F.projection k x) := by
  -- The scalar upgrade retains the ring action’s underlying function.
  simpa only [completedAlgebraAction, MonoidHom.coe_mk, OneHom.coe_mk,
    AlgEquiv.ofRingEquiv_apply, MonoidHom.comp_apply, MulSemiringAction.toRingAut_apply,
    MulSemiringAction.toRingEquiv_apply_apply, AlgEquiv.smul_def] using
      F.projection_completedAction (fun k => (MulSemiringAction.toRingAut _ _).comp (ρ k))
        (F.ringRepresentation_compatible ρ hρ) g x k

/-- The projection formula uniquely determines the completed action. -/
theorem completedAlgebraAction_unique (σ : completedGroup G →* (F.completion ≃ₐ[R] F.completion))
    (hσ : ∀ (g : completedGroup G) (x : F.completion) (k : ℕ),
      F.projection k (σ g x) = ρ k (CompletedGroup.projection k g) (F.projection k x)) :
    σ = F.completedAlgebraAction ρ hρ := by
  apply MonoidHom.ext
  intro g
  apply AlgEquiv.ext
  intro x
  apply F.completion_ext
  intro k
  rw [F.projection_completedAlgebraAction, hσ]

/-- Every completed automorphism preserves and reflects each filtration ideal. -/
@[simp]
theorem completedAlgebraAction_mem_completionIdeal_iff (g : completedGroup G)
    (x : F.completion) (k : ℕ) :
    F.completedAlgebraAction ρ hρ g x ∈ F.completionIdeal k ↔ x ∈ F.completionIdeal k := by
  cases k with
  | zero => simp
  | succ k =>
    simp only [completionIdeal_succ, RingHom.mem_ker, F.projection_completedAlgebraAction,
      map_eq_zero_iff _ (ρ k (CompletedGroup.projection k g)).injective]

/-- An element of the group filtration acts trivially through the corresponding order. -/
theorem projection_completedAlgebraAction_of_mem_degreeFiltration {g : completedGroup G}
    {k : ℕ} (hg : g ∈ CompletedGroup.degreeFiltration G (k + 1)) (x : F.completion) :
    F.projection k (F.completedAlgebraAction ρ hρ g x) = F.projection k x := by
  have hg' : CompletedGroup.projection k g = 1 := by
    simpa only [CompletedGroup.degreeFiltration_succ, MonoidHom.mem_ker] using hg
  simp [hg']

/-- Elements vanishing through order `k` move every coefficient only in order `k + 1`. -/
theorem completedAlgebraAction_sub_mem_completionIdeal {g : completedGroup G} {k : ℕ}
    (hg : g ∈ CompletedGroup.degreeFiltration G (k + 1)) (x : F.completion) :
    F.completedAlgebraAction ρ hρ g x - x ∈ F.completionIdeal (k + 1) := by
  simp only [completionIdeal_succ, RingHom.mem_ker, map_sub,
    F.projection_completedAlgebraAction_of_mem_degreeFiltration ρ hρ hg, sub_self]

section RestrictScalars

variable {S : Type*} [CommRing S] [Algebra S R] [Algebra S A] [IsScalarTower S R A]

/-- The completed action commutes with restriction of the coefficient scalars. -/
theorem completedAlgebraAction_restrictScalars (g : completedGroup G) :
    (F.completedAlgebraAction ρ hρ g).restrictScalars S =
      F.completedAlgebraAction (R := S)
        (fun k => (AlgEquiv.restrictScalarsHom S).comp (ρ k))
        (by
          intro k l h g x
          simpa only [MonoidHom.comp_apply, AlgEquiv.restrictScalarsHom_apply,
            AlgEquiv.restrictScalars_apply] using hρ h g x) g := by
  apply AlgEquiv.ext
  intro x
  apply F.completion_ext
  intro k
  rw [AlgEquiv.restrictScalars_apply, F.projection_completedAlgebraAction ρ hρ]
  symm
  convert F.projection_completedAlgebraAction (R := S)
    (fun k => (AlgEquiv.restrictScalarsHom S).comp (ρ k))
    (by
      intro k l h g x
      simpa only [MonoidHom.comp_apply, AlgEquiv.restrictScalarsHom_apply,
        AlgEquiv.restrictScalars_apply] using hρ h g x) g x k
  simp only [MonoidHom.comp_apply, AlgEquiv.restrictScalarsHom_apply,
    AlgEquiv.restrictScalars_apply]

end RestrictScalars

end TauCeti.AlgFiltration
