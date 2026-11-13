/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.GroupTheory.CompletedGroup.Basic
public import TauCeti.RingTheory.FilteredAlgebra.Completion

/-!
# Compatible actions on filtered ring completions

Compatible actions of a group tower on the finite-order quotient rings of a filtered ring
induce an action of its completed group on the completed ring. The action is a homomorphism
to ring automorphisms, characterized by its projections. Every completion ideal is preserved
and reflected, an element of the group filtration moves each element only in the next order,
and the action is faithful as soon as every finite-order action is.

The construction uses `AlgFiltration.lift` for the compatible endomorphisms and the group
structure of Mathlib's `RingAut`. It needs no surjectivity of the group transitions,
separatedness of the filtered ring, or assumption that the actions arise from exponentials.

Adapted from `yuma-mizuno-lean/Mei`, commit
`3d2e9c869ee44c41ae9c7b5c6e2042898430d0ca`,
`Mei/RingTheory/FilteredAlgebra/Action.lean` (Apache 2.0), at the level of rings.
-/

public section

open CategoryTheory Opposite

universe u

namespace TauCeti.AlgFiltration

variable {A : Type*} [Ring A] (F : TauCeti.AlgFiltration A) {G : ℕᵒᵖ ⥤ GrpCat.{u}}
  (ρ : ∀ k : ℕ, G.obj (op k) →* RingAut (A ⧸ F.ideal (k + 1)))
  (hρ : ∀ {k l : ℕ} (h : k ≤ l) (g : G.obj (op l)) (x : A ⧸ F.ideal (l + 1)),
    Ideal.Quotient.factor (F.antitone (Nat.add_le_add_right h 1)) (ρ l g x) =
      ρ k (G.map (homOfLE h).op g)
        (Ideal.Quotient.factor (F.antitone (Nat.add_le_add_right h 1)) x))

include hρ

/-- The endomorphism of the completion acting at order `k` by `ρ k` of the order-`k`
component of a completed group element. -/
private def actionHom (g : TauCeti.completedGroup G) : F.completion →+* F.completion :=
  F.lift (fun k => (ρ k (CompletedGroup.projection k g)).toRingHom.comp (F.projection k))
    (by
      intro k l h
      ext x
      simp [hρ h, CompletedGroup.map_projection, F.factor_projection h])

private theorem projection_actionHom (g : TauCeti.completedGroup G) (x : F.completion)
    (k : ℕ) :
    F.projection k (F.actionHom ρ hρ g x) =
      ρ k (CompletedGroup.projection k g) (F.projection k x) := by
  simp [actionHom]

private theorem actionHom_one : F.actionHom ρ hρ 1 = RingHom.id _ := by
  refine RingHom.ext fun x => F.completion_ext fun k => ?_
  simp [projection_actionHom]

private theorem actionHom_mul (g g' : TauCeti.completedGroup G) :
    F.actionHom ρ hρ (g * g') = (F.actionHom ρ hρ g).comp (F.actionHom ρ hρ g') := by
  refine RingHom.ext fun x => F.completion_ext fun k => ?_
  simp [projection_actionHom]

/-- Extend compatible quotient-ring actions to an action of the completed group by ring
automorphisms of the completed ring. -/
def completedAction : TauCeti.completedGroup G →* RingAut F.completion where
  toFun g := RingEquiv.ofRingHom (F.actionHom ρ hρ g) (F.actionHom ρ hρ g⁻¹)
    (by rw [← actionHom_mul, mul_inv_cancel, actionHom_one])
    (by rw [← actionHom_mul, inv_mul_cancel, actionHom_one])
  map_one' := RingEquiv.ext fun x => by simp [actionHom_one]
  map_mul' g g' := RingEquiv.ext fun x => by simp [actionHom_mul]

/-- The action at order `k` depends only on the order-`k` group and ring components. -/
@[simp]
theorem projection_completedAction (g : TauCeti.completedGroup G) (x : F.completion)
    (k : ℕ) :
    F.projection k (F.completedAction ρ hρ g x) =
      ρ k (CompletedGroup.projection k g) (F.projection k x) :=
  F.projection_actionHom ρ hρ g x k

/-- The projection formula uniquely determines the completed action. -/
theorem completedAction_unique (σ : TauCeti.completedGroup G →* RingAut F.completion)
    (hσ : ∀ (g : TauCeti.completedGroup G) (x : F.completion) (k : ℕ),
      F.projection k (σ g x) = ρ k (CompletedGroup.projection k g) (F.projection k x)) :
    σ = F.completedAction ρ hρ :=
  MonoidHom.ext fun g => RingEquiv.ext fun x => F.completion_ext fun k => by
    rw [hσ, projection_completedAction]

/-- Every completed automorphism preserves and reflects each completion ideal. -/
@[simp]
theorem completedAction_mem_completionIdeal_iff (g : TauCeti.completedGroup G)
    (x : F.completion) (k : ℕ) :
    F.completedAction ρ hρ g x ∈ F.completionIdeal k ↔ x ∈ F.completionIdeal k := by
  cases k with
  | zero => simp
  | succ k =>
    simp [completionIdeal_succ, map_eq_zero_iff _ (ρ k (CompletedGroup.projection k g)).injective]

/-- An element of the group filtration acts trivially through the corresponding order. -/
theorem projection_completedAction_of_mem_degreeFiltration {g : TauCeti.completedGroup G}
    {k : ℕ} (hg : g ∈ CompletedGroup.degreeFiltration G (k + 1)) (x : F.completion) :
    F.projection k (F.completedAction ρ hρ g x) = F.projection k x := by
  have hg' : CompletedGroup.projection k g = 1 := by
    simpa only [CompletedGroup.degreeFiltration_succ, MonoidHom.mem_ker] using hg
  simp [hg']

/-- An element of the group filtration moves every element only in the next order. -/
theorem completedAction_sub_mem_completionIdeal {g : TauCeti.completedGroup G} {k : ℕ}
    (hg : g ∈ CompletedGroup.degreeFiltration G (k + 1)) (x : F.completion) :
    F.completedAction ρ hρ g x - x ∈ F.completionIdeal (k + 1) := by
  simp [completionIdeal_succ, F.projection_completedAction_of_mem_degreeFiltration ρ hρ hg]

/-- Faithful finite-order actions induce a faithful action of the completed group. No
surjectivity of the group transitions is needed, since the canonical map to the completion is
surjective at every finite order. -/
theorem completedAction_injective (hfaithful : ∀ k, Function.Injective (ρ k)) :
    Function.Injective (F.completedAction ρ hρ) := by
  intro g g' h
  refine CompletedGroup.ext fun k => hfaithful k (RingEquiv.ext fun x => ?_)
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  simpa using congrArg (fun e : RingAut F.completion => F.projection k (e (F.toCompletion a))) h

end TauCeti.AlgFiltration
