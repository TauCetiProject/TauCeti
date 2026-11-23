/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Tower.Basic
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic

/-!
# Compatible group actions on module tower limits

A tower of groups acting compatibly on a tower of modules acts on its module limit.
The acting group is Mathlib's group of sections of the group tower, and the module
limit is the existing `TauCeti.ModuleTower.lim`. Thus this construction applies to
completed coefficient modules without choosing representatives of quotient classes.

`limAction` is characterized by its projections. Equivariant tower maps remain equivariant
on limits. Faithfulness follows from faithful finite actions when the module-limit
projections are surjective; this last hypothesis is needed to test the finite actions.

Adapted from `Mei/LinearAlgebra/ModuleFiltration/GroupAction.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`97304cc1bd51a202db1a705709fb4763f61e190a` (Apache 2.0). The construction uses
`ModuleTower.limLift` and Mathlib's passage from endomorphisms to automorphisms.
-/

public noncomputable section

namespace TauCeti.ModuleTower

open CategoryTheory Opposite

universe u v w

variable {R : Type u} [Ring R] (F : ModuleTower.{v} R)
  {G : ℕᵒᵖ ⥤ GrpCat.{w}}
  (ρ : ∀ k : ℕ, G.obj (op k) →* (F.obj (op k) ≃ₗ[R] F.obj (op k)))
  (hρ : ∀ (k : ℕ) (g : G.obj (op (k + 1))) (x : F.obj (op (k + 1))),
    F.transition k (ρ (k + 1) g x) =
      ρ k (G.map (homOfLE (Nat.le_succ k)).op g) (F.transition k x))

private def limActionEnd : (G ⋙ forget GrpCat).sections →* Module.End R F.lim where
  toFun g := F.limLift
    (fun k => (ρ k (g.val (op k))).toLinearMap.comp (F.limπ k))
    (by
      intro k
      ext x
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      have hg : G.map (homOfLE (Nat.le_succ k)).op (g.val (op (k + 1))) =
          g.val (op k) := g.property (homOfLE (Nat.le_succ k)).op
      rw [hρ, hg]
      simpa only [limπ_apply] using
        congrArg (ρ k (g.val (op k))) (F.transition_coe_lim_succ x k))
  map_one' := by
    apply LinearMap.ext
    intro x
    apply F.lim_ext
    intro k
    have h_one : (1 : (G ⋙ forget GrpCat).sections).val (op k) = 1 :=
      (GrpCat.sectionsπMonoidHom G (op k)).map_one
    simp [h_one]
  map_mul' g g' := by
    apply LinearMap.ext
    intro x
    apply F.lim_ext
    intro k
    have h_mul : (g * g').val (op k) = g.val (op k) * g'.val (op k) :=
      (GrpCat.sectionsπMonoidHom G (op k)).map_mul g g'
    simp [h_mul]

/-- Compatible finite-order representations induce a representation on the module limit.
The source is the group of matching families of the group tower. -/
def limAction : (G ⋙ forget GrpCat).sections →* (F.lim ≃ₗ[R] F.lim) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv R F.lim).toMonoidHom.comp
    (F.limActionEnd ρ hρ).toHomUnits

/-- The induced action is computed at each order by the given representation. -/
@[simp]
theorem coe_limAction_apply (g : (G ⋙ forget GrpCat).sections) (x : F.lim) (k : ℕ) :
    (F.limAction ρ hρ g x : F.Product) k = ρ k (g.val (op k)) (x.val k) := by
  simp [limAction, limActionEnd]

/-- The projection formula uniquely determines the induced representation. -/
theorem limAction_unique
    (σ : (G ⋙ forget GrpCat).sections →* (F.lim ≃ₗ[R] F.lim))
    (hσ : ∀ (g : (G ⋙ forget GrpCat).sections) (x : F.lim) (k : ℕ),
      F.limπ k (σ g x) = ρ k (g.val (op k)) (F.limπ k x)) :
    σ = F.limAction ρ hρ := by
  ext g x : 2
  apply F.lim_ext
  intro k
  simpa only [limπ_apply, F.coe_limAction_apply] using hσ g x k

/-- Faithful finite representations induce a faithful limit representation if every
module-limit projection is surjective. No surjectivity of group transitions is required. -/
theorem limAction_injective (hπ : ∀ k, Function.Surjective (F.limπ k))
    (hfaithful : ∀ k, Function.Injective (ρ k)) :
    Function.Injective (F.limAction ρ hρ) := by
  intro g g' he
  apply Subtype.ext
  funext j
  apply hfaithful j.unop
  ext x
  obtain ⟨a, rfl⟩ := hπ j.unop x
  have hx := congrArg (fun e : F.lim ≃ₗ[R] F.lim => F.limπ j.unop (e a)) he
  simp only [F.limπ_apply, F.coe_limAction_apply, op_unop] at hx ⊢
  exact hx

section EquivariantMap

variable {H : ModuleTower R}
  (σ : ∀ k : ℕ, G.obj (op k) →* (H.obj (op k) ≃ₗ[R] H.obj (op k)))
  (hσ : ∀ (k : ℕ) (g : G.obj (op (k + 1))) (x : H.obj (op (k + 1))),
    H.transition k (σ (k + 1) g x) =
      σ k (G.map (homOfLE (Nat.le_succ k)).op g) (H.transition k x))
  (f : F ⟶ H)

/-- A map intertwining all the finite-order actions intertwines the limit actions. -/
theorem limMap_limAction
    (hequiv : ∀ (k : ℕ) (g : G.obj (op k)) (x : F.obj (op k)),
      f.app (op k) (ρ k g x) = σ k g (f.app (op k) x))
    (g : (G ⋙ forget GrpCat).sections) (x : F.lim) :
    limMap f (F.limAction ρ hρ g x) = H.limAction σ hσ g (limMap f x) := by
  apply H.lim_ext
  intro k
  simpa only [F.limπ_apply, H.limπ_apply, F.coe_limAction_apply,
    H.coe_limAction_apply, coe_limMap_apply, productMap_apply] using
    hequiv k (g.val (op k)) (F.limπ k x)

end EquivariantMap

end TauCeti.ModuleTower
