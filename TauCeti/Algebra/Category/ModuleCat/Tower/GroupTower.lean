/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Tower.Basic
public import TauCeti.Algebra.Group.Tower

/-!
# The nonabelian `lim¹` of a tower of modules

The underlying additive groups of a tower of modules, written multiplicatively, form a tower of
groups (`TauCeti.ModuleTower.toGroupTower`). For abelian groups the twisted action of a family `g`
is translation by the image `δ(g)` of the shift map, `δ(g)ₙ = gₙ - φₙ(gₙ₊₁)`, so the orbits of the
twisted action are the cosets of the image of `δ`, and its stabilizer of `0` is the kernel of `δ`.
Hence the nonabelian `lim¹` and `lim` of the underlying tower of groups are the cokernel and the
kernel of the shift map, `TauCeti.ModuleTower.limOne` and `TauCeti.ModuleTower.lim`.

## Main statements

* `TauCeti.ModuleTower.groupTowerLimOneEquiv`: the orbit set of the twisted action is the cokernel
  of the shift map, compatibly with the base points.
* `TauCeti.ModuleTower.mem_toGroupTower_lim_iff`: the compatible families of the two towers agree.
-/

public section

namespace TauCeti.ModuleTower

open CategoryTheory Opposite

universe v u

variable {R : Type u} [Ring R] (F : ModuleTower.{v} R)

/-- The tower of groups underlying a tower of modules, written multiplicatively. -/
def toGroupTower : GroupTower fun n ↦ Multiplicative (F.obj (op n)) :=
  fun n ↦ (F.transition n).toAddMonoidHom.toMultiplicative

@[simp]
lemma toGroupTower_apply (n : ℕ) (x : Multiplicative (F.obj (op (n + 1)))) :
    F.toGroupTower n x = Multiplicative.ofAdd (F.transition n x.toAdd) :=
  (rfl)

/-- A family lies in the limit of the underlying tower of groups exactly when the corresponding
family of the tower of modules lies in its limit. -/
lemma mem_toGroupTower_lim_iff {x : ∀ n, Multiplicative (F.obj (op n))} :
    x ∈ F.toGroupTower.lim ↔ (fun n ↦ (x n).toAdd) ∈ F.lim := by
  simp [GroupTower.mem_lim, mem_lim, ← Equiv.eq_symm_apply]

/-- The nonabelian `lim¹` of the tower of groups underlying a tower of modules is its `lim¹`, the
cokernel of the shift map: the orbit of a family under the twisted action is sent to its class
modulo the image of the shift map. -/
def groupTowerLimOneEquiv : F.toGroupTower.limOne ≃ F.limOne :=
  Quotient.congr
    { toFun x n := (x.val n).toAdd
      invFun x := ⟨fun n ↦ Multiplicative.ofAdd (x n)⟩
      left_inv _ := rfl
      right_inv _ := rfl } fun x y ↦ by
    simp only [Equiv.coe_fn_mk, MulAction.orbitRel_apply, MulAction.mem_orbit_iff,
      Submodule.quotientRel_def, LinearMap.mem_range, GroupTower.Twisted.ext_iff, funext_iff,
      GroupTower.val_smul, shift_apply, Pi.sub_apply]
    constructor
    · rintro ⟨g, hg⟩
      refine ⟨fun n ↦ (g n).toAdd, fun n ↦ ?_⟩
      rw [← hg n]
      simp only [toAdd_mul, toAdd_inv, toGroupTower_apply, toAdd_ofAdd]
      abel
    · rintro ⟨g, hg⟩
      refine ⟨fun n ↦ Multiplicative.ofAdd (g n), fun n ↦ ?_⟩
      rw [← Multiplicative.toAdd.apply_eq_iff_eq, ← add_eq_of_eq_sub (hg n)]
      simp only [toAdd_mul, toAdd_inv, toGroupTower_apply, toAdd_ofAdd]
      abel

@[simp]
lemma groupTowerLimOneEquiv_mk (x : ∀ n, Multiplicative (F.obj (op n))) :
    F.groupTowerLimOneEquiv (Quotient.mk'' ⟨x⟩) =
      Submodule.Quotient.mk (fun n ↦ (x n).toAdd) :=
  (rfl)

/-- The comparison carries the base point of the nonabelian `lim¹` to `0`. -/
@[simp]
lemma groupTowerLimOneEquiv_one : F.groupTowerLimOneEquiv 1 = 0 := by
  rw [GroupTower.one_def, groupTowerLimOneEquiv_mk]
  rfl

end TauCeti.ModuleTower
