/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Data.ZMod.Defs
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import TauCeti.Algebra.QuadraticAlgebra.UnitMatrix

import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Quadratic multiplication matrices at level three

Over `(a, b) = (0, 0)` in `ZMod 3` — the ramified reduction occurring when `3` divides both `a`
and `b` — the three lower-triangular unipotent matrices `!![1, 0; s, 1]` (`s : ZMod 3`) of
`unipotentPeriodMatrixHom (ZMod 3)` form a subgroup isomorphic to `Multiplicative (ZMod 3)` that
projects bijectively onto the cosets modulo `{±I}` (`unipotentPeriodMatrixQuotientEquivZModThree`).

## References

* D. H. Shin, *Generation of class fields by Siegel–Ramachandra invariants*, §§2, 4.
-/

public noncomputable section

open Matrix

namespace QuadraticAlgebra

/-- Injectivity of the composite `Multiplicative (ZMod 3) →* periodMatrixGroup 0 0 ⧸ {±I}`. -/
private theorem unipotentPeriodMatrixHom_mk_injective :
    Function.Injective
      ((QuotientGroup.mk'
          (Subgroup.zpowers (-1 : periodMatrixGroup (0 : ZMod 3) (0 : ZMod 3)))).comp
        (unipotentPeriodMatrixHom (ZMod 3))) := by
  rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
  intro s hs
  simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff, Subgroup.mem_zpowers_iff] at hs
  obtain ⟨k, hk⟩ := hs
  rw [show (-1 : periodMatrixGroup (0 : ZMod 3) (0 : ZMod 3)) = periodUnitMatrixEquiv (-1) by simp,
    ← map_zpow] at hk
  have him := congrArg (fun M : periodMatrixGroup (0 : ZMod 3) (0 : ZMod 3) ↦
      ((M : GL (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)) 1 0) hk
  have hneg : ((((-1 : (QuadraticAlgebra (ZMod 3) 0 0)ˣ) ^ k :
      (QuadraticAlgebra (ZMod 3) 0 0)ˣ) : QuadraticAlgebra (ZMod 3) 0 0)).im = 0 := by
    rcases Int.even_or_odd k with ⟨n, rfl⟩ | ⟨n, rfl⟩
    · simp [← two_mul, zpow_mul]
    · simp [zpow_add, zpow_mul]
  simp only [coe_periodUnitMatrixEquiv, coe_periodUnitMatrix, periodMulMatrix_eq,
    coe_unipotentPeriodMatrixHom, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one,
    Matrix.cons_val_zero, hneg] at him
  exact Multiplicative.toAdd.injective him.symm

/-- Surjectivity of the composite `Multiplicative (ZMod 3) →* periodMatrixGroup 0 0 ⧸ {±I}`. -/
private theorem unipotentPeriodMatrixHom_mk_surjective :
    Function.Surjective
      ((QuotientGroup.mk'
          (Subgroup.zpowers (-1 : periodMatrixGroup (0 : ZMod 3) (0 : ZMod 3)))).comp
        (unipotentPeriodMatrixHom (ZMod 3))) := by
  intro x
  obtain ⟨M, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨u, rfl⟩ := periodUnitMatrixEquiv.surjective M
  have hu : IsUnit u.val.re := by simpa [norm_def, sq] using isUnit_iff_norm_isUnit.mp u.isUnit
  rcases (show ∀ t : ZMod 3, IsUnit t → t = 1 ∨ t = -1 by decide) u.val.re hu with h1 | h1
  · refine ⟨Multiplicative.ofAdd u.val.im, ?_⟩
    simp only [MonoidHom.comp_apply, QuotientGroup.mk'_apply]
    congr 1; apply periodUnitMatrixEquiv.symm.injective; apply Units.ext
    rw [val_periodUnitMatrixEquiv_symm_unipotentPeriodMatrixHom, MulEquiv.symm_apply_apply]
    ext <;> simp [h1]
  · refine ⟨Multiplicative.ofAdd (-u.val.im), ?_⟩
    have hneg : unipotentPeriodMatrixHom (ZMod 3) (Multiplicative.ofAdd (-u.val.im)) =
        -periodUnitMatrixEquiv u := by
      apply periodUnitMatrixEquiv.symm.injective; apply Units.ext
      rw [val_periodUnitMatrixEquiv_symm_unipotentPeriodMatrixHom, ← periodUnitMatrixEquiv_neg,
        MulEquiv.symm_apply_apply]
      ext <;> simp [h1]
    simp only [MonoidHom.comp_apply, QuotientGroup.mk'_apply, hneg, QuotientGroup.eq,
      Subgroup.mem_zpowers_iff]
    exact ⟨1, by rw [zpow_one, eq_inv_mul_iff_mul_eq]; simp⟩

/-- Over `ZMod 3` with `(a, b) = (0, 0)`, the three lower-triangular unipotent matrices
`!![1, 0; s, 1]` (`s : ZMod 3`) form a complete, irredundant set of coset representatives for
`periodMatrixGroup (0 : ZMod 3) (0 : ZMod 3) ⧸ Subgroup.zpowers (-1)`. -/
def unipotentPeriodMatrixQuotientEquivZModThree :
    Multiplicative (ZMod 3) ≃*
      periodMatrixGroup (0 : ZMod 3) (0 : ZMod 3) ⧸
        Subgroup.zpowers (-1 : periodMatrixGroup (0 : ZMod 3) (0 : ZMod 3)) :=
  MulEquiv.ofBijective ((QuotientGroup.mk' _).comp (unipotentPeriodMatrixHom (ZMod 3)))
    ⟨unipotentPeriodMatrixHom_mk_injective, unipotentPeriodMatrixHom_mk_surjective⟩

/-- `unipotentPeriodMatrixQuotientEquivZModThree` sends `Multiplicative.ofAdd s` to the coset of
`unipotentPeriodMatrixHom (ZMod 3) (Multiplicative.ofAdd s)`. -/
@[simp]
theorem unipotentPeriodMatrixQuotientEquivZModThree_ofAdd (s : ZMod 3) :
    unipotentPeriodMatrixQuotientEquivZModThree (Multiplicative.ofAdd s) =
      (unipotentPeriodMatrixHom (ZMod 3) (Multiplicative.ofAdd s) :
        periodMatrixGroup (0 : ZMod 3) (0 : ZMod 3) ⧸ Subgroup.zpowers (-1)) := by
  rfl

end QuadraticAlgebra
