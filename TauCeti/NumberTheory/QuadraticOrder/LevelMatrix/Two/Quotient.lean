/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.QuadraticOrder.LevelMatrix.Quotient
import TauCeti.NumberTheory.QuadraticOrder.LevelMatrix.Two.Basic

/-!
# Reduced global-unit subgroups at level two

For discriminants strictly below `-4`, `unitPeriodMatrixSubgroup a b 2 = ⊥`
(`unitPeriodMatrixSubgroup_two_eq_bot_of_discr_lt_neg_four`). By contrast, for the Gaussian and
Eisenstein integer algebras, every residue unit lifts to an actual integral unit, so the reduced
global-unit subgroup is `⊤` (`unitPeriodMatrixSubgroup_neg_one_zero_two_eq_top`,
`unitPeriodMatrixSubgroup_neg_one_one_two_eq_top`,
`unitPeriodMatrixSubgroup_neg_three_three_two_eq_top`).

## References

* D. H. Shin, *Generation of class fields by Siegel-Ramachandra invariants*, §§2, 4.
-/

public section

namespace QuadraticAlgebra

/-- At level `2`, `-1 = 1` in `periodMatrixGroup`, so for `discr a b < -4` the reduced global-unit
subgroup is trivial and the quotient collapses to `periodMatrixGroup (a : ZMod 2) (b : ZMod 2)`
itself. -/
@[simp]
theorem unitPeriodMatrixSubgroup_two_eq_bot_of_discr_lt_neg_four {a b : ℤ} (hd : discr a b < -4) :
    unitPeriodMatrixSubgroup a b 2 = ⊥ := by
  rw [unitPeriodMatrixSubgroup_eq_zpowers_neg_one hd 2, Subgroup.zpowers_eq_bot]
  exact Subtype.ext <| Units.ext <| by
    ext i j; fin_cases i <;> fin_cases j <;> simp [ZMod.neg_eq_self_mod_two]

/-- In the Gaussian integer algebra (`a = -1`, `b = 0`, `discr = -4`), the reduced global-unit
subgroup at level `2` is the entire multiplication-matrix group. -/
@[simp]
theorem unitPeriodMatrixSubgroup_neg_one_zero_two_eq_top :
    unitPeriodMatrixSubgroup (-1) 0 2 = ⊤ := by
  rw [eq_top_iff]
  rintro M -
  obtain ⟨u, hu⟩ := units_map_zmod_two_gaussian_surjective (periodUnitMatrixEquiv.symm M)
  exact mem_unitPeriodMatrixSubgroup_iff.mpr
    ⟨u, by rw [unitPeriodMatrixHom_apply, hu, MulEquiv.apply_symm_apply]⟩

/-- In the Eisenstein integer algebra (`a = -1`, `b = 1`, `discr = -3`), the reduced global-unit
subgroup at level `2` is the entire multiplication-matrix group. -/
@[simp]
theorem unitPeriodMatrixSubgroup_neg_one_one_two_eq_top :
    unitPeriodMatrixSubgroup (-1) 1 2 = ⊤ := by
  rw [eq_top_iff]
  rintro M -
  obtain ⟨u, hu⟩ := units_map_zmod_two_eisenstein_surjective (periodUnitMatrixEquiv.symm M)
  exact mem_unitPeriodMatrixSubgroup_iff.mpr
    ⟨u, by rw [unitPeriodMatrixHom_apply, hu, MulEquiv.apply_symm_apply]⟩

/-- In the `(1, (3 + i√3)/2)` presentation of the Eisenstein integers (`a = -3`, `b = 3`,
`discr = -3`), every level-`2` multiplication matrix likewise lifts to an integral unit (`1`,
`ω - 1`, or `(ω - 1)²`). -/
@[simp]
theorem unitPeriodMatrixSubgroup_neg_three_three_two_eq_top :
    unitPeriodMatrixSubgroup (-3) 3 2 = ⊤ := by
  rw [eq_top_iff]
  rintro M -
  set u := periodUnitMatrixEquiv.symm M
  suffices ∃ v : (QuadraticAlgebra ℤ (-3) 3)ˣ,
      Units.map (mapRingHom (Int.castRingHom (ZMod 2)) (-3) 3).toMonoidHom v = u by
    obtain ⟨v, hv⟩ := this
    exact mem_unitPeriodMatrixSubgroup_iff.mpr
      ⟨v, by rw [unitPeriodMatrixHom_apply, hv, MulEquiv.apply_symm_apply]⟩
  have hζ : IsUnit (⟨-1, 1⟩ : QuadraticAlgebra ℤ (-3) 3) :=
    isUnit_iff_norm_isUnit.mpr (by norm_num [norm_def])
  have hu := isUnit_iff_norm_isUnit.mp u.isUnit
  have h3 : (3 : ZMod 2) = 1 := by decide
  have key : ∀ t s : ZMod 2, IsUnit (t ^ 2 + t * s + s ^ 2) →
      (t = 1 ∧ s = 0) ∨ (t = 1 ∧ s = 1) ∨ (t = 0 ∧ s = 1) := by decide
  have hn : IsUnit (u.val.re ^ 2 + u.val.re * u.val.im + u.val.im ^ 2) := by
    simpa [norm_def, sq, h3, sub_eq_add_neg, ZMod.neg_eq_self_mod_two] using hu
  rcases key _ _ hn with h | h | h
  · exact ⟨1, Units.ext (by ext <;> simp [h.1, h.2])⟩
  · exact ⟨hζ.unit, Units.ext (by ext <;> simp [mapRingHom, h.1, h.2])⟩
  · exact ⟨hζ.unit ^ 2, Units.ext (by ext <;> simp [mapRingHom, sq, h.1, h.2, h3,
      CharTwo.add_self_eq_zero])⟩

end QuadraticAlgebra
