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
Eisenstein integer algebras — and hence for every integral quadratic algebra of discriminant `-4`
or `-3` — every residue unit lifts to an actual integral unit, so the reduced global-unit subgroup
is `⊤` (`unitPeriodMatrixSubgroup_neg_one_zero_two_eq_top`,
`unitPeriodMatrixSubgroup_neg_one_one_two_eq_top`,
`unitPeriodMatrixSubgroup_two_eq_top_of_discr_eq_neg_four`,
`unitPeriodMatrixSubgroup_two_eq_top_of_discr_eq_neg_three`).

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

/-- For any quadratic algebra of discriminant `-4`, the reduced global-unit subgroup at level `2`
is the entire multiplication-matrix group. -/
@[simp]
theorem unitPeriodMatrixSubgroup_two_eq_top_of_discr_eq_neg_four {a b : ℤ} (hd : discr a b = -4) :
    unitPeriodMatrixSubgroup a b 2 = ⊤ :=
  unitPeriodMatrixSubgroup_eq_top_of_discr_eq (by rw [hd, discr_def]; norm_num)
    unitPeriodMatrixSubgroup_neg_one_zero_two_eq_top

/-- For any quadratic algebra of discriminant `-3`, the reduced global-unit subgroup at level `2`
is the entire multiplication-matrix group. -/
@[simp]
theorem unitPeriodMatrixSubgroup_two_eq_top_of_discr_eq_neg_three {a b : ℤ} (hd : discr a b = -3) :
    unitPeriodMatrixSubgroup a b 2 = ⊤ :=
  unitPeriodMatrixSubgroup_eq_top_of_discr_eq (by rw [hd, discr_def]; norm_num)
    unitPeriodMatrixSubgroup_neg_one_one_two_eq_top

end QuadraticAlgebra
