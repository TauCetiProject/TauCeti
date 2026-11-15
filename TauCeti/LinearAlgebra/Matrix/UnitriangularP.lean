/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.GroupTheory.PGroup
public import Mathlib.LinearAlgebra.Matrix.CharP
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperUnitriangular.Basic

/-!
# Upper-unitriangular groups in prime characteristic

Let `R` be a ring of prime characteristic `p` and `m` a finite linearly ordered index type. For an
upper-unitriangular matrix `M`, the matrix `M - 1` is strictly upper triangular, so its
`Fintype.card m`th power vanishes; since `1` commutes with `M - 1`, the Frobenius identity then
gives `M ^ p ^ Fintype.card m = 1`. Hence the upper-unitriangular group
`TauCeti.upperUnitriangularGroup m R` is a `p`-group.
-/

public section

namespace Matrix

variable {m R : Type*} [Fintype m] [LinearOrder m]

/-- An upper-unitriangular `m × m` matrix over a ring of prime characteristic `p` has order
dividing `p ^ Fintype.card m`. -/
theorem IsUpperUnitriangular.pow_eq_one [Ring R] {p : ℕ} [hp : Fact p.Prime] [CharP R p]
    {M : Matrix m m R} (hM : M.IsUpperUnitriangular) : M ^ p ^ Fintype.card m = 1 := by
  -- the characteristic of the matrix ring is only available over a nonempty index type
  cases isEmpty_or_nonempty m
  · exact Subsingleton.elim _ _
  have hnil : (M - 1) ^ p ^ Fintype.card m = 0 :=
    pow_eq_zero_of_le (Nat.lt_pow_self hp.out.one_lt).le
      (pow_card_eq_zero_of_isUpperTriangular_of_diag_eq_zero hM.isUpperTriangular_sub_one
        hM.sub_one_apply_diag)
  rw [← add_sub_cancel 1 M, add_pow_char_pow_of_commute p (Fintype.card m) (Commute.one_left _),
    one_pow, hnil, add_zero]

end Matrix

namespace TauCeti

variable {m R : Type*} [Fintype m] [LinearOrder m]

/-- Over a ring of prime characteristic `p`, the upper-unitriangular group is a `p`-group. -/
theorem isPGroup_upperUnitriangularGroup [Ring R] {p : ℕ} [Fact p.Prime] [CharP R p] :
    IsPGroup p (upperUnitriangularGroup m R) := fun g ↦
  ⟨Fintype.card m, Subtype.ext (Units.ext (by
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val]
    exact (UpperUnitriangularGroup.isUpperUnitriangular g).pow_eq_one))⟩

end TauCeti
