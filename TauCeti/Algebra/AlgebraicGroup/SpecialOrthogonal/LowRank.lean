/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Reductive
public import TauCeti.Algebra.AlgebraicGroup.SpecialOrthogonal.Basic

/-!
# Special orthogonal groups in ranks zero and one

The standard special orthogonal groups `SO₀` and `SO₁` are trivial over every commutative base
ring. In Hopf coordinates, their defining ideals agree with the corresponding special-linear
ideals. In rank zero there are no orthogonality relations. In rank one, the single relation
`x² - 1` is a multiple of the determinant-one relation `x - 1`.

The resulting equality identifies the finite-type coordinate Hopf algebras with those of `SL₀`
and `SL₁`. Since the special linear groups are reductive in every rank and characteristic, this
settles reductivity of the two low-rank special orthogonal groups without a hypothesis on `2`.

## Main declarations

* `TauCeti.SpecialOrthogonal.definingHopfIdeal_zero`: the rank-zero defining ideal agrees with
  the special-linear ideal.
* `TauCeti.SpecialOrthogonal.definingHopfIdeal_one`: the rank-one defining ideal agrees with the
  special-linear ideal.
* `TauCeti.SpecialOrthogonal.reductiveCommHopfAlgProperty_finiteTypeCoordinateHopfAlgebra_zero`
  and `TauCeti.SpecialOrthogonal.reductiveCommHopfAlgProperty_finiteTypeCoordinateHopfAlgebra_one`:
  `SO₀` and `SO₁` are reductive over every field.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§2.3 and 21, for the standard orthogonal groups and
  reductivity.
-/

public section

namespace TauCeti.SpecialOrthogonal

universe u

noncomputable section

variable (R : Type u) [CommRing R]

/-- In rank zero the special-orthogonal and special-linear defining Hopf ideals agree. -/
@[simp]
theorem definingHopfIdeal_zero :
    definingHopfIdeal R 0 = SpecialLinear.definingHopfIdeal R 0 := by
  have hempty : Orthogonal.relationSet R 0 = ∅ := by
    ext x
    rw [ConstantForm.mem_relationSet_iff]
    constructor
    · rintro ⟨i, -⟩
      exact Fin.elim0 i
    · simp
  apply HopfIdeal.ext
  intro x
  rw [← HopfIdeal.mem_toIdeal, ← HopfIdeal.mem_toIdeal, definingHopfIdeal_toIdeal,
    SpecialLinear.definingHopfIdeal_toIdeal]
  simp [hempty]

/-- In rank one the special-orthogonal and special-linear defining Hopf ideals agree. -/
@[simp]
theorem definingHopfIdeal_one :
    definingHopfIdeal R 1 = SpecialLinear.definingHopfIdeal R 1 := by
  have hrelation :
      ConstantForm.relationMatrix R 1 1 0 0 =
        (GeneralLinear.determinantGroupLike R 1 :
            GeneralLinear.coordinateHopfAlgebra R 1) ^ 2 - 1 := by
    rw [ConstantForm.relationMatrix_def]
    simp [Matrix.mul_apply, pow_two]
  have hrel : Ideal.span (Orthogonal.relationSet R 1) ≤
      Ideal.span
        {(GeneralLinear.determinantGroupLike R 1 :
            GeneralLinear.coordinateHopfAlgebra R 1) - 1} := by
    rw [Ideal.span_le]
    intro y hy
    rw [ConstantForm.mem_relationSet_iff] at hy
    obtain ⟨i, j, rfl⟩ := hy
    have hi : i = 0 := Subsingleton.elim _ _
    have hj : j = 0 := Subsingleton.elim _ _
    subst i
    subst j
    rw [hrelation]
    exact Ideal.mem_of_dvd _
      (sub_one_dvd_pow_sub_one
        (GeneralLinear.determinantGroupLike R 1 :
          GeneralLinear.coordinateHopfAlgebra R 1) 2)
      (Ideal.mem_span_singleton_self _)
  apply HopfIdeal.ext
  intro x
  rw [← HopfIdeal.mem_toIdeal, ← HopfIdeal.mem_toIdeal, definingHopfIdeal_toIdeal,
    SpecialLinear.definingHopfIdeal_toIdeal, sup_eq_right.mpr hrel]

/-- The finite-type coordinate Hopf algebra of `SO₀` is the one of `SL₀`. -/
@[simp]
theorem finiteTypeCoordinateHopfAlgebra_zero :
    finiteTypeCoordinateHopfAlgebra R 0 = SpecialLinear.finiteTypeCoordinateHopfAlgebra R 0 := by
  apply CategoryTheory.ObjectProperty.FullSubcategory.ext
  rw [finiteTypeCoordinateHopfAlgebra_obj, SpecialLinear.finiteTypeCoordinateHopfAlgebra_obj]
  exact congrArg (CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra R 0))
    (definingHopfIdeal_zero R)

/-- The finite-type coordinate Hopf algebra of `SO₁` is the one of `SL₁`. -/
@[simp]
theorem finiteTypeCoordinateHopfAlgebra_one :
    finiteTypeCoordinateHopfAlgebra R 1 = SpecialLinear.finiteTypeCoordinateHopfAlgebra R 1 := by
  apply CategoryTheory.ObjectProperty.FullSubcategory.ext
  rw [finiteTypeCoordinateHopfAlgebra_obj, SpecialLinear.finiteTypeCoordinateHopfAlgebra_obj]
  exact congrArg (CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra R 1))
    (definingHopfIdeal_one R)

/-- **The rank-zero special orthogonal group is reductive over every field.** -/
theorem reductiveCommHopfAlgProperty_finiteTypeCoordinateHopfAlgebra_zero
    (k : Type u) [Field k] :
    reductiveCommHopfAlgProperty k (finiteTypeCoordinateHopfAlgebra k 0) := by
  rw [finiteTypeCoordinateHopfAlgebra_zero]
  exact SpecialLinear.reductiveCommHopfAlgProperty_finiteTypeCoordinateHopfAlgebra k 0

/-- **The rank-one special orthogonal group is reductive over every field.** -/
theorem reductiveCommHopfAlgProperty_finiteTypeCoordinateHopfAlgebra_one
    (k : Type u) [Field k] :
    reductiveCommHopfAlgProperty k (finiteTypeCoordinateHopfAlgebra k 1) := by
  rw [finiteTypeCoordinateHopfAlgebra_one]
  exact SpecialLinear.reductiveCommHopfAlgProperty_finiteTypeCoordinateHopfAlgebra k 1

end

end TauCeti.SpecialOrthogonal
