/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.LinearAlgebra.Matrix.SpecialOrthogonalGroup.Basic

/-!
# The two-dimensional special orthogonal group

Over a commutative ring containing an element `i` with `i ^ 2 = -1` and a chosen half, the
special orthogonal group of the standard form in dimension two is the unit group. The
equivalence sends

`!![a, b; -b, a]` to the unit `a + i * b`.

This is the elementary matrix form of the splitness of the even-dimensional standard
orthogonal group in rank one.  Keeping the explicit formulas available is useful when a
one-parameter family in `SO₂` must be evaluated over a Laurent polynomial ring.

## Main declaration

* `Matrix.SpecialOrthogonalGroup.finTwoMulEquivUnits`: the explicit equivalence
  `SO₂(R) ≃* Rˣ`.

## References

* J. S. Milne, *Algebraic Groups* (2017), §18.c.
-/

public section

namespace Matrix.SpecialOrthogonalGroup

variable {R : Type*} [CommRing R]

attribute [local instance] starRingOfComm

/-- The unit determined by a two-dimensional special orthogonal matrix. -/
noncomputable def finTwoToUnit (i : R) (hi : i ^ 2 = -1)
    (M : Matrix.specialOrthogonalGroup (Fin 2) R) : Rˣ :=
  let a : R := M.val 0 0
  let b : R := M.val 0 1
  { val := a + i * b
    inv := a - i * b
    val_inv := by
      have hM := (Matrix.mem_specialOrthogonalGroup_fin_two_iff.mp M.2).2.2
      dsimp only [a, b]
      calc
        (M.val 0 0 + i * M.val 0 1) * (M.val 0 0 - i * M.val 0 1) =
            M.val 0 0 ^ 2 - i ^ 2 * M.val 0 1 ^ 2 := by ring
        _ = M.val 0 0 ^ 2 + M.val 0 1 ^ 2 := by rw [hi]; ring
        _ = 1 := hM
    inv_val := by
      have hM := (Matrix.mem_specialOrthogonalGroup_fin_two_iff.mp M.2).2.2
      dsimp only [a, b]
      calc
        (M.val 0 0 - i * M.val 0 1) * (M.val 0 0 + i * M.val 0 1) =
            M.val 0 0 ^ 2 - i ^ 2 * M.val 0 1 ^ 2 := by ring
        _ = M.val 0 0 ^ 2 + M.val 0 1 ^ 2 := by rw [hi]; ring
        _ = 1 := hM }

/-- The underlying value of the unit determined by a two-dimensional special orthogonal
matrix. -/
@[simp]
theorem coe_finTwoToUnit (i : R) (hi : i ^ 2 = -1)
    (M : Matrix.specialOrthogonalGroup (Fin 2) R) :
    (finTwoToUnit i hi M : R) =
      (M : Matrix (Fin 2) (Fin 2) R) 0 0 +
        i * (M : Matrix (Fin 2) (Fin 2) R) 0 1 :=
  (rfl)

/-- The inverse of the unit determined by a two-dimensional special orthogonal matrix. -/
@[simp]
theorem coe_inv_finTwoToUnit (i : R) (hi : i ^ 2 = -1)
    (M : Matrix.specialOrthogonalGroup (Fin 2) R) :
    (↑(finTwoToUnit i hi M)⁻¹ : R) =
      (M : Matrix (Fin 2) (Fin 2) R) 0 0 -
        i * (M : Matrix (Fin 2) (Fin 2) R) 0 1 :=
  (rfl)

/-- The two-dimensional special orthogonal matrix determined by a unit. -/
noncomputable def finTwoOfUnit (i half : R) (hi : i ^ 2 = -1)
    (hhalf : 2 * half = 1) (u : Rˣ) : Matrix.specialOrthogonalGroup (Fin 2) R :=
  let a : R := half * ((u : R) + (↑u⁻¹ : R))
  let b : R := -i * half * ((u : R) - (↑u⁻¹ : R))
  ⟨!![a, b; -b, a], by
    rw [Matrix.of_mem_specialOrthogonalGroup_fin_two_iff]
    refine ⟨rfl, (neg_neg _).symm, ?_⟩
    have hu : (u : R) * (↑u⁻¹ : R) = 1 := Units.mul_inv u
    dsimp only [a, b]
    calc
      (half * ((u : R) + (↑u⁻¹ : R))) ^ 2 +
          (-i * half * ((u : R) - (↑u⁻¹ : R))) ^ 2 =
        half ^ 2 * (((u : R) + (↑u⁻¹ : R)) ^ 2 +
          i ^ 2 * ((u : R) - (↑u⁻¹ : R)) ^ 2) := by ring
      _ = (2 * half) ^ 2 * ((u : R) * (↑u⁻¹ : R)) := by rw [hi]; ring
      _ = 1 := by rw [hhalf, hu]; simp⟩

/-- The underlying matrix determined by a unit, in terms of the unit and its inverse. -/
@[simp]
theorem coe_finTwoOfUnit (i half : R) (hi : i ^ 2 = -1)
    (hhalf : 2 * half = 1) (u : Rˣ) :
    (finTwoOfUnit i half hi hhalf u : Matrix (Fin 2) (Fin 2) R) =
      !![half * ((u : R) + (↑u⁻¹ : R)),
          -i * half * ((u : R) - (↑u⁻¹ : R));
        -(-i * half * ((u : R) - (↑u⁻¹ : R))),
          half * ((u : R) + (↑u⁻¹ : R))] :=
  (rfl)

/-- Extracting the unit from its two-dimensional special orthogonal matrix recovers the unit. -/
@[simp]
theorem finTwoToUnit_finTwoOfUnit (i half : R) (hi : i ^ 2 = -1)
    (hhalf : 2 * half = 1) (u : Rˣ) :
    finTwoToUnit i hi (finTwoOfUnit i half hi hhalf u) = u := by
  apply Units.ext
  rw [coe_finTwoToUnit, finTwoOfUnit]
  norm_num [Matrix.of_apply]
  calc
    half * ((u : R) + (↑u⁻¹ : R)) +
        -(i * (i * half * ((u : R) - (↑u⁻¹ : R)))) =
      half * ((u : R) + (↑u⁻¹ : R)) -
        i ^ 2 * half * ((u : R) - (↑u⁻¹ : R)) := by ring
    _ = (2 * half) * (u : R) := by rw [hi]; ring
    _ = u := by rw [hhalf, one_mul]

/-- Reconstructing a two-dimensional special orthogonal matrix from its unit recovers the
matrix. -/
@[simp]
theorem finTwoOfUnit_finTwoToUnit (i half : R) (hi : i ^ 2 = -1)
    (hhalf : 2 * half = 1) (M : Matrix.specialOrthogonalGroup (Fin 2) R) :
    finTwoOfUnit i half hi hhalf (finTwoToUnit i hi M) = M := by
  apply Subtype.ext
  have hM := Matrix.mem_specialOrthogonalGroup_fin_two_iff.mp M.2
  have hM10 : M.val 1 0 = -M.val 0 1 := by
    simpa only [neg_neg] using (congrArg Neg.neg hM.2.1).symm
  rw [finTwoOfUnit]
  simp only [coe_inv_finTwoToUnit, coe_finTwoToUnit]
  ext j k
  fin_cases j
  · fin_cases k
    · norm_num [Matrix.of_apply]
      calc
        half * (M.val 0 0 + M.val 0 0) = (2 * half) * M.val 0 0 := by ring
        _ = M.val 0 0 := by rw [hhalf, one_mul]
    · norm_num [Matrix.of_apply]
      calc
        -(i * half * (i * M.val 0 1 + i * M.val 0 1)) =
            -(i ^ 2) * (2 * half) * M.val 0 1 := by ring
        _ = M.val 0 1 := by rw [hi, hhalf]; ring
  · fin_cases k
    · norm_num [Matrix.of_apply]
      rw [hM10]
      calc
        i * half * (i * M.val 0 1 + i * M.val 0 1) =
            i ^ 2 * (2 * half) * M.val 0 1 := by ring
        _ = -M.val 0 1 := by rw [hi, hhalf]; ring
    · norm_num [Matrix.of_apply]
      rw [← hM.1]
      calc
        half * (M.val 0 0 + M.val 0 0) = (2 * half) * M.val 0 0 := by ring
        _ = M.val 0 0 := by rw [hhalf, one_mul]

/-- Multiplication of two-dimensional special orthogonal matrices becomes multiplication of
their associated units. -/
theorem finTwoToUnit_mul (i : R) (hi : i ^ 2 = -1)
    (M N : Matrix.specialOrthogonalGroup (Fin 2) R) :
    finTwoToUnit i hi (M * N) = finTwoToUnit i hi M * finTwoToUnit i hi N := by
  apply Units.ext
  rw [Units.val_mul, coe_finTwoToUnit, coe_finTwoToUnit, coe_finTwoToUnit]
  have hN := Matrix.mem_specialOrthogonalGroup_fin_two_iff.mp N.2
  have hN11 : N.val 1 1 = N.val 0 0 := hN.1.symm
  have hN10 : N.val 1 0 = -N.val 0 1 := by
    simpa only [neg_neg] using (congrArg Neg.neg hN.2.1).symm
  simp only [Submonoid.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  rw [hN11, hN10]
  calc
    (M.val 0 0 * N.val 0 0 + M.val 0 1 * -N.val 0 1) +
        i * (M.val 0 0 * N.val 0 1 + M.val 0 1 * N.val 0 0) =
      (M.val 0 0 + i * M.val 0 1) * (N.val 0 0 + i * N.val 0 1) := by
        apply sub_eq_zero.mp
        calc
          ((M.val 0 0 * N.val 0 0 + M.val 0 1 * -N.val 0 1) +
                i * (M.val 0 0 * N.val 0 1 + M.val 0 1 * N.val 0 0)) -
              (M.val 0 0 + i * M.val 0 1) * (N.val 0 0 + i * N.val 0 1) =
            -(i ^ 2 + 1) * M.val 0 1 * N.val 0 1 := by ring
          _ = 0 := by rw [hi]; ring

/-- The two-dimensional matrix attached to a unit is natural under ring homomorphisms. -/
theorem map_finTwoOfUnit {S : Type*} [CommRing S] (f : R →+* S)
    (i half : R) (hi : i ^ 2 = -1) (hhalf : 2 * half = 1) (u : Rˣ) :
    map f (finTwoOfUnit i half hi hhalf u) =
      finTwoOfUnit (f i) (f half)
        (by simpa only [map_pow, map_neg, map_one] using congrArg f hi)
        (by simpa only [map_ofNat, map_mul, map_one] using congrArg f hhalf)
        (Units.map f u) := by
  apply Subtype.ext
  rw [coe_map, finTwoOfUnit, finTwoOfUnit]
  ext j k
  fin_cases j
  · fin_cases k <;> norm_num [Matrix.of_apply, Units.coe_map]
  · fin_cases k <;> norm_num [Matrix.of_apply, Units.coe_map]

/-- The unit attached to a two-dimensional matrix is natural under ring homomorphisms. -/
theorem finTwoToUnit_map {S : Type*} [CommRing S] (f : R →+* S)
    (i : R) (hi : i ^ 2 = -1) (M : Matrix.specialOrthogonalGroup (Fin 2) R) :
    finTwoToUnit (f i)
        (by simpa only [map_pow, map_neg, map_one] using congrArg f hi) (map f M) =
      Units.map f (finTwoToUnit i hi M) := by
  apply Units.ext
  simp only [coe_finTwoToUnit, coe_map, Matrix.map_apply, Units.coe_map]
  calc
    f (M.val 0 0) + f i * f (M.val 0 1) =
        f (M.val 0 0) + f (i * M.val 0 1) := by rw [map_mul]
    _ = f (M.val 0 0 + i * M.val 0 1) := (map_add f _ _).symm

/-- Over a commutative ring containing a square root of `-1` and a half, the standard
two-dimensional special orthogonal group is the group of units. -/
noncomputable def finTwoMulEquivUnits (i half : R) (hi : i ^ 2 = -1)
    (hhalf : 2 * half = 1) : Matrix.specialOrthogonalGroup (Fin 2) R ≃* Rˣ where
  toFun := finTwoToUnit i hi
  invFun := finTwoOfUnit i half hi hhalf
  left_inv := finTwoOfUnit_finTwoToUnit i half hi hhalf
  right_inv := finTwoToUnit_finTwoOfUnit i half hi hhalf
  map_mul' := finTwoToUnit_mul i hi

/-- The explicit equivalence from two-dimensional special orthogonal matrices to units is given
by `finTwoToUnit`. -/
@[simp]
theorem finTwoMulEquivUnits_apply (i half : R) (hi : i ^ 2 = -1)
    (hhalf : 2 * half = 1) (M : Matrix.specialOrthogonalGroup (Fin 2) R) :
    finTwoMulEquivUnits i half hi hhalf M = finTwoToUnit i hi M :=
  (rfl)

/-- The inverse of the explicit equivalence from two-dimensional special orthogonal matrices to
units is given by `finTwoOfUnit`. -/
@[simp]
theorem finTwoMulEquivUnits_symm_apply (i half : R) (hi : i ^ 2 = -1)
    (hhalf : 2 * half = 1) (u : Rˣ) :
    (finTwoMulEquivUnits i half hi hhalf).symm u = finTwoOfUnit i half hi hhalf u :=
  (rfl)

/-- The unit `1` determines the identity two-dimensional special orthogonal matrix. -/
@[simp]
theorem finTwoOfUnit_one (i half : R) (hi : i ^ 2 = -1) (hhalf : 2 * half = 1) :
    finTwoOfUnit i half hi hhalf 1 = 1 :=
  (finTwoMulEquivUnits i half hi hhalf).symm.map_one

end Matrix.SpecialOrthogonalGroup
