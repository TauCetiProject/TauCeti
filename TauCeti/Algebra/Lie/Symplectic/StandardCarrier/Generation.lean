/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Symplectic.StandardCarrier.IntegralMatrix
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Basic

/-!
# Numbered root-subgroup matrix identifications of the type-`C` carrier

`TauCeti.SpStd.groupScheme n` is the explicit full-weight Chevalley carrier of type `C_(n+1)`, the
smallest closed subgroup scheme of `GL_(2n+2)` containing the divided-power exponentials of the
Bourbaki-numbered Chevalley generators together with the weight torus of the standard lattice.
`TauCeti.SpStd.mem_GLSymplecticFin_of_mem_points` is the containment in one direction, that every
point of the carrier preserves the standard alternating form. This file identifies the carrier's
four families of numbered simple-root points with the corresponding elementary generators of
`TauCeti.GLSymplecticFin` over every commutative ring.

## The numbered root subgroups

Each numbered root generator squares to zero in the standard representation, so its divided-power
exponential is `1 + u X` for `X` the integral matrix `TauCeti.SpStd.rootIntMatrix` of the
generator, which `AlternatingForm.lean` computes in the enumerated coordinate basis: the single
unit `E_{i,m+i}` at the final node, the difference `E_{i,i+1} - E_{m+i+1,m+i}` of two units at a
nonfinal one. Those are the matrices of the symplectic group's long-root transvection at the
terminal coordinate and of its difference short-root element at an adjacent pair, so the carrier's
four families of numbered root points are the corresponding elements of `TauCeti.GLSymplecticFin`,
and the terminal coordinate is what makes them the Bourbaki simple roots of type `C`.

## What is not proved

Only the identifications of the numbered root points are proved here. Using these four equations
together with `TauCeti.GLSymplecticFin.eq_top_of_adjacent_of_long`,
`TauCeti.Algebra.Lie.Symplectic.StandardCarrier.Symplectic.Basic` establishes the equality of
defining Hopf ideals over `ℤ` and the canonical commutative-ring point-group equality and
equivalence `TauCeti.SpStd.points_eq_GLSymplecticFin` and
`TauCeti.SpStd.pointsMulEquivGLSymplecticFin`. Nothing below asserts that the carrier is reductive,
that its weight torus is maximal, or that the two group *schemes* agree.

## Main results

* `TauCeti.SpStd.rootSubgroupPoints_inl_last_eq_positiveLongRootTransvectionUnit` and its three
  siblings: each numbered root point is the corresponding long-root transvection or difference
  short-root element of the symplectic group, over every commutative ring.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §§4.4 and 11.3.
* R. Steinberg, *Lectures on Chevalley Groups*, §3.
-/
public section

open Matrix

namespace TauCeti.SpStd

universe v

variable (n : ℕ)

variable {A : Type v} [CommRing A]

/-- The final raising point of the carrier is the positive long-root transvection. -/
@[simp]
theorem rootSubgroupPoints_inl_last_eq_positiveLongRootTransvectionUnit (u : Multiplicative A) :
    (rootSubgroupPoints n (.inl (Fin.last n)) A u :
        Matrix.GeneralLinearGroup (Fin ((n + 1) + (n + 1))) A) =
      ((GLSymplecticFin.positiveLongRootTransvectionUnit (Fin.last n)
        (Multiplicative.toAdd u) : GLSymplecticFin (n + 1) A) :
          GL (Fin ((n + 1) + (n + 1))) A) := by
  apply Units.ext
  rw [coe_rootSubgroupPoints_eq_one_add_smul, rootIntMatrix_inl_last,
    GLSymplecticFin.coe_positiveLongRootTransvectionUnit, coe_transvectionUnit]
  ext r s
  simp [Matrix.transvection, Matrix.single_apply]

/-- The final lowering point of the carrier is the negative long-root transvection. -/
@[simp]
theorem rootSubgroupPoints_inr_last_eq_negativeLongRootTransvectionUnit (u : Multiplicative A) :
    (rootSubgroupPoints n (.inr (Fin.last n)) A u :
        Matrix.GeneralLinearGroup (Fin ((n + 1) + (n + 1))) A) =
      ((GLSymplecticFin.negativeLongRootTransvectionUnit (Fin.last n)
        (Multiplicative.toAdd u) : GLSymplecticFin (n + 1) A) :
          GL (Fin ((n + 1) + (n + 1))) A) := by
  apply Units.ext
  rw [coe_rootSubgroupPoints_eq_one_add_smul, rootIntMatrix_inr_last,
    GLSymplecticFin.coe_negativeLongRootTransvectionUnit, coe_transvectionUnit]
  ext r s
  simp [Matrix.transvection, Matrix.single_apply]

/-- A nonfinal raising point of the carrier is the difference short-root element. -/
@[simp]
theorem rootSubgroupPoints_inl_eq_differenceShortRootUnit_of_ne_last (i : Fin (n + 1))
    (hi : i ≠ Fin.last n)
    (u : Multiplicative A) :
    (rootSubgroupPoints n (.inl i) A u :
        Matrix.GeneralLinearGroup (Fin ((n + 1) + (n + 1))) A) =
      ((GLSymplecticFin.differenceShortRootUnit (Order.lt_succ_iff_ne_top.2 hi).ne
        (Multiplicative.toAdd u) : GLSymplecticFin (n + 1) A) :
          GL (Fin ((n + 1) + (n + 1))) A) := by
  apply Units.ext
  rw [coe_rootSubgroupPoints_eq_one_add_smul, rootIntMatrix_inl_of_ne_last n i hi,
    GLSymplecticFin.coe_differenceShortRootUnit_eq_one_add_single_sub_single]
  ext r s
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.map_apply,
    Matrix.single_apply, smul_eq_mul, Int.cast_ite, Int.cast_one, Int.cast_zero, Int.cast_sub,
    mul_sub, mul_ite, mul_one, mul_zero]
  split_ifs <;> ring

/-- A nonfinal lowering point of the carrier is the opposite difference short-root element. -/
@[simp]
theorem rootSubgroupPoints_inr_eq_differenceShortRootUnit_of_ne_last (i : Fin (n + 1))
    (hi : i ≠ Fin.last n)
    (u : Multiplicative A) :
    (rootSubgroupPoints n (.inr i) A u :
        Matrix.GeneralLinearGroup (Fin ((n + 1) + (n + 1))) A) =
      ((GLSymplecticFin.differenceShortRootUnit (Order.lt_succ_iff_ne_top.2 hi).ne'
        (Multiplicative.toAdd u) : GLSymplecticFin (n + 1) A) :
          GL (Fin ((n + 1) + (n + 1))) A) := by
  apply Units.ext
  rw [coe_rootSubgroupPoints_eq_one_add_smul, rootIntMatrix_inr_of_ne_last n i hi,
    GLSymplecticFin.coe_differenceShortRootUnit_eq_one_add_single_sub_single]
  ext r s
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.map_apply,
    Matrix.single_apply, smul_eq_mul, Int.cast_ite, Int.cast_one, Int.cast_zero, Int.cast_sub,
    mul_sub, mul_ite, mul_one, mul_zero]
  split_ifs <;> ring

end TauCeti.SpStd
