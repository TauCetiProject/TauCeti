/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Ring.Ultra
public import Mathlib.Analysis.Normed.Ring.Units
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.Jacobson.Ideal

import Mathlib.RingTheory.Henselian

/-!
# Neumann inversion in ultrametric normed rings

This file gives the sharp form of the Neumann-series estimate in an ultrametric normed ring
with summable geometric series (in particular, in a complete normed ring). If `‖x‖ < 1`, then
both `(1 - x)⁻¹` and `1 - x` have norm one, while `‖(1 - x)⁻¹ - 1‖ = ‖x‖`. The equalities
use only submultiplicativity of the norm, not a multiplicative norm.

For an ultrametric commutative ring, the elements of norm less than one form an ideal in the
closed unit-ball subring. The sharp Neumann estimates show that this ideal lies in the Jacobson
radical, so units lift across reduction by it. When the ambient ring is a normed field, the ideal
is maximal and the reduction is a field.

These results are the normed-ring input for perturbative arguments over Banach--Tate rings.
-/

public section

namespace Ideal

/-- The open unit ball as an ideal of the closed unit-ball subring of an ultrametric
commutative ring. -/
def unitOpenBall (R : Type*) [SeminormedCommRing R] [NormOneClass R] [IsUltrametricDist R] :
    Ideal (Subring.unitClosedBall R) where
  carrier := {x | ‖(x : R)‖ < 1}
  zero_mem' := by simp
  add_mem' {x y} hx hy := by
    exact (IsUltrametricDist.norm_add_le_max (x : R) y).trans_lt (max_lt hx hy)
  smul_mem' x y hy := by
    calc
      ‖((x * y : Subring.unitClosedBall R) : R)‖ ≤ ‖(x : R)‖ * ‖(y : R)‖ :=
        norm_mul_le _ _
      _ ≤ 1 * ‖(y : R)‖ := mul_le_mul_of_nonneg_right
        (Subring.mem_unitClosedBall.mp x.property) (norm_nonneg _)
      _ < 1 := by simpa using hy

/-- Membership in the open unit-ball ideal means that the ambient norm is less than one. -/
@[simp]
theorem mem_unitOpenBall {R : Type*} [SeminormedCommRing R] [NormOneClass R]
    [IsUltrametricDist R] {x : Subring.unitClosedBall R} :
    x ∈ unitOpenBall R ↔ ‖(x : R)‖ < 1 :=
  Iff.rfl

end Ideal

namespace TauCeti

section Neumann

variable {R : Type*} [NormedRing R] [NormOneClass R] [IsUltrametricDist R]

/-- An element strictly smaller than one does not change the norm of one when subtracted. -/
theorem norm_one_sub_of_norm_lt_one {x : R} (hx : ‖x‖ < 1) : ‖1 - x‖ = 1 := by
  rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm]
  · simp [hx.le]
  · exact ne_of_gt (by simpa using hx)

variable [HasSummableGeomSeries R]

/-- The inverse of `1 - x` has norm one when `‖x‖ < 1`.

This is stronger than the usual archimedean geometric-series bound. -/
theorem norm_inv_one_sub_of_norm_lt_one {x : R} (hx : ‖x‖ < 1) :
    ‖(((Units.oneSub x hx)⁻¹ : Rˣ) : R)‖ = 1 := by
  let u := Units.oneSub x hx
  have hu : ((u⁻¹ : Rˣ) : R) = ∑' n : ℕ, x ^ n := rfl
  apply le_antisymm
  · rw [hu]
    apply IsUltrametricDist.norm_tsum_le_of_forall_le
    intro n
    calc
      ‖x ^ n‖ ≤ ‖x‖ ^ n := norm_pow_le _ n
      _ ≤ 1 := pow_le_one₀ (norm_nonneg x) hx.le
  · have hmul : (1 - x) * ((u⁻¹ : Rˣ) : R) = 1 := by
      simp [u]
    calc
      1 = ‖(1 : R)‖ := norm_one.symm
      _ = ‖(1 - x) * ((u⁻¹ : Rˣ) : R)‖ := congrArg norm hmul.symm
      _ ≤ ‖1 - x‖ * ‖((u⁻¹ : Rˣ) : R)‖ := norm_mul_le _ _
      _ = ‖((u⁻¹ : Rˣ) : R)‖ := by rw [norm_one_sub_of_norm_lt_one hx, one_mul]

/-- The displacement of the Neumann inverse from one has exactly the norm of the original
perturbation. -/
theorem norm_inv_one_sub_sub_one {x : R} (hx : ‖x‖ < 1) :
    ‖(((Units.oneSub x hx)⁻¹ : Rˣ) : R) - 1‖ = ‖x‖ := by
  let u := Units.oneSub x hx
  have hinv : ‖((u⁻¹ : Rˣ) : R)‖ = 1 := norm_inv_one_sub_of_norm_lt_one hx
  apply le_antisymm
  · have hdiff : ((u⁻¹ : Rˣ) : R) - 1 = ((u⁻¹ : Rˣ) : R) * x := by
      calc
        ((u⁻¹ : Rˣ) : R) - 1 = ((u⁻¹ : Rˣ) : R) * 1 -
            ((u⁻¹ : Rˣ) : R) * (u : R) := by simp
        _ = ((u⁻¹ : Rˣ) : R) * (1 - (u : R)) := by rw [mul_sub]
        _ = ((u⁻¹ : Rˣ) : R) * x := by simp [u]
    rw [hdiff]
    exact (norm_mul_le _ _).trans_eq (by rw [hinv, one_mul])
  · have hrecover : (1 - x) * (((u⁻¹ : Rˣ) : R) - 1) = x := by
      have hmul : (u : R) * ((u⁻¹ : Rˣ) : R) = 1 := Units.mul_inv u
      calc
        (1 - x) * (((u⁻¹ : Rˣ) : R) - 1) =
            (u : R) * (((u⁻¹ : Rˣ) : R) - 1) := by rfl
        _ = (u : R) * ((u⁻¹ : Rˣ) : R) - (u : R) * 1 := by rw [mul_sub]
        _ = 1 - (u : R) := by rw [hmul, mul_one]
        _ = x := by simp [u]
    calc
      ‖x‖ = ‖(1 - x) * (((u⁻¹ : Rˣ) : R) - 1)‖ := congrArg norm hrecover.symm
      _ ≤ ‖1 - x‖ * ‖((u⁻¹ : Rˣ) : R) - 1‖ := norm_mul_le _ _
      _ = ‖((u⁻¹ : Rˣ) : R) - 1‖ := by rw [norm_one_sub_of_norm_lt_one hx, one_mul]

end Neumann

end TauCeti

namespace Ideal

section UnitOpenBall

variable {R : Type*} [NormedCommRing R] [NormOneClass R] [IsUltrametricDist R]
  [HasSummableGeomSeries R]

private theorem isUnit_one_sub_of_norm_lt_one (x : Subring.unitClosedBall R)
    (hx : ‖(x : R)‖ < 1) : IsUnit (1 - x) := by
  let u := Units.oneSub (x : R) hx
  have hinv : ‖((u⁻¹ : Rˣ) : R)‖ = 1 := TauCeti.norm_inv_one_sub_of_norm_lt_one hx
  let v : (Subring.unitClosedBall R)ˣ :=
    { val := 1 - x
      inv := ⟨((u⁻¹ : Rˣ) : R), by simp [hinv]⟩
      val_inv := by
        ext
        exact Units.mul_inv u
      inv_val := by
        ext
        exact Units.inv_mul u }
  exact v.isUnit

/-- The open unit-ball ideal lies in the Jacobson radical of the closed unit-ball subring. -/
theorem unitOpenBall_le_jacobson :
    unitOpenBall R ≤ jacobson (⊥ : Ideal (Subring.unitClosedBall R)) := by
  intro x hx
  rw [mem_jacobson_bot]
  intro y
  have hy : ‖(y : R)‖ ≤ 1 :=
    (Subring.mem_unitClosedBall (R := R) (x := (y : R))).mp y.property
  have hxy : ‖((x * y : Subring.unitClosedBall R) : R)‖ < 1 := by
    calc
      ‖((x * y : Subring.unitClosedBall R) : R)‖ ≤ ‖(x : R)‖ * ‖(y : R)‖ :=
        norm_mul_le _ _
      _ ≤ ‖(x : R)‖ * 1 := mul_le_mul_of_nonneg_left hy (norm_nonneg _)
      _ < 1 := by simpa using hx
  simpa [sub_eq_add_neg, add_comm] using
    isUnit_one_sub_of_norm_lt_one (R := R) (-(x * y)) (by simpa using hxy)

/-- Reduction modulo the open unit ball reflects units. This is the unit-lifting property of
the closed unit-ball subring. -/
theorem isUnit_quotient_mk_unitOpenBall_iff (x : Subring.unitClosedBall R) :
    IsUnit (Quotient.mk (unitOpenBall R) x) ↔ IsUnit x := by
  let _ := isLocalHom_of_le_jacobson_bot (unitOpenBall R) unitOpenBall_le_jacobson
  exact isUnit_map_iff (Quotient.mk (unitOpenBall R)) x

end UnitOpenBall

section Field

variable (K : Type*) [NormedField K] [IsUltrametricDist K]

/-- Over a normed field, the open unit ball is the maximal ideal of the closed unit-ball
subring. -/
theorem isMaximal_unitOpenBall : (unitOpenBall K).IsMaximal := by
  rw [isMaximal_iff]
  constructor
  · simp
  · intro J x hIJ hx hxJ
    have hxnorm : ‖(x : K)‖ = 1 :=
      le_antisymm (Subring.mem_unitClosedBall.mp x.property) (not_lt.mp hx)
    have hx0 : (x : K) ≠ 0 := norm_ne_zero_iff.mp (by simp [hxnorm])
    have hinvnorm : ‖(x : K)⁻¹‖ ≤ 1 := by simp [hxnorm]
    let u : (Subring.unitClosedBall K)ˣ :=
      { val := x
        inv := ⟨(x : K)⁻¹, Subring.mem_unitClosedBall.mpr hinvnorm⟩
        val_inv := by ext; exact mul_inv_cancel₀ hx0
        inv_val := by ext; exact inv_mul_cancel₀ hx0 }
    exact (Ideal.eq_top_iff_one J).mp (J.eq_top_of_isUnit_mem hxJ u.isUnit)

/-- The reduction of the closed unit ball of an ultrametric normed field by its open unit ball
is a field. -/
theorem isField_quotient_unitOpenBall :
    IsField (Subring.unitClosedBall K ⧸ unitOpenBall K) :=
  (Quotient.maximal_ideal_iff_isField_quotient (unitOpenBall K)).mp
    (isMaximal_unitOpenBall K)

end Field

end Ideal
