/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Ring.Ultra
public import Mathlib.Analysis.Normed.Ring.Units
public import Mathlib.RingTheory.Jacobson.Ideal

import Mathlib.RingTheory.Henselian

/-!
# Neumann inversion in ultrametric normed rings

This file gives the sharp form of the Neumann-series estimate in an ultrametric normed ring
with summable geometric series (in particular, in a complete normed ring). If `‖x‖ < 1`, then
both `(1 - x)⁻¹` and `1 - x` have norm one, while `‖(1 - x)⁻¹ - 1‖ = ‖x‖`. The equalities
use only submultiplicativity of the norm, not a multiplicative norm.

The sharp Neumann estimates show that the open unit-ball ideal in the closed unit-ball subring
lies in the Jacobson radical, so units lift across reduction by it.

These results are the normed-ring input for perturbative arguments over Banach--Tate rings.
-/

public section

namespace TauCeti

/-- An element strictly smaller than one does not change the norm of one when subtracted. -/
theorem norm_one_sub_of_norm_lt_one {R : Type*} [SeminormedRing R] [NormOneClass R]
    [IsUltrametricDist R] {x : R} (hx : ‖x‖ < 1) : ‖1 - x‖ = 1 := by
  rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm]
  · simp [hx.le]
  · exact ne_of_gt (by simpa using hx)

section Neumann

variable {R : Type*} [NormedRing R] [NormOneClass R] [IsUltrametricDist R]

variable [HasSummableGeomSeries R]

/-- The inverse of `1 - x` has norm one when `‖x‖ < 1`.

This is stronger than the usual archimedean geometric-series bound. -/
theorem norm_inv_one_sub_of_norm_lt_one {x : R} (hx : ‖x‖ < 1) :
    ‖(((Units.oneSub x hx)⁻¹ : Rˣ) : R)‖ = 1 := by
  let u := Units.oneSub x hx
  have hu : ((u⁻¹ : Rˣ) : R) = ∑' n : ℕ, x ^ n := by
    rw [← NormedRing.inverse_one_sub x hx, ← geom_series_eq_inverse x hx]
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
      rw [show x = 1 - (u : R) by simp [u]]
      noncomm_ring [Units.inv_mul u]
    rw [hdiff]
    exact (norm_mul_le _ _).trans_eq (by rw [hinv, one_mul])
  · have hrecover : (1 - x) * (((u⁻¹ : Rˣ) : R) - 1) = x := by
      rw [show 1 - x = (u : R) by simp [u], show x = 1 - (u : R) by simp [u]]
      noncomm_ring [Units.mul_inv u]
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
  exact Subring.isUnit_unitClosedBall_of_inverse (y := ((u⁻¹ : Rˣ) : R)) (by simp [hinv])
    (by simp [u]) (by simp [u])

/-- The open unit-ball ideal lies in the Jacobson radical of the closed unit-ball subring. -/
theorem unitOpenBall_le_jacobson :
    unitOpenBall R ≤ jacobson (⊥ : Ideal (Subring.unitClosedBall R)) := by
  intro x hx
  rw [mem_jacobson_bot]
  intro y
  simpa [sub_eq_add_neg, add_comm] using
    isUnit_one_sub_of_norm_lt_one (R := R) (-(x * y))
      (mem_unitOpenBall.mp
        ((unitOpenBall R).neg_mem ((unitOpenBall R).mul_mem_right y hx)))

/-- Reduction modulo the open unit ball is a local ring homomorphism. -/
instance isLocalHom_quotientMk_unitOpenBall :
    IsLocalHom (Quotient.mk (unitOpenBall R)) :=
  isLocalHom_of_le_jacobson_bot _ unitOpenBall_le_jacobson

/-- Reduction modulo the open unit ball reflects units. This is the unit-lifting property of
the closed unit-ball subring. -/
theorem isUnit_quotient_mk_unitOpenBall_iff (x : Subring.unitClosedBall R) :
    IsUnit (Quotient.mk (unitOpenBall R) x) ↔ IsUnit x := by
  exact isUnit_map_iff (Quotient.mk (unitOpenBall R)) x

end UnitOpenBall

end Ideal
