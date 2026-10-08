/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.LinearAlgebra.Orientation

/-!
# Transporting orientations along linear equivalences

Two facts about `Orientation.map`, the transport of orientations along a linear equivalence:
it is compatible with composition of equivalences, and two self-equivalences of a
finite-dimensional space transport an orientation to the same orientation exactly when their
determinants have the same sign.

## Main results

* `Orientation.map_trans`: transport along a composite is the composite of the transports.
* `Orientation.map_eq_map_iff_det_mul_pos`: `f` and `g` transport `x` to the same orientation
  if and only if `0 < det f * det g`.
-/

public section

open Module

section CommSemiring

variable {R : Type*} [CommSemiring R] [PartialOrder R] [IsStrictOrderedRing R]
  {M N P : Type*} [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
  [AddCommMonoid P] [Module R P] {ι : Type*}

/-- Transporting an orientation along a composite of linear equivalences is the same as
transporting it along each in turn. -/
theorem Orientation.map_trans (e : M ≃ₗ[R] N) (f : N ≃ₗ[R] P) (x : Orientation R M ι) :
    Orientation.map ι (e.trans f) x = Orientation.map ι f (Orientation.map ι e x) := by
  induction x using Module.Ray.ind with | h v hv => rfl

end CommSemiring

section Field

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  {M : Type*} [AddCommGroup M] [Module R M] {ι : Type*} [Fintype ι]

/-- When the index type has cardinality equal to the finite dimension, two self-equivalences
transport an orientation to the same orientation if and only if their determinants have the same
sign. -/
theorem Orientation.map_eq_map_iff_det_mul_pos [FiniteDimensional R M] (x : Orientation R M ι)
    (f g : M ≃ₗ[R] M) (h : Fintype.card ι = finrank R M) :
    Orientation.map ι f x = Orientation.map ι g x ↔
      0 < LinearMap.det (f : M →ₗ[R] M) * LinearMap.det (g : M →ₗ[R] M) := by
  rw [map_eq_det_inv_smul _ _ h, map_eq_det_inv_smul _ _ h,
    ← smul_left_cancel_iff (LinearEquiv.det g), smul_inv_smul, smul_smul, units_smul_eq_self_iff,
    Units.val_mul, Units.val_inv_eq_inv_val, ← div_eq_mul_inv, div_pos_iff, mul_pos_iff,
    LinearEquiv.coe_det, LinearEquiv.coe_det]
  tauto

end Field
