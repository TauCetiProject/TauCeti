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
@[simp]
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
  have htransport : Orientation.map ι f x = Orientation.map ι g x ↔
      Orientation.map ι (f.trans g.symm) x = x := by
    rw [map_trans, ← map_symm, Equiv.symm_apply_eq]
  have hdet : LinearMap.det (f.trans g.symm : M →ₗ[R] M) =
      LinearMap.det (f : M →ₗ[R] M) / LinearMap.det (g : M →ₗ[R] M) := by
    simp [← LinearEquiv.coe_det, LinearEquiv.det_trans, LinearEquiv.det_symm,
      div_eq_mul_inv, mul_comm]
  rw [htransport, map_eq_iff_det_pos _ _ h, hdet]
  exact div_pos_iff.trans mul_pos_iff.symm

end Field
