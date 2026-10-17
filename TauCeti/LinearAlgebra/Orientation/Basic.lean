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

Orientation transport commutes with composition, and determinants characterize when transported
rays agree. Integral unit signs retain or reverse orientations; signed Jacobians determine their
compatibility under linear equivalences.

## Main results

* `Orientation.map_trans`: transport along a composite is the composite of the transports.
* `Orientation.map_eq_map_iff_det_mul_pos`: `f` and `g` transport `x` to the same orientation
  if and only if `0 < det f * det g`.
* `Orientation.intCast_units_smul_eq_ite`: an integer unit acts by retention or reversal.
* `Orientation.intCast_units_smul_injective`: the two signs give distinct orientations.
* `Orientation.map_units_smul_eq_iff_det_mul_pos`: the signed-Jacobian compatibility criterion.
* `Orientation.intCast_units_smul_ite_eq`: the relative sign reconstructs an orientation.
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

section CommRing

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
  {M : Type*} [AddCommGroup M] [Module R M] {ι : Type*}

/-- Integral unit signs act on orientations by retaining or reversing the ray. -/
theorem Orientation.intCast_units_smul_eq_ite (u : ℤˣ) (o : Orientation R M ι) :
    (Units.map (Int.castRingHom R).toMonoidHom u) • o = if u = 1 then o else -o := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · simp
  · rw [ite_eq_right (by decide)]
    exact Module.Ray.units_smul_of_neg _ (by norm_num) _

/-- Distinct integral unit signs induce distinct orientations. -/
theorem Orientation.intCast_units_smul_injective (o : Orientation R M ι) :
    Function.Injective (fun u : ℤˣ ↦ (Units.map (Int.castRingHom R).toMonoidHom u) • o) := by
  intro u v huv
  simp only [intCast_units_smul_eq_ite] at huv
  rcases Int.units_eq_one_or u with rfl | rfl <;>
    rcases Int.units_eq_one_or v with rfl | rfl <;>
    simp_all [Module.Ray.ne_neg_self, (Module.Ray.ne_neg_self o).symm]

end CommRing

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

/-- The signed Jacobian criterion for transporting orientations with arbitrary unit scalars. -/
theorem Orientation.map_units_smul_eq_iff_det_mul_pos [FiniteDimensional R M]
    (o : Orientation R M ι) (A : M ≃ₗ[R] M) (u v : Rˣ)
    (hι : Fintype.card ι = finrank R M) :
    Orientation.map ι A (u • o) = v • o ↔
      0 < (u : R) * (v : R) * LinearMap.det A.toLinearMap := by
  rw [map_eq_det_inv_smul _ _ hι, ← inv_smul_eq_iff, ← mul_smul,
    ← mul_smul, units_smul_eq_self_iff]
  simp only [Units.val_mul, Units.val_inv_eq_inv_val, LinearEquiv.coe_det]
  have h := (div_pos_iff.trans mul_pos_iff.symm :
    0 < (u : R) / ((v : R) * LinearMap.det A.toLinearMap) ↔
      0 < (u : R) * ((v : R) * LinearMap.det A.toLinearMap))
  simpa only [div_eq_mul_inv, mul_inv_rev, mul_comm, mul_left_comm, mul_assoc] using h

open Classical in
/-- The sign distinguishing two orientations reconstructs the second from the first when
the index type has the dimension of the space. -/
theorem Orientation.intCast_units_smul_ite_eq [FiniteDimensional R M]
    (model o : Orientation R M ι) (hι : Fintype.card ι = finrank R M) :
    (Units.map (Int.castRingHom R).toMonoidHom (if o = model then 1 else -1)) • model = o := by
  rcases eq_or_eq_neg o model hι with h | h
  · simp [h]
  · rw [h]
    rw [ite_eq_right (Module.Ray.ne_neg_self model).symm]
    exact Module.Ray.units_smul_of_neg _ (by norm_num) _

end Field
