/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.InnerAutomorphism
public import TauCeti.LinearAlgebra.Matrix.Exponential.Truncated
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Matrices of nilpotent adjoint exponentials

`Module.Basis.toMatrixAlgEquiv_expAd` expresses the matrix of the inner automorphism
`exp(ad(t • e))` as `Matrix.expSeries` in the matrix of `ad e`. Any truncation degree
annihilating `ad e` suffices. This identifies adjoint exponentials with polynomial matrix
families in the scalar parameter, without assumptions on Cartan subalgebras or roots.
-/

public section

namespace Module.Basis

open LieAlgebra Matrix TauCeti

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]

section Exponential

variable [CharZero K] [LieAlgebra ℚ L]

/-- The truncated exponential series of the matrix of `ad e` is the matrix of `exp (ad (t • e))`,
once the truncation degree kills `ad e`. -/
theorem toMatrixAlgEquiv_expAd {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K L) {e : L} {d : ℕ} (hd : ad K L e ^ d = 0) (t : K)
    (ht : IsNilpotent (ad K L (t • e))) :
    LinearMap.toMatrixAlgEquiv b (expAd (t • e) ht).toLinearEquiv.toLinearMap =
      expSeries (LinearMap.toMatrixAlgEquiv b (ad K L e)) d t := by
  have hlin : (expAd (t • e) ht).toLinearEquiv.toLinearMap =
      ∑ k ∈ Finset.range d, ((k.factorial : K)⁻¹) • (t • ad K L e) ^ k := by
    ext y
    have hy : (ad K L (t • e) ^ d) y = 0 := by
      rw [map_smul, smul_pow, hd, smul_zero, LinearMap.zero_apply]
    simp only [LinearEquiv.coe_coe, LieEquiv.coe_toLinearEquiv, LinearMap.sum_apply,
      expAd_apply_eq_sum ht hy]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    have hq := ratCast_smul_eq ℚ K ((k.factorial : ℚ)⁻¹) (((t • ad K L e) ^ k) y)
    rw [Rat.cast_id] at hq
    rw [map_smul, hq, LinearMap.smul_apply, Rat.cast_inv, Rat.cast_natCast]
  rw [hlin, expSeries_def, map_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [map_smul, map_pow, map_smul, smul_pow, smul_smul, mul_comm]
  simp [Algebra.algebraMap_self]

end Exponential

end Module.Basis
