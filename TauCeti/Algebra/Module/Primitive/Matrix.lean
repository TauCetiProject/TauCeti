/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Primitive.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
import TauCeti.LinearAlgebra.Basis.Basic

/-!
# Detecting an integral operator by its matrix entries

If the image of an integral linear map contains a primitive vector, its matrix entries
have an integral linear combination equal to one. This supplies coefficients that recover
scalar multiples of the operator over every commutative value ring.
-/

public section

namespace LinearMap

/-- The matrix entries of an integral linear map whose image contains a primitive vector
have an integral linear combination equal to one. -/
theorem exists_sum_smul_toMatrix_eq_one_of_isPrimitive
    {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    {η κ : Type*} [Fintype η] [Fintype κ] [DecidableEq η]
    (f : M →ₗ[ℤ] N) (b : Module.Basis η ℤ M) (d : Module.Basis κ ℤ N) (m : M)
    (hm : TauCeti.IsPrimitive (f m)) :
    ∃ c : κ → η → ℤ, ∑ s, ∑ r, c r s • toMatrix b d f r s = 1 := by
  obtain ⟨ℓ, hℓ⟩ := TauCeti.isPrimitive_def.mp hm
  refine ⟨fun r s ↦ ℓ (d r) * b.repr m s, ?_⟩
  simp only [toMatrix_apply, zsmul_eq_mul, Int.cast_id]
  calc
    _ = ∑ s, b.repr m s * ∑ r, d.repr (f (b s)) r * ℓ (d r) := by
      simp_rw [Finset.mul_sum]
      congr 1
      ext s
      congr 1
      ext r
      ring
    _ = ∑ s, b.repr m s * ℓ (f (b s)) := by
      congr 1
      ext s
      simpa only [zsmul_eq_mul, Int.cast_id] using
        congrArg (b.repr m s * ·) (d.apply_eq_sum_repr_zsmul ℓ (f (b s))).symm
    _ = ℓ (f m) := by
      simpa only [LinearMap.comp_apply, zsmul_eq_mul, Int.cast_id] using
        (b.apply_eq_sum_repr_zsmul (ℓ.comp f) m).symm
    _ = 1 := hℓ

end LinearMap
