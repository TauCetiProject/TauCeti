/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.Transvection.Basic

/-!
# Powers of Eichler transvections

Powers of `E_{u,w}` are obtained by multiplying its parameter by the exponent. This is the
one-parameter subgroup law of `QuadraticMap.transvectionHom`, read on representatives. In
particular, the nonnegative powers of a rational transvection have uniformly controlled
integrality at finite places.
-/

public section

namespace TauCeti
namespace QuadraticMap

open _root_.QuadraticMap

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  {Q : QuadraticForm R M} {u w : M}

/-- The `n`th power of an Eichler transvection is the transvection with parameter `n • w`. -/
@[simp]
theorem transvection_pow (hu : Q u = 0) (huw : polar Q u w = 0) (n : ℕ) :
    transvection Q hu huw ^ n = transvection Q (w := n • w) hu
      (by simp [← Nat.cast_smul_eq_nsmul R, polar_smul_right, huw]) := by
  have h := congrArg (fun x : Additive (specialOrthogonalGroup Q) ↦
      ((Additive.toMul x : specialOrthogonalGroup Q) : M ≃ₗ[R] M))
    (map_nsmul (transvectionHom Q hu) n
      (Submodule.Quotient.mk ⟨w, by simpa only [LinearMap.mem_ker, polarBilin_apply_apply]
        using huw⟩))
  simp only [← Nat.cast_smul_eq_nsmul R, ← Submodule.Quotient.mk_smul,
    SetLike.mk_smul_mk, toMul_nsmul, Subgroup.coe_pow] at h
  rw [coe_transvectionHom_mk hu (by simp [polar_smul_right, huw]),
    coe_transvectionHom_mk hu huw] at h
  simpa only [Nat.cast_smul_eq_nsmul] using h.symm

end QuadraticMap
end TauCeti
