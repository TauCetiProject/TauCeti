/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Associator
public import Mathlib.Algebra.Module.Torsion.Basic
import TauCeti.Algebra.Module.Torsion.Basic

/-!
# Torsion as the kernel of multiplication on `M ⊗ R`

For an element `r` of a commutative semiring `R` and an `R`-module `M`, the right unitor
`M ⊗[R] R ≃ M` carries multiplication by `r` on the right factor to multiplication by `r` on `M`.
So the kernel of `(LinearMap.lsmul R R r).lTensor M` is the `r`-torsion `M[r]`
(`TauCeti.kerLTensorLsmulEquiv`). This identifies the cycles of the complex `M ⊗ R → M ⊗ R`,
which computes `Tor₁^R(M, R ⧸ (r))` when `r` is regular on `R`.
-/

public section

open Submodule TensorProduct

namespace TauCeti

variable {R : Type*} [CommSemiring R] (M : Type*) [AddCommMonoid M] [Module R M] (r : R)

/-- The right unitor `M ⊗[R] R ≃ M` intertwines `(LinearMap.lsmul R R r).lTensor M` with
multiplication by `r` on `M`. -/
theorem lTensor_lsmul_comp_rid_symm :
    (LinearMap.lsmul R R r).lTensor M ∘ₗ (TensorProduct.rid R M).symm.toLinearMap =
      (TensorProduct.rid R M).symm.toLinearMap ∘ₗ LinearMap.lsmul R M r :=
  LinearMap.ext fun x => by simpa using tmul_smul (R := R) r x (1 : R)

/-- The kernel of `x ⊗ s ↦ x ⊗ r s` on `M ⊗[R] R` is the `r`-torsion `M[r]` of `M`, through the
right unitor `M ⊗[R] R ≃ M`. -/
noncomputable def kerLTensorLsmulEquiv :
    LinearMap.ker ((LinearMap.lsmul R R r).lTensor M) ≃ₗ[R] torsionBy R M r :=
  (TensorProduct.rid R M).ofSubmodules _ _ <| by
    rw [map_equiv_eq_comap_symm, ← LinearMap.ker_comp, lTensor_lsmul_comp_rid_symm,
      LinearEquiv.ker_comp, torsionBy_eq_ker_lsmul]

@[simp]
theorem coe_kerLTensorLsmulEquiv_apply (x : LinearMap.ker ((LinearMap.lsmul R R r).lTensor M)) :
    (kerLTensorLsmulEquiv M r x : M) = TensorProduct.rid R M x :=
  LinearEquiv.ofSubmodules_apply _ _ x

@[simp]
theorem coe_kerLTensorLsmulEquiv_symm_apply (x : torsionBy R M r) :
    ((kerLTensorLsmulEquiv M r).symm x : M ⊗[R] R) = (x : M) ⊗ₜ 1 :=
  (LinearEquiv.ofSubmodules_symm_apply _ _ x).trans (TensorProduct.rid_symm_apply _)

end TauCeti
