/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.GradedModule.TensorProduct

/-!
# The Koszul sign automorphism of a tensor product

The Koszul sign is often needed without exchanging the two factors, for example in the
pairing between a tensor product and the tensor product of its graded duals. This file
constructs the linear automorphism acting by `(-1)^(p*q)` on bidegree `(p,q)`, and proves
its evaluation formula, the corresponding inverse formula, and preservation of total degree.

The construction reuses the quadratic twist of an internal grading: the identity
`choose(p+q,2) = choose(p,2) + choose(q,2) + p*q` supplies the sign.
The convention follows E. Getzler and J. D. S. Jones, *A-infinity algebras and the cyclic
bar complex*, Section 1.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe u v w

namespace InternalGrading

section Signs

variable {R : Type u} [CommRing R]
variable {M : Type v} {N : Type w}
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- The Koszul sign automorphism of a graded tensor product. On bidegree `(p,q)` it
multiplies by `(-1)^(p*q)`, without interchanging the factors. -/
noncomputable def koszulTensorTwist (G : InternalGrading R M) (H : InternalGrading R N) :
    M ⊗[R] N ≃ₗ[R] M ⊗[R] N :=
  TensorProduct.congr G.quadraticTwistEquiv H.quadraticTwistEquiv ≪≫ₗ
    (G.tensorProduct H).quadraticTwistEquiv

/-- The sign automorphism evaluates to the Koszul sign on homogeneous pure tensors. -/
theorem koszulTensorTwist_tmul (G : InternalGrading R M) (H : InternalGrading R N)
    {p q : ℤ} {x : M} {y : N} (hx : x ∈ G.piece p) (hy : y ∈ H.piece q) :
    G.koszulTensorTwist H (x ⊗ₜ[R] y) =
      (p * q).negOnePow • (x ⊗ₜ[R] y) := by
  simp only [koszulTensorTwist, LinearEquiv.trans_apply, TensorProduct.congr_tmul,
    quadraticTwistEquiv_apply, G.quadraticTwist_apply_of_mem hx,
    H.quadraticTwist_apply_of_mem hy, TensorProduct.smul_tmul,
    TensorProduct.tmul_smul, map_smul]
  rw [(G.tensorProduct H).quadraticTwist_apply_of_mem (G.tmul_mem_tensorProduct H hx hy),
    negOnePow_quadraticExponent_add]
  simp only [smul_smul, ← Int.cast_mul, ← Units.val_mul]
  have hsign : (quadraticExponent q).negOnePow * ((quadraticExponent p).negOnePow *
      ((p * q).negOnePow * (quadraticExponent p).negOnePow *
        (quadraticExponent q).negOnePow)) = (p * q).negOnePow := by
    calc
      _ = (p * q).negOnePow *
          ((quadraticExponent p).negOnePow * (quadraticExponent p).negOnePow) *
          ((quadraticExponent q).negOnePow * (quadraticExponent q).negOnePow) := by ac_rfl
      _ = _ := by simp
  rw [hsign]
  simp only [Units.smul_def, Int.cast_smul_eq_zsmul]

/-- The inverse sign automorphism has the same value on homogeneous pure tensors. -/
theorem koszulTensorTwist_symm_tmul (G : InternalGrading R M) (H : InternalGrading R N)
    {p q : ℤ} {x : M} {y : N} (hx : x ∈ G.piece p) (hy : y ∈ H.piece q) :
    (G.koszulTensorTwist H).symm (x ⊗ₜ[R] y) =
      (p * q).negOnePow • (x ⊗ₜ[R] y) := by
  apply (G.koszulTensorTwist H).injective
  rw [LinearEquiv.apply_symm_apply, Units.smul_def, map_zsmul,
    G.koszulTensorTwist_tmul H hx hy, Units.smul_def, smul_smul,
    ← Units.val_mul, Int.units_mul_self]
  simp

/-- The Koszul sign automorphism preserves total degree. -/
theorem isHomogeneous_koszulTensorTwist (G : InternalGrading R M) (H : InternalGrading R N) :
    LinearMap.IsHomogeneous (G.koszulTensorTwist H).toLinearMap
      (G.tensorProduct H).piece (G.tensorProduct H).piece 0 := by
  have hG : LinearMap.IsHomogeneous G.quadraticTwistEquiv.toLinearMap G.piece G.piece 0 := by
    rw [LinearMap.isHomogeneous_def]
    intro p x hx
    simpa using G.quadraticTwist_mem_piece hx
  have hH : LinearMap.IsHomogeneous H.quadraticTwistEquiv.toLinearMap H.piece H.piece 0 := by
    rw [LinearMap.isHomogeneous_def]
    intro p y hy
    simpa using H.quadraticTwist_mem_piece hy
  have hT : LinearMap.IsHomogeneous (G.tensorProduct H).quadraticTwistEquiv.toLinearMap
      (G.tensorProduct H).piece (G.tensorProduct H).piece 0 := by
    rw [LinearMap.isHomogeneous_def]
    intro p z hz
    simpa using (G.tensorProduct H).quadraticTwist_mem_piece hz
  simpa [koszulTensorTwist, LinearEquiv.coe_trans] using hT.comp (hG.tensorProduct hH)

end Signs

end InternalGrading

end TauCeti
