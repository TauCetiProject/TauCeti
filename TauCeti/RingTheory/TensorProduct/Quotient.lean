/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# Tensor products of quotient algebras

Quotienting both factors of a tensor product is the same as quotienting the tensor product
by the sum of the two extended ideals. This is the algebra analogue of Mathlib's linear
`TensorProduct.quotientTensorQuotientEquiv`, and the finite-level comparison used when
completing both factors simultaneously. The construction uses
`Algebra.TensorProduct.map_ker` and `Ideal.quotientKerAlgEquivOfSurjective`.
-/

public section

open TensorProduct

namespace Algebra.TensorProduct

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra A C]

/-- The tensor product of two quotient algebras is the quotient by the sum of the extended
ideals. The equivalence sends the tensor of two residue classes to the class of their tensor. -/
noncomputable def quotientTensorQuotientEquiv (I : Ideal B) (J : Ideal C) :
    (B ⧸ I) ⊗[A] (C ⧸ J) ≃ₐ[A]
      (B ⊗[A] C) ⧸ (I.map (includeLeft : B →ₐ[A] B ⊗[A] C) ⊔
        J.map (includeRight : C →ₐ[A] B ⊗[A] C)) := by
  exact ((Ideal.quotientEquivAlgOfEq A (by
    rw [map_ker _ _ Ideal.Quotient.mk_surjective Ideal.Quotient.mk_surjective,
      AlgHom.ker_coe, AlgHom.ker_coe, Ideal.Quotient.mkₐ_ker, Ideal.Quotient.mkₐ_ker])).trans
    (Ideal.quotientKerAlgEquivOfSurjective
      (map_surjective (Ideal.Quotient.mkₐ A I) (Ideal.Quotient.mkₐ A J)
        Ideal.Quotient.mk_surjective Ideal.Quotient.mk_surjective))).symm

/-- The inverse double-quotient comparison on classes of tensors. -/
@[simp]
theorem quotientTensorQuotientEquiv_symm_tmul (I : Ideal B) (J : Ideal C) (b : B) (c : C) :
    (quotientTensorQuotientEquiv (A := A) I J).symm
      (Ideal.Quotient.mk _ (b ⊗ₜ[A] c)) =
        Ideal.Quotient.mk I b ⊗ₜ[A] Ideal.Quotient.mk J c := by
  simp [quotientTensorQuotientEquiv]

/-- The double-quotient comparison on tensors of residue classes. -/
@[simp]
theorem quotientTensorQuotientEquiv_tmul (I : Ideal B) (J : Ideal C) (b : B) (c : C) :
    quotientTensorQuotientEquiv (A := A) I J
      (Ideal.Quotient.mk I b ⊗ₜ[A] Ideal.Quotient.mk J c) =
        Ideal.Quotient.mk _ (b ⊗ₜ[A] c) := by
  apply (quotientTensorQuotientEquiv (A := A) I J).symm.injective
  simp

/-- The double-quotient comparison on the left factor inclusion. -/
@[simp]
theorem quotientTensorQuotientEquiv_tmul_one (I : Ideal B) (J : Ideal C) (b : B) :
    quotientTensorQuotientEquiv (A := A) I J (Ideal.Quotient.mk I b ⊗ₜ[A] 1) =
      Ideal.Quotient.mk _ (b ⊗ₜ[A] 1) := by
  simpa only [map_one] using quotientTensorQuotientEquiv_tmul (A := A) I J b 1

/-- The double-quotient comparison on the right factor inclusion. -/
@[simp]
theorem quotientTensorQuotientEquiv_one_tmul (I : Ideal B) (J : Ideal C) (c : C) :
    quotientTensorQuotientEquiv (A := A) I J (1 ⊗ₜ[A] Ideal.Quotient.mk J c) =
      Ideal.Quotient.mk _ (1 ⊗ₜ[A] c) := by
  simpa only [map_one] using quotientTensorQuotientEquiv_tmul (A := A) I J 1 c

end Algebra.TensorProduct
