/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Tensor products of quotient algebras

This file complements `Mathlib.RingTheory.TensorProduct.Quotient` with algebra equivalences for
tensor products involving quotient algebras:

* **Double-quotient comparison** (`Algebra.TensorProduct.quotientTensorQuotientEquiv`): quotienting
  both factors of a tensor product is the same as quotienting the tensor product by the sum of the
  two extended ideals. This is the algebra analogue of Mathlib's linear
  `TensorProduct.quotientTensorQuotientEquiv`, constructed from `Algebra.TensorProduct.map_ker` and
  `Ideal.quotientKerAlgEquivOfSurjective`.
* **Ideals killed under base change** (`Algebra.TensorProduct.tensorQuotientEquivOfLeKer`,
  `Algebra.TensorProduct.tensorQuotientEquivOfLeMap`): when an ideal `J` of an `R`-algebra `T` lies
  in the kernel of `Algebra.TensorProduct.includeRight : T →ₐ[R] A ⊗[R] T` (in particular, when
  `A = R ⧸ I` and `J ≤ I.map (algebraMap R T)`), its extended ideal in `A ⊗[R] T` is `⊥`, so
  `Algebra.TensorProduct.tensorQuotientEquiv` collapses to an equivalence `A ⊗[R] (T ⧸ J) ≃ₐ[S]
  A ⊗[R] T`.
-/

public section

open TensorProduct

namespace Algebra.TensorProduct

section DoubleQuotient

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

end DoubleQuotient

section Ker

variable {R : Type*} (S : Type*) {T A : Type*}
  [CommRing R] [CommRing S] [Algebra R S] [CommRing T] [Algebra R T]
  [CommRing A] [Algebra R A] [Algebra S A] [IsScalarTower R S A]

/-- Quotienting `T` by an ideal killed by `includeRight : T →ₐ[R] A ⊗[R] T` leaves `A ⊗[R] T`
unchanged as an `S`-algebra. -/
noncomputable def tensorQuotientEquivOfLeKer {J : Ideal T}
    (hJ : J ≤ RingHom.ker (includeRight (R := R) (A := A) (B := T))) :
    A ⊗[R] (T ⧸ J) ≃ₐ[S] A ⊗[R] T :=
  (tensorQuotientEquiv (R := R) S T A J).trans <|
    (Ideal.quotientEquivAlgOfEq S ((Ideal.map_eq_bot_iff_le_ker _).mpr hJ)).trans <|
      AlgEquiv.quotientBot S (A ⊗[R] T)

/-- `tensorQuotientEquivOfLeKer` acts on pure tensors by dropping the quotient map in the right
factor. -/
@[simp]
theorem tensorQuotientEquivOfLeKer_tmul {J : Ideal T}
    (hJ : J ≤ RingHom.ker (includeRight (R := R) (A := A) (B := T))) (a : A) (t : T) :
    tensorQuotientEquivOfLeKer S hJ (a ⊗ₜ[R] Ideal.Quotient.mk J t) = a ⊗ₜ[R] t := by
  rw [tensorQuotientEquivOfLeKer, AlgEquiv.trans_apply, AlgEquiv.trans_apply,
    tensorQuotientEquiv_apply_tmul (R := R), Ideal.quotientEquivAlgOfEq_mk,
    AlgEquiv.quotientBot_mk]

/-- The inverse of `tensorQuotientEquivOfLeKer` reduces the right factor modulo `J`. -/
@[simp]
theorem tensorQuotientEquivOfLeKer_symm_tmul {J : Ideal T}
    (hJ : J ≤ RingHom.ker (includeRight (R := R) (A := A) (B := T))) (a : A) (t : T) :
    (tensorQuotientEquivOfLeKer S hJ).symm (a ⊗ₜ[R] t) = a ⊗ₜ[R] Ideal.Quotient.mk J t := by
  rw [tensorQuotientEquivOfLeKer, AlgEquiv.symm_trans_apply, AlgEquiv.symm_trans_apply,
    AlgEquiv.quotientBot_symm_mk, Ideal.quotientEquivAlgOfEq_symm,
    Ideal.quotientEquivAlgOfEq_mk, tensorQuotientEquiv_symm_apply_tmul (R := R)]

end Ker

section Map

variable {R T : Type*} [CommRing R] [CommRing T] [Algebra R T]

/-- Quotienting `T` by an ideal contained in `IT` leaves `(R ⧸ I) ⊗[R] T` unchanged as an
`(R ⧸ I)`-algebra. -/
noncomputable def tensorQuotientEquivOfLeMap (I : Ideal R) {J : Ideal T}
    (hJ : J ≤ I.map (algebraMap R T)) :
    (R ⧸ I) ⊗[R] (T ⧸ J) ≃ₐ[R ⧸ I] (R ⧸ I) ⊗[R] T :=
  tensorQuotientEquivOfLeKer (R ⧸ I) fun x hx ↦ by
    rw [RingHom.mem_ker, includeRight_apply, ← quotIdealMapEquivQuotTensor_mk T I x,
      Ideal.Quotient.eq_zero_iff_mem.mpr (hJ hx), map_zero]

/-- `tensorQuotientEquivOfLeMap` acts on pure tensors by dropping the quotient map in the right
factor. -/
@[simp]
theorem tensorQuotientEquivOfLeMap_tmul (I : Ideal R) {J : Ideal T}
    (hJ : J ≤ I.map (algebraMap R T)) (x : R ⧸ I) (t : T) :
    tensorQuotientEquivOfLeMap I hJ (x ⊗ₜ[R] Ideal.Quotient.mk J t) = x ⊗ₜ[R] t :=
  tensorQuotientEquivOfLeKer_tmul (R ⧸ I) _ x t

/-- The inverse of `tensorQuotientEquivOfLeMap` reduces the right factor modulo `J`. -/
@[simp]
theorem tensorQuotientEquivOfLeMap_symm_tmul (I : Ideal R) {J : Ideal T}
    (hJ : J ≤ I.map (algebraMap R T)) (x : R ⧸ I) (t : T) :
    (tensorQuotientEquivOfLeMap I hJ).symm (x ⊗ₜ[R] t) = x ⊗ₜ[R] Ideal.Quotient.mk J t :=
  tensorQuotientEquivOfLeKer_symm_tmul (R ⧸ I) _ x t

end Map

end Algebra.TensorProduct
