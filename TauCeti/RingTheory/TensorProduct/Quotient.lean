/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Tensor products with quotients by ideals killed under base change

When an ideal `J` of an `R`-algebra `T` lies in the kernel of
`Algebra.TensorProduct.includeRight : T →ₐ[R] A ⊗[R] T`, the extended ideal of `J` in `A ⊗[R] T`
is `⊥`, so `Algebra.TensorProduct.tensorQuotientEquiv` collapses to an `S`-algebra equivalence
`A ⊗[R] (T ⧸ J) ≃ₐ[S] A ⊗[R] T` (`Algebra.TensorProduct.tensorQuotientEquivOfLeKer`).

Specializing to `A = S = R ⧸ I` shows that quotienting `T` by any ideal `J ≤ I.map (algebraMap R T)`
leaves the fiber `(R ⧸ I) ⊗[R] T` unchanged (`Algebra.TensorProduct.tensorQuotientEquivOfLeMap`).
-/

public section

open TensorProduct

namespace Algebra.TensorProduct

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
