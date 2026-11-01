/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.TensorProduct.Basic
public import TauCeti.LinearAlgebra.PiTensorProduct.Option

/-!
# Algebra equivalences for indexed tensor products

The linear equivalences for reindexing, removing an empty index set, and splitting off one
factor preserve the algebra structures on indexed tensor products. Their algebra versions
allow algebraic properties stable under binary tensor products to be proved by induction on a
finite index type.

These constructions upgrade Mathlib's `PiTensorProduct.reindex` and
`PiTensorProduct.isEmptyEquiv`, and `PiTensorProduct.optionEquiv`.
-/

public section

open scoped TensorProduct

namespace PiTensorProduct

variable {R : Type*} [CommSemiring R]

/-- Reindexing an indexed tensor product of algebras as an algebra equivalence. -/
noncomputable def reindexAlgEquiv {ι κ : Type*} (A : ι → Type*)
    [∀ i, CommSemiring (A i)] [∀ i, Algebra R (A i)] (e : ι ≃ κ) :
    (⨂[R] i, A i) ≃ₐ[R] ⨂[R] j, A (e.symm j) :=
  AlgEquiv.ofLinearEquiv (reindex R A e) (by simp only [one_def, reindex_tprod]; rfl) (by
    intro x y
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r a =>
      induction y using PiTensorProduct.induction_on with
      | smul_tprod s b =>
        simp only [smul_mul_smul_comm, map_smul, tprod_mul_tprod, reindex_tprod]
        rfl
      | add y z hy hz => simp only [mul_add, map_add, hy, hz]
    | add x z hx hz => simp only [add_mul, map_add, hx, hz])

/-- Reindexing preserves the labels of the entries of a pure tensor. -/
@[simp]
theorem reindexAlgEquiv_tprod {ι κ : Type*} (A : ι → Type*)
    [∀ i, CommSemiring (A i)] [∀ i, Algebra R (A i)] (e : ι ≃ κ) (a : ∀ i, A i) :
    reindexAlgEquiv A e (tprod R a) = tprod R (fun j ↦ a (e.symm j)) := by
  simp [reindexAlgEquiv, reindex_tprod]

/-- Reattaching the original index labels recovers the original pure tensor. -/
@[simp]
theorem reindexAlgEquiv_symm_tprod {ι κ : Type*} (A : ι → Type*)
    [∀ i, CommSemiring (A i)] [∀ i, Algebra R (A i)] (e : ι ≃ κ) (a : ∀ i, A i) :
    (reindexAlgEquiv (R := R) A e).symm (tprod R (fun j ↦ a (e.symm j))) = tprod R a := by
  rw [AlgEquiv.symm_apply_eq, reindexAlgEquiv_tprod]

/-- The tensor product over an empty family of algebras is the base algebra. -/
noncomputable def isEmptyAlgEquiv (ι : Type*) [IsEmpty ι] (A : ι → Type*)
    [∀ i, CommSemiring (A i)] [∀ i, Algebra R (A i)] : (⨂[R] i, A i) ≃ₐ[R] R :=
  AlgEquiv.ofLinearEquiv (isEmptyEquiv ι) (by simp [one_def, isEmptyEquiv_apply_tprod]) (by
    intro x y
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r a =>
      induction y using PiTensorProduct.induction_on with
      | smul_tprod s b =>
        simp only [smul_mul_smul_comm, map_smul, tprod_mul_tprod,
          isEmptyEquiv_apply_tprod, mul_one]
      | add y z hy hz => simp only [mul_add, map_add, hy, hz]
    | add x z hx hz => simp only [add_mul, map_add, hx, hz])

/-- An empty pure tensor is the multiplicative unit. -/
@[simp]
theorem isEmptyAlgEquiv_tprod (ι : Type*) [IsEmpty ι] (A : ι → Type*)
    [∀ i, CommSemiring (A i)] [∀ i, Algebra R (A i)] (a : ∀ i, A i) :
    isEmptyAlgEquiv ι A (tprod R a) = 1 := by
  simp [isEmptyAlgEquiv, isEmptyEquiv_apply_tprod]

/-- The inverse empty-family equivalence sends a scalar to that scalar times the empty tensor. -/
@[simp]
theorem isEmptyAlgEquiv_symm_apply (ι : Type*) [IsEmpty ι] (A : ι → Type*)
    [∀ i, CommSemiring (A i)] [∀ i, Algebra R (A i)] (r : R) :
    (isEmptyAlgEquiv (R := R) ι A).symm r = r • 1 := by
  apply (isEmptyAlgEquiv (R := R) ι A).injective
  simp

/-- Splitting off the factor at `none` of an indexed tensor product of algebras. -/
noncomputable def optionAlgEquiv {ι : Type*} (A : Option ι → Type*)
    [∀ i, CommSemiring (A i)] [∀ i, Algebra R (A i)] :
    (⨂[R] i, A i) ≃ₐ[R] (⨂[R] i, A (some i)) ⊗[R] A none :=
  AlgEquiv.ofLinearEquiv (optionEquiv A) (by
    simp only [one_def, optionEquiv_tprod, Algebra.TensorProduct.one_def]
    rfl) (by
    intro x y
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r a =>
      induction y using PiTensorProduct.induction_on with
      | smul_tprod s b =>
        simp only [smul_mul_smul_comm, map_smul, tprod_mul_tprod, optionEquiv_tprod,
          Algebra.TensorProduct.tmul_mul_tmul]
        rfl
      | add y z hy hz => simp only [mul_add, map_add, hy, hz]
    | add x z hx hz => simp only [add_mul, map_add, hx, hz])

/-- Splitting off a factor of a pure tensor separates the `some` entries from the `none` entry. -/
@[simp]
theorem optionAlgEquiv_tprod {ι : Type*} (A : Option ι → Type*)
    [∀ i, CommSemiring (A i)] [∀ i, Algebra R (A i)] (a : ∀ i, A i) :
    optionAlgEquiv (R := R) A (tprod R a) = tprod R (fun i ↦ a (some i)) ⊗ₜ a none := by
  simp [optionAlgEquiv]

/-- Reattaching the separated factor recovers the original pure tensor. -/
@[simp]
theorem optionAlgEquiv_symm_tmul {ι : Type*} (A : Option ι → Type*)
    [∀ i, CommSemiring (A i)] [∀ i, Algebra R (A i)] (a : ∀ i, A i) :
    (optionAlgEquiv (R := R) A).symm (tprod R (fun i ↦ a (some i)) ⊗ₜ a none) = tprod R a := by
  rw [AlgEquiv.symm_apply_eq, optionAlgEquiv_tprod]

end PiTensorProduct
