/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Norm.Basic
public import Mathlib.RingTheory.Trace.Basic
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Charpoly.BaseChange
public import TauCeti.LinearAlgebra.Trace.Pi

/-!
# Norms and traces of finite products

This file records the determinant and trace calculations for finite dependent products.  The
tensor-product formulas are the scalar-extension interface used by the number-field local-global
development.
-/

public section

namespace TauCeti

open scoped BigOperators

universe u v

variable {K : Type u} [Field K]

variable {ι : Type v} [Fintype ι]
variable {L : ι → Type*} [∀ i, Field (L i)] [∀ i, Algebra K (L i)]
  [∀ i, FiniteDimensional K (L i)]

open Module

/-- The determinant of a coordinatewise endomorphism of a finite dependent product. -/
theorem LinearMap.det_pi_of_apply_eq_dependent {M : ι → Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, Module K (M i)] [∀ i, FiniteDimensional K (M i)]
    (T : ((i : ι) → M i) →ₗ[K] ((i : ι) → M i)) (f : ∀ i, M i →ₗ[K] M i)
    (hT : ∀ x i, T x i = f i (x i)) :
    T.det = ∏ i, (f i).det := by
  classical
  let b (i : ι) := Module.Free.chooseBasis K (M i)
  let _ (i : ι) : Fintype (Module.Free.ChooseBasisIndex K (M i)) := Fintype.ofFinite _
  let B : Module.Basis (Σ i, Module.Free.ChooseBasisIndex K (M i)) K ((i : ι) → M i) :=
    Pi.basis b
  rw [← LinearMap.det_toMatrix B]
  have hmatrix :
      (LinearMap.toMatrix B B T) =
        Matrix.blockDiagonal' (fun i ↦ LinearMap.toMatrix (b i) (b i) (f i)) := by
    ext ⟨i₁, j₁⟩ ⟨i₂, j₂⟩
    simp only [LinearMap.toMatrix_apply', B, b, Pi.basis_apply, Matrix.blockDiagonal'_apply]
    split_ifs with h
    · subst i₂
      simp [hT]
    · simp [hT, h]
  rw [hmatrix]
  let _ : LinearOrder ι := Equiv.linearOrder (Fintype.equivFin ι)
  rw [(Matrix.blockTriangular_blockDiagonal' _).det_fintype]
  apply Finset.prod_congr rfl
  intro i hi
  let e : Module.Free.ChooseBasisIndex K (M i) ≃
      {a : Σ i, Module.Free.ChooseBasisIndex K (M i) // a.1 = i} :=
    { toFun := fun j ↦ ⟨⟨i, j⟩, rfl⟩
      invFun := fun a ↦ cast (by rw [a.2]) a.1.2
      left_inv := by intro j; rfl
      right_inv := by
        intro a
        apply Subtype.ext
        rcases a with ⟨⟨a, j⟩, ha⟩
        dsimp at ha
        subst a
        rfl }
  rw [← LinearMap.det_toMatrix (b i)]
  rw [← Matrix.det_reindex_self e]
  congr 1
  ext j k
  rcases j with ⟨⟨j₁, j₂⟩, hj⟩
  rcases k with ⟨⟨k₁, k₂⟩, hk⟩
  dsimp at hj hk
  subst j₁
  subst k₁
  simp [e, Matrix.toSquareBlock_def, Matrix.reindex]

/-- The norm of an element of a finite dependent product is the product of its component norms. -/
theorem Algebra.norm_pi (x : ∀ i, L i) :
    Algebra.norm K x = ∏ i, Algebra.norm K (x i) := by
  rw [Algebra.norm_apply]
  have h : Algebra.lmul K (∀ i, L i) x =
      LinearMap.pi (fun i ↦ (Algebra.lmul K (L i) (x i)).comp (LinearMap.proj i)) := by
    ext y i
    simp [Algebra.lmul]
  rw [h]
  rw [LinearMap.det_pi_of_apply_eq_dependent
    (f := fun i ↦ Algebra.lmul K (L i) (x i)) (hT := by
    intro y i
    simp [Algebra.lmul])]
  congr 1

/-- The trace of an element of a finite dependent product is the sum of its component traces. -/
theorem Algebra.trace_pi (x : ∀ i, L i) :
    Algebra.trace K (∀ i, L i) x = ∑ i, Algebra.trace K (L i) (x i) := by
  rw [Algebra.trace_apply]
  apply LinearMap.trace_pi_of_apply_eq_dependent
    (f := fun i ↦ Algebra.lmul K (L i) (x i))
  intro y i
  simp [Algebra.lmul]

variable {A B : Type*} [CommRing A] [Algebra K A]
variable [CommRing B] [Algebra K B]
variable [Module.Free K B] [Module.Finite K B]

/-- Norm commutes with scalar extension on a pure tensor. -/
theorem Algebra.norm_baseChange_tmul (x : B) :
    Algebra.norm A ((1 : A) ⊗ₜ[K] x) = algebraMap K A (Algebra.norm K x) := by
  rw [Algebra.norm_apply]
  calc
    LinearMap.det (Algebra.lmul A (TensorProduct K A B) ((1 : A) ⊗ₜ[K] x)) =
        LinearMap.det ((Algebra.lmul K B x).baseChange A) := by
          rw [Algebra.baseChange_lmul]
    _ = algebraMap K A (LinearMap.det (Algebra.lmul K B x)) :=
      LinearMap.det_baseChange (R := K) (M := B) (f := Algebra.lmul K B x) (A := A)

/-- Trace commutes with scalar extension on a pure tensor. -/
theorem Algebra.trace_baseChange_tmul (x : B) :
    Algebra.trace A (TensorProduct K A B) ((1 : A) ⊗ₜ[K] x) =
      algebraMap K A (Algebra.trace K B x) := by
  rw [Algebra.trace_apply]
  calc
    LinearMap.trace A (TensorProduct K A B)
        (Algebra.lmul A (TensorProduct K A B) ((1 : A) ⊗ₜ[K] x)) =
        LinearMap.trace A (TensorProduct K A B) ((Algebra.lmul K B x).baseChange A) := by
          rw [Algebra.baseChange_lmul]
    _ = algebraMap K A (LinearMap.trace K B (Algebra.lmul K B x)) :=
      LinearMap.trace_baseChange (R := K) (M := B) (f := Algebra.lmul K B x) (A := A)

end TauCeti
