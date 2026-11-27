/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Algebra.Equiv
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import TauCeti.RingTheory.TensorProduct.Maps
import TauCeti.Topology.Algebra.Module.ModuleTopology

/-!
# Continuity of change of coefficients on tensor products

For module topologies, a continuous algebra homomorphism `B → C` induces a continuous
map `B ⊗[A] M → C ⊗[A] M`. Only the source needs the module topology; the target can
be any topological `C`-module. This applies in particular to restriction maps on finite
modules over topological algebras.

When `T ⊗[A] B` and `B ⊗[A] T` carry their `T`-module topologies, swapping tensor factors gives
a continuous `T`-algebra equivalence
`Algebra.TensorProduct.continuousCommRight : T ⊗[A] B ≃A[T] B ⊗[A] T`. Precomposing a continuous
`T`-algebra equivalence `e : T ⊗[A] B ≃A[T] S` sending `1 ⊗ b` to `algebraMap B S b` with this
swap gives a continuous `B`-algebra equivalence
`ContinuousAlgEquiv.ofCommRight : B ⊗[A] T ≃A[B] S`.
-/

public section

namespace AlgHom

open TensorProduct

variable {A B C M : Type*} [CommSemiring A] [Semiring B] [Semiring C]
    [Algebra A B] [Algebra A C] [AddCommMonoid M] [Module A M]
    [TopologicalSpace B] [TopologicalSpace C]
    [TopologicalSpace (B ⊗[A] M)] [IsModuleTopology B (B ⊗[A] M)]
    [TopologicalSpace (C ⊗[A] M)] [ContinuousAdd (C ⊗[A] M)]
    [ContinuousSMul C (C ⊗[A] M)]

/-- Changing coefficients along a continuous algebra homomorphism is continuous when the
source tensor product has the module topology over its coefficient algebra. -/
theorem continuous_rTensor (f : B →ₐ[A] C) (hf : Continuous f) :
    Continuous (f.toLinearMap.rTensor M) := by
  let g : B ⊗[A] M →ₛₗ[f.toRingHom] C ⊗[A] M :=
    { (f.toLinearMap.rTensor M).toAddHom with
      map_smul' := fun b z ↦ by
        induction z using TensorProduct.inductionOn with
        | tmul c m => simp [smul_tmul']
        | add x y hx hy => simp_all [smul_add] }
  exact IsModuleTopology.continuous_of_linearMapₛₗ hf g

end AlgHom

namespace Algebra.TensorProduct

open scoped _root_.TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable (A T B : Type*) [CommSemiring A] [CommSemiring T] [Semiring B]
  [Algebra A T] [Algebra A B] [TopologicalSpace T]
  [TopologicalSpace (T ⊗[A] B)] [IsModuleTopology T (T ⊗[A] B)]
  [TopologicalSpace (B ⊗[A] T)] [IsModuleTopology T (B ⊗[A] T)]

/-- Continuous upgrade of `Algebra.TensorProduct.commRight`: when `T ⊗[A] B` and `B ⊗[A] T` carry
their `T`-module topologies (acting on the right factor of `B ⊗[A] T`), swapping tensor factors
is a continuous `T`-algebra equivalence `T ⊗[A] B ≃A[T] B ⊗[A] T`. -/
noncomputable def continuousCommRight : T ⊗[A] B ≃A[T] B ⊗[A] T :=
  let h := (Algebra.TensorProduct.commRight A T B).toLinearEquiv
    |>.toContinuousLinearEquivOfIsModuleTopology
  { toAlgEquiv := Algebra.TensorProduct.commRight A T B
    continuous_toFun := h.continuous.congr fun _ ↦ by simp [h]
    continuous_invFun := h.symm.continuous.congr fun _ ↦ by simp [h] }

/-- Forgetting continuity from `Algebra.TensorProduct.continuousCommRight` recovers
`Algebra.TensorProduct.commRight`. -/
@[simp]
theorem continuousCommRight_toAlgEquiv :
    (continuousCommRight A T B).toAlgEquiv = Algebra.TensorProduct.commRight A T B := (rfl)

variable {A T B}

/-- `Algebra.TensorProduct.continuousCommRight` acts as the ordinary tensor swap. -/
@[simp]
theorem continuousCommRight_apply (z : T ⊗[A] B) :
    continuousCommRight A T B z = Algebra.TensorProduct.comm A T B z := (rfl)

/-- The inverse of `Algebra.TensorProduct.continuousCommRight` acts as the ordinary tensor
swap. -/
@[simp]
theorem continuousCommRight_symm_apply (w : B ⊗[A] T) :
    (continuousCommRight A T B).symm w = Algebra.TensorProduct.comm A B T w :=
  DFunLike.congr_fun (Algebra.TensorProduct.comm_symm (R := A) (A := T) (B := B)) w

end Algebra.TensorProduct

namespace ContinuousAlgEquiv

open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable {A B T S : Type*} [CommSemiring A] [CommSemiring B] [CommSemiring T] [Semiring S]
  [Algebra A B] [Algebra A T] [Algebra B S] [Algebra T S]
  [TopologicalSpace T] [TopologicalSpace S]
  [TopologicalSpace (B ⊗[A] T)] [IsModuleTopology T (B ⊗[A] T)]
  [TopologicalSpace (T ⊗[A] B)] [IsModuleTopology T (T ⊗[A] B)]

/-- Continuous upgrade of `AlgEquiv.ofCommRight`: when `B ⊗[A] T` and `T ⊗[A] B` carry their
`T`-module topologies, swapping tensor factors and applying `e : T ⊗[A] B ≃A[T] S` is a continuous
`B`-algebra equivalence `B ⊗[A] T ≃A[B] S`. -/
noncomputable def ofCommRight (e : T ⊗[A] B ≃A[T] S)
    (he : ∀ b : B, e (1 ⊗ₜ[A] b) = algebraMap B S b) : B ⊗[A] T ≃A[B] S :=
  let hcomm := (Algebra.TensorProduct.continuousCommRight A T B).symm
  { toAlgEquiv := e.toAlgEquiv.ofCommRight he
    continuous_toFun := (e.continuous.comp hcomm.continuous).congr fun z ↦ by
      rw [Function.comp_apply, Algebra.TensorProduct.continuousCommRight_symm_apply]
      exact (e.toAlgEquiv.ofCommRight_apply he z).symm
    continuous_invFun := (hcomm.symm.continuous.comp e.symm.continuous).congr fun s ↦ by
      rw [Function.comp_apply, ContinuousAlgEquiv.symm_symm,
        Algebra.TensorProduct.continuousCommRight_apply, ← Algebra.TensorProduct.comm_symm]
      exact (e.toAlgEquiv.ofCommRight_symm_apply he s).symm }

/-- Forgetting continuity from `ContinuousAlgEquiv.ofCommRight` recovers
`AlgEquiv.ofCommRight`. -/
@[simp]
theorem ofCommRight_toAlgEquiv (e : T ⊗[A] B ≃A[T] S)
    (he : ∀ b : B, e (1 ⊗ₜ[A] b) = algebraMap B S b) :
    (e.ofCommRight he).toAlgEquiv = e.toAlgEquiv.ofCommRight he := (rfl)

/-- `ContinuousAlgEquiv.ofCommRight` swaps tensor factors and applies `e`. -/
@[simp]
theorem ofCommRight_apply (e : T ⊗[A] B ≃A[T] S)
    (he : ∀ b : B, e (1 ⊗ₜ[A] b) = algebraMap B S b) (z : B ⊗[A] T) :
    e.ofCommRight he z = e (Algebra.TensorProduct.comm A B T z) :=
  e.toAlgEquiv.ofCommRight_apply he z

/-- The inverse of `ContinuousAlgEquiv.ofCommRight` applies `e.symm` and swaps tensor
factors. -/
@[simp]
theorem ofCommRight_symm_apply (e : T ⊗[A] B ≃A[T] S)
    (he : ∀ b : B, e (1 ⊗ₜ[A] b) = algebraMap B S b) (s : S) :
    (e.ofCommRight he).symm s = (Algebra.TensorProduct.comm A B T).symm (e.symm s) :=
  e.toAlgEquiv.ofCommRight_symm_apply he s

end ContinuousAlgEquiv
