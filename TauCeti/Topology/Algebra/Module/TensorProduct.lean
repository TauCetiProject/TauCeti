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

When `B ⊗[A] T` and `T ⊗[A] B` carry their `T`-module topologies, swapping the tensor factors of a
continuous `T`-algebra equivalence `e : T ⊗[A] B ≃A[T] S` sending `1 ⊗ b` to `algebraMap B S b`
gives a continuous `B`-algebra equivalence `ContinuousAlgEquiv.baseChangeRight : B ⊗[A] T ≃A[B] S`.
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

namespace ContinuousAlgEquiv

open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable {A B T S : Type*} [CommSemiring A] [CommSemiring B] [CommSemiring T] [Semiring S]
  [Algebra A B] [Algebra A T] [Algebra B S] [Algebra T S]
  [TopologicalSpace T] [TopologicalSpace S]
  [TopologicalSpace (B ⊗[A] T)] [IsModuleTopology T (B ⊗[A] T)]
  [TopologicalSpace (T ⊗[A] B)] [IsModuleTopology T (T ⊗[A] B)]

/-- Continuous upgrade of `AlgEquiv.baseChangeRight`: when `B ⊗[A] T` and `T ⊗[A] B` carry their
`T`-module topologies, swapping tensor factors and applying `e : T ⊗[A] B ≃A[T] S` is a continuous
`B`-algebra equivalence `B ⊗[A] T ≃A[B] S`. -/
noncomputable def baseChangeRight (e : T ⊗[A] B ≃A[T] S)
    (he : ∀ b : B, e (1 ⊗ₜ[A] b) = algebraMap B S b) : B ⊗[A] T ≃A[B] S :=
  let hcomm : B ⊗[A] T ≃L[T] T ⊗[A] B :=
    (Algebra.TensorProduct.commRight A T B).symm.toLinearEquiv
      |>.toContinuousLinearEquivOfIsModuleTopology
  { toAlgEquiv := e.toAlgEquiv.baseChangeRight he
    continuous_toFun := (e.continuous.comp hcomm.continuous).congr fun z ↦ by
      have hswap (w : B ⊗[A] T) : hcomm w = Algebra.TensorProduct.comm A B T w := by
        induction w using TensorProduct.inductionOn with
        | tmul b t => simp [hcomm]
        | add x y hx hy => simp only [map_add, hx, hy]
      rw [Function.comp_apply, hswap]
      exact (e.toAlgEquiv.baseChangeRight_apply he z).symm
    continuous_invFun := (hcomm.symm.continuous.comp e.symm.continuous).congr fun s ↦ by
      have hswap (w : T ⊗[A] B) : hcomm.symm w = (Algebra.TensorProduct.comm A B T).symm w := by
        induction w using TensorProduct.inductionOn with
        | tmul t b => simp [hcomm]
        | add x y hx hy => simp only [map_add, hx, hy]
      rw [Function.comp_apply, hswap]
      exact (e.toAlgEquiv.baseChangeRight_symm_apply he s).symm }

/-- Forgetting continuity from `ContinuousAlgEquiv.baseChangeRight` recovers
`AlgEquiv.baseChangeRight`. -/
@[simp]
theorem baseChangeRight_toAlgEquiv (e : T ⊗[A] B ≃A[T] S)
    (he : ∀ b : B, e (1 ⊗ₜ[A] b) = algebraMap B S b) :
    (e.baseChangeRight he).toAlgEquiv = e.toAlgEquiv.baseChangeRight he := (rfl)

/-- `ContinuousAlgEquiv.baseChangeRight` swaps tensor factors and applies `e`. -/
@[simp]
theorem baseChangeRight_apply (e : T ⊗[A] B ≃A[T] S)
    (he : ∀ b : B, e (1 ⊗ₜ[A] b) = algebraMap B S b) (z : B ⊗[A] T) :
    e.baseChangeRight he z = e (Algebra.TensorProduct.comm A B T z) :=
  e.toAlgEquiv.baseChangeRight_apply he z

/-- The inverse of `ContinuousAlgEquiv.baseChangeRight` applies `e.symm` and swaps tensor
factors. -/
@[simp]
theorem baseChangeRight_symm_apply (e : T ⊗[A] B ≃A[T] S)
    (he : ∀ b : B, e (1 ⊗ₜ[A] b) = algebraMap B S b) (s : S) :
    (e.baseChangeRight he).symm s = (Algebra.TensorProduct.comm A B T).symm (e.symm s) :=
  e.toAlgEquiv.baseChangeRight_symm_apply he s

end ContinuousAlgEquiv
