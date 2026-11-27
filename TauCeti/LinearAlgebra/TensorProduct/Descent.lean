/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.BaseChange
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.Finiteness.Descent
public import TauCeti.LinearAlgebra.TensorProduct.Basis
public import TauCeti.LinearAlgebra.TensorProduct.Intersection

/-!
# Pulling back tensor products of subspaces

For a field extension `L / K`, subspaces of `L ⊗[K] M` and `L ⊗[K] N` pull back to subspaces
of `M` and `N`. A tensor defined over `K` belongs to the tensor product of the two larger
subspaces exactly when it belongs to the tensor product of their pullbacks. Contractions by
linear functionals, extended from `K` to `L`, detect this membership. This permits descent of
comultiplication stability without requiring either larger subspace itself to descend. Over a
field extension, a finite-dimensional subspace also has a finite-dimensional pullback.
-/

public section

open TensorProduct
open scoped TensorProduct

namespace LinearMap

variable {K L M N : Type*} [CommSemiring K] [CommSemiring L] [Algebra K L]
  [AddCommMonoid M] [Module K M] [AddCommMonoid N] [Module K N]

/-- Contracting a scalar-extended tensor by a scalar-extended functional commutes with insertion
of the coefficient `1` in the left factor. -/
@[simp]
theorem tensorComponent_tensorTensorTensorComm (φ : Module.Dual K N) (z : M ⊗[K] N) :
    tensorComponent (Module.Dual.baseChange L φ)
        (AlgebraTensorModule.tensorTensorTensorComm K L K L L L M N
          (((1 : L) ⊗ₜ[L] (1 : L)) ⊗ₜ[K] z)) =
      (1 : L) ⊗ₜ[K] tensorComponent φ z := by
  induction z using TensorProduct.inductionOn with
  | tmul m n => simp [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]

end LinearMap

namespace Submodule

section TensorMembership

variable {K L M N : Type*} [Field K] [CommRing L] [Algebra K L]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]

/-- A tensor defined over the smaller field that lies in `P ⊗ Q` after scalar extension lies in
the tensor product of the pullbacks of `P` and `Q`. Neither subspace is assumed to descend. -/
theorem tensor_mem_range_comap_of_baseChange
    (P : Submodule L (L ⊗[K] M)) (Q : Submodule L (L ⊗[K] N)) (z : M ⊗[K] N)
    (hz : AlgebraTensorModule.tensorTensorTensorComm K L K L L L M N
      (((1 : L) ⊗ₜ[L] (1 : L)) ⊗ₜ[K] z) ∈
        LinearMap.range (TensorProduct.map P.subtype Q.subtype)) :
    z ∈ LinearMap.range (TensorProduct.map
      ((P.restrictScalars K).comap (TensorProduct.mk K L M 1)).subtype
      ((Q.restrictScalars K).comap (TensorProduct.mk K L N 1)).subtype) := by
  let P₀ := (P.restrictScalars K).comap (TensorProduct.mk K L M 1)
  let Q₀ := (Q.restrictScalars K).comap (TensorProduct.mk K L N 1)
  rw [range_map_subtype_subtype _ _
    (Module.Flat.lTensor_preserves_injective_linearMap _ Q₀.injective_subtype)]
  obtain ⟨t, ht⟩ := hz
  have hright : z ∈ LinearMap.range (P₀.subtype.rTensor N) := by
    rw [LinearMap.rTensor_def, tensor_mem_range_iff_forall_tensorComponent_mem]
    intro φ
    have h := congrArg (LinearMap.tensorComponent (Module.Dual.baseChange L φ)) ht
    rw [LinearMap.tensorComponent_tensorTensorTensorComm,
      LinearMap.tensorComponent_map] at h
    exact (h ▸ (LinearMap.tensorComponent ((Module.Dual.baseChange L φ).comp Q.subtype)
      t).property : (1 : L) ⊗ₜ[K] LinearMap.tensorComponent φ z ∈ P)
  have hleft : TensorProduct.comm K M N z ∈ LinearMap.range (Q₀.subtype.rTensor M) := by
    rw [LinearMap.rTensor_def, tensor_mem_range_iff_forall_tensorComponent_mem]
    intro φ
    have h := congrArg (fun w ↦ LinearMap.tensorComponent (Module.Dual.baseChange L φ)
      (TensorProduct.comm L (L ⊗[K] M) (L ⊗[K] N) w)) ht
    have hswap : TensorProduct.comm L (L ⊗[K] M) (L ⊗[K] N)
        (AlgebraTensorModule.tensorTensorTensorComm K L K L L L M N
          (((1 : L) ⊗ₜ[L] (1 : L)) ⊗ₜ[K] z)) =
        AlgebraTensorModule.tensorTensorTensorComm K L K L L L N M
          (((1 : L) ⊗ₜ[L] (1 : L)) ⊗ₜ[K] TensorProduct.comm K M N z) := by
      clear ht hright h
      induction z using TensorProduct.inductionOn with
      | tmul m n => simp
      | add x y hx hy => simp only [map_add, TensorProduct.tmul_add, hx, hy]
    rw [hswap, LinearMap.tensorComponent_tensorTensorTensorComm, ← TensorProduct.map_comm,
      LinearMap.tensorComponent_map] at h
    exact (h ▸ (LinearMap.tensorComponent ((Module.Dual.baseChange L φ).comp P.subtype)
      (TensorProduct.comm L P Q t)).property :
        (1 : L) ⊗ₜ[K] LinearMap.tensorComponent φ (TensorProduct.comm K M N z) ∈ Q)
  refine ⟨?_, hright⟩
  obtain ⟨s, hs⟩ := hleft
  refine ⟨TensorProduct.comm K Q₀ M s, ?_⟩
  simpa only [LinearMap.rTensor_def, LinearMap.lTensor_def, ← TensorProduct.map_comm,
    TensorProduct.comm_comm] using
    congrArg (TensorProduct.comm K N M) hs

end TensorMembership

/-- The inverse image of a finite-dimensional subspace under scalar extension to a field is
finite-dimensional over the original field. -/
theorem finiteDimensional_comap_mk_one {K L M : Type*} [Field K] [Field L] [Algebra K L]
    [AddCommGroup M] [Module K M] (D : Submodule L (L ⊗[K] M)) [FiniteDimensional L D] :
    FiniteDimensional K ((D.restrictScalars K).comap (TensorProduct.mk K L M 1)) := by
  let A := (D.restrictScalars K).comap (TensorProduct.mk K L M 1)
  have hle : A.baseChange L ≤ D :=
    Submodule.baseChange_le_iff_le_comap.mpr le_rfl
  have : FiniteDimensional L (A.baseChange L) := Submodule.finiteDimensional_of_le hle
  let e : L ⊗[K] A ≃ₗ[L] A.baseChange L :=
    LinearEquiv.ofInjective (A.subtype.baseChange L)
      (Module.Flat.lTensor_preserves_injective_linearMap _ A.injective_subtype)
  have : FiniteDimensional L (L ⊗[K] A) := Module.Finite.equiv e.symm
  exact Module.Finite.of_finite_tensorProduct_of_faithfullyFlat L

end Submodule
