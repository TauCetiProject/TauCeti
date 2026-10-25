/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.Topology.Algebra.LinearMapCompletion
public import Mathlib.Topology.Algebra.UniformRing

/-!
# Base change of a topological module to the completed ring

Let `A` be a commutative topological ring with a compatible uniformity and `M` a topological
`A`-module with a compatible uniformity. For each `m : M` the continuous linear map `a ↦ a • m`
extends to the separated completions, giving `Â → M̂`. These maps are `A`-bilinear in `(â, m)`
and define the canonical map

  `UniformSpace.Completion.ofTensorProduct A M : Completion A ⊗[A] M →ₗ[A] Completion M`,

sending `a ⊗ m` to the image of `a • m` for `a ∈ A`. It is the topological analogue of Mathlib's
`AdicCompletion.ofTensorProduct`. For finite modules over a Huber ring with a noetherian ring of
definition it is bijective (`TauCeti.Huber.PairOfDefinition.ofTensorProduct_bijective`).

No completeness, separation or finiteness is assumed here.
-/

public section

open TensorProduct

namespace UniformSpace.Completion

variable (A : Type*) [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
  (M : Type*) [AddCommGroup M] [Module A M] [UniformSpace M] [IsUniformAddGroup M]
  [ContinuousSMul A M] [UniformContinuousConstSMul A M]

/-- The bilinear map `(m, â) ↦ â • m`: for each `m : M`, the completion of `a ↦ a • m`. -/
private noncomputable def smulCompletion : M →ₗ[A] Completion A →ₗ[A] Completion M where
  toFun m := (ContinuousLinearMap.toSpanSingleton A m).completion.toLinearMap
  map_add' m m' := by
    ext a
    induction a using Completion.induction_on with
    | hp =>
      exact isClosed_eq (ContinuousLinearMap.continuous _)
        ((ContinuousLinearMap.continuous _).add (ContinuousLinearMap.continuous _))
    | ih a => simp [coe_add, coe_smul]
  map_smul' c m := by
    ext a
    induction a using Completion.induction_on with
    | hp =>
      exact isClosed_eq (ContinuousLinearMap.continuous _)
        ((ContinuousLinearMap.continuous _).const_smul c)
    | ih a => simp [← coe_smul, smul_comm a c m]

/-- The canonical map `Â ⊗[A] M → M̂` from the base change of `M` to the completion of `A` into
the completion of `M`: it sends `â ⊗ m` to the value at `â` of the completion of `a ↦ a • m`. -/
noncomputable def ofTensorProduct : Completion A ⊗[A] M →ₗ[A] Completion M :=
  TensorProduct.lift (smulCompletion A M).flip

variable {A M}

/-- On a pure tensor `â ⊗ m`, the canonical map is the completion of `a ↦ a • m`, evaluated
at `â`. -/
theorem ofTensorProduct_tmul (a : Completion A) (m : M) :
    ofTensorProduct A M (a ⊗ₜ m) = (ContinuousLinearMap.toSpanSingleton A m).completion a :=
  (rfl)

/-- The canonical map sends `a ⊗ m`, for `a ∈ A`, to the image of `a • m` in the completion. -/
@[simp]
theorem ofTensorProduct_coe_tmul (a : A) (m : M) :
    ofTensorProduct A M ((a : Completion A) ⊗ₜ m) = ↑(a • m) := by
  simp [ofTensorProduct_tmul]

/-- For fixed `m`, the canonical map is continuous in the completed scalar. -/
theorem continuous_ofTensorProduct_tmul (m : M) :
    Continuous fun a : Completion A ↦ ofTensorProduct A M (a ⊗ₜ m) :=
  (ContinuousLinearMap.toSpanSingleton A m).completion.continuous

end UniformSpace.Completion
