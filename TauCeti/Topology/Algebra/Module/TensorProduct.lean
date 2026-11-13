/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Continuity of change of coefficients on tensor products

For module topologies, a continuous algebra homomorphism `B → C` induces a continuous
map `B ⊗[A] M → C ⊗[A] M`. Only the source needs the module topology; the target can
be any topological `C`-module. This applies in particular to restriction maps on finite
modules over topological algebras.
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
