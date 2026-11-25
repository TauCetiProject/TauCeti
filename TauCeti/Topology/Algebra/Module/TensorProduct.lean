/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Linear maps and dense ranges on tensor products

For module topologies, a continuous algebra homomorphism `B → C` induces a continuous
map `B ⊗[A] M → C ⊗[A] M`. Only the source needs the module topology; the target can
be any topological `C`-module. This applies in particular to restriction maps on finite
modules over topological algebras.

The pure tensors also give a densely spanning family under any linear map with dense range.
-/

public section

open scoped TensorProduct

/-- The images of pure tensors under a linear map with dense range span a dense submodule. -/
theorem DenseRange.dense_span_range_tmul {R M N P : Type*} [CommSemiring R]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    [AddCommMonoid P] [Module R P] [TopologicalSpace P]
    {f : M ⊗[R] N →ₗ[R] P} (hf : DenseRange f) :
    Dense (Submodule.span R (Set.range fun p : M × N ↦ f (p.1 ⊗ₜ[R] p.2)) : Set P) := by
  have hspan : Submodule.span R (Set.range fun p : M × N ↦ p.1 ⊗ₜ[R] p.2) = ⊤ := by
    convert TensorProduct.span_tmul_eq_top R M N using 2
    ext x
    simp only [Set.mem_range, Set.mem_ofPred_eq, Prod.exists]
  change Dense (Submodule.span R (Set.range (f ∘ fun p : M × N ↦ p.1 ⊗ₜ[R] p.2)) : Set P)
  rw [Set.range_comp, ← Submodule.map_span, hspan, Submodule.map_top, LinearMap.coe_range]
  exact hf

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
