/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Density.Basic
public import Mathlib.Topology.Algebra.Module.Equiv.Basic
public import Mathlib.Topology.Algebra.Ring.Real

/-!
# The topology of the density line

Densities carry the topology of pointwise convergence on tuples. In top degree,
evaluation on any basis is a continuous linear equivalence with ℝ. Thus this topology
is the rank-one vector-space topology, independently of the evaluation basis.
The coefficient change between two bases is multiplication by their absolute
determinant. These coordinates are suitable as local models of the density line bundle.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Chapter 16,
  Densities.
-/

public section

namespace TauCeti.Density

open Topology

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {m : ℕ}

/-- The intrinsic pointwise topology on densities. -/
instance : TopologicalSpace (Density V m) :=
  TopologicalSpace.induced (DFunLike.coe : Density V m → (Fin m → V) → ℝ) inferInstance

/-- The inclusion of densities into functions on tuples is a topological embedding. -/
theorem isEmbedding_coe :
    IsEmbedding (DFunLike.coe : Density V m → (Fin m → V) → ℝ) :=
  DFunLike.coe_injective.isEmbedding_induced

instance : T2Space (Density V m) := isEmbedding_coe.t2Space

instance : IsTopologicalAddGroup (Density V m) :=
  isTopologicalAddGroup_induced
    (⟨⟨DFunLike.coe, rfl⟩, fun _ _ ↦ rfl⟩ : Density V m →+ ((Fin m → V) → ℝ))

instance : ContinuousSMul ℝ (Density V m) :=
  ContinuousSMul.induced
    ({ toFun := DFunLike.coe, map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl } :
      Density V m →ₗ[ℝ] ((Fin m → V) → ℝ))

/-- Evaluation on a tuple is continuous. -/
@[fun_prop]
theorem continuous_eval (v : Fin m → V) : Continuous (fun μ : Density V m ↦ μ v) :=
  (continuous_apply v).comp isEmbedding_coe.continuous

end TauCeti.Density

namespace Module.Basis

open TauCeti

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {m : ℕ}

/-- Constructing a density with coefficient `c` in a fixed basis is continuous in `c`. -/
@[fun_prop]
theorem continuous_density (b : Module.Basis (Fin m) ℝ V) : Continuous (density b) := by
  apply continuous_induced_rng.2
  apply continuous_pi
  intro v
  simp only [Function.comp_def, density_apply]
  fun_prop

/-- Evaluation on any basis is a topological linear coordinate on the density line. -/
noncomputable def densityContinuousLinearEquiv (b : Module.Basis (Fin m) ℝ V) :
    Density V m ≃L[ℝ] ℝ where
  toLinearEquiv := densityEquiv b
  continuous_toFun := by
    convert Density.continuous_eval b using 1
    exact funext (densityEquiv_apply b)
  continuous_invFun := by
    convert continuous_density b using 1
    exact funext (densityEquiv_symm_apply b)

@[simp]
theorem densityContinuousLinearEquiv_apply (b : Module.Basis (Fin m) ℝ V) (μ : Density V m) :
    densityContinuousLinearEquiv b μ = μ b := densityEquiv_apply b μ

@[simp]
theorem densityContinuousLinearEquiv_symm_apply (b : Module.Basis (Fin m) ℝ V) (c : ℝ) :
    (densityContinuousLinearEquiv b).symm c = density b c := densityEquiv_symm_apply b c

/-- Continuity into the density line can be checked in any single basis. -/
theorem continuous_iff_eval_basis {X : Type*} [TopologicalSpace X]
    (b : Module.Basis (Fin m) ℝ V) {f : X → Density V m} :
    Continuous f ↔ Continuous (fun x ↦ f x b) := by
  simpa only [Function.comp_def, ContinuousLinearEquiv.coe_toHomeomorph,
    densityContinuousLinearEquiv_apply] using
    (densityContinuousLinearEquiv b).toHomeomorph.comp_continuous_iff (f := f) |>.symm

end Module.Basis
