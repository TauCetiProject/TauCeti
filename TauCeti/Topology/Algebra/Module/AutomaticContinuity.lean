/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Separation.Hausdorff

/-!
# Automatic continuity over compact coefficient rings

A finitely generated Hausdorff topological module over a compact ring has the module topology.
Consequently every linear map from it to a topological module is continuous. In particular this
applies to finitely generated compact Hausdorff topological `ℤ_p`-modules with continuous
addition and scalar action, allowing algebraic maps between abelian pro-`p` groups to be used
as maps of topological groups.

The construction uses Mathlib's module topology and finite free presentations, rather than a
second topology on finite modules.
-/

public section

variable {R : Type*} [Semiring R] [TopologicalSpace R] [IsTopologicalSemiring R]
  [CompactSpace R]
  {M : Type*} [AddCommMonoid M] [Module R M] [Module.Finite R M]
  [TopologicalSpace M] [T2Space M] [ContinuousAdd M] [ContinuousSMul R M]

/-- A finitely generated Hausdorff topological module over a compact semiring has the module
topology. -/
theorem TauCeti.isModuleTopology_of_finite_of_compactSpace : IsModuleTopology R M := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
  have hq := Topology.IsQuotientMap.of_surjective_continuous hf f.continuous_on_pi
  have hf' : @Continuous (Fin n → R) M inferInstance (moduleTopology R M) f := by
    let _ : TopologicalSpace M := moduleTopology R M
    let _ := ModuleTopology.continuousAdd R M
    let _ := ModuleTopology.continuousSMul R M
    exact IsModuleTopology.continuous_of_linearMap f
  exact IsModuleTopology.of_continuous_id
    ((@Topology.IsQuotientMap.continuous_iff _ _ M f id _ _ (moduleTopology R M) hq).mpr hf')

/-- Every linear map from a finitely generated Hausdorff topological module over a compact
semiring to a topological module is continuous. -/
theorem LinearMap.continuous_of_finite_of_compactSpace
    {N : Type*} [AddCommMonoid N] [Module R N] [TopologicalSpace N]
    [ContinuousAdd N] [ContinuousSMul R N] (f : M →ₗ[R] N) : Continuous f := by
  have := TauCeti.isModuleTopology_of_finite_of_compactSpace (R := R) (M := M)
  exact IsModuleTopology.continuous_of_linearMap f
