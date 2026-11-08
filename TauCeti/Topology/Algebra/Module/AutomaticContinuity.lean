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

## Implementation notes

A surjection `(Fin n → R) →ₗ[R] M` is a continuous map from a compact space to a Hausdorff space,
hence a quotient map. The topology of `M` is therefore coinduced from the product topology, and
since every linear map out of `Fin n → R` is continuous into the module topology of `M`, the given
topology is no finer than the module topology.
-/

public section

variable {R : Type*} [Semiring R] [TopologicalSpace R] [CompactSpace R]
  {M : Type*} [AddCommMonoid M] [Module R M] [Module.Finite R M]
  [TopologicalSpace M] [T2Space M] [ContinuousAdd M] [ContinuousSMul R M]

/-- A finitely generated Hausdorff topological module over a compact semiring has the module
topology. -/
theorem TauCeti.isModuleTopology_of_finite_of_compactSpace : IsModuleTopology R M := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
  refine .of_continuous_id ?_
  rw [(Topology.IsQuotientMap.of_surjective_continuous hf f.continuous_on_pi).eq_coinduced,
    continuous_coinduced_dom]
  -- It remains to see that `f` is continuous for the module topology on `M`.
  let _ : TopologicalSpace M := moduleTopology R M
  have := ModuleTopology.continuousAdd R M
  have := ModuleTopology.continuousSMul R M
  exact f.continuous_on_pi

/-- Every linear map from a finitely generated Hausdorff topological module over a compact
semiring to a topological module is continuous. -/
theorem LinearMap.continuous_of_finite_of_compactSpace
    {N : Type*} [AddCommMonoid N] [Module R N] [TopologicalSpace N]
    [ContinuousAdd N] [ContinuousSMul R N] (f : M →ₗ[R] N) : Continuous f := by
  have := TauCeti.isModuleTopology_of_finite_of_compactSpace (R := R) (M := M)
  exact IsModuleTopology.continuous_of_linearMap f
