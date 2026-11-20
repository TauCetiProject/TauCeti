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
Consequently every linear map from it to a topological module is continuous
(`LinearMap.continuous_of_finite_of_compactSpace`) and upgrades to a bundled continuous linear map
(`LinearMap.toContinuousLinearMapOfFiniteOfCompactSpace`). In particular this applies to finitely
generated compact Hausdorff topological `ℤ_p`-modules with continuous addition and scalar action,
allowing algebraic maps between abelian pro-`p` groups to be used as maps of topological groups.

## Implementation notes

A surjection `(Fin n → R) →ₗ[R] M` is a continuous map from a compact space to a Hausdorff space,
hence a quotient map. The topology of `M` is therefore coinduced from the product topology, and
since every linear map out of `Fin n → R` is continuous into the module topology of `M`, the given
topology is no coarser than the module topology. It is also no finer, because the module topology
is the finest topology for which addition and scalar multiplication are continuous, so
`IsModuleTopology.of_continuous_id` identifies the two.
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

namespace LinearMap

variable {N : Type*} [AddCommMonoid N] [Module R N] [TopologicalSpace N]
  [ContinuousAdd N] [ContinuousSMul R N]

/-- Every linear map from a finitely generated Hausdorff topological module over a compact
semiring to a topological module is continuous. -/
theorem continuous_of_finite_of_compactSpace (f : M →ₗ[R] N) : Continuous f := by
  have := TauCeti.isModuleTopology_of_finite_of_compactSpace (R := R) (M := M)
  exact IsModuleTopology.continuous_of_linearMap f

/-- Upgrade a linear map out of a finitely generated Hausdorff topological module over a compact
semiring to a bundled continuous linear map. -/
def toContinuousLinearMapOfFiniteOfCompactSpace (f : M →ₗ[R] N) : M →L[R] N :=
  ⟨f, f.continuous_of_finite_of_compactSpace⟩

/-- `LinearMap.toContinuousLinearMapOfFiniteOfCompactSpace` has the same underlying function. -/
@[simp]
theorem coe_toContinuousLinearMapOfFiniteOfCompactSpace (f : M →ₗ[R] N) :
    ⇑f.toContinuousLinearMapOfFiniteOfCompactSpace = f :=
  (rfl)

/-- Forgetting continuity of `LinearMap.toContinuousLinearMapOfFiniteOfCompactSpace` recovers the
original linear map. -/
@[simp]
theorem toLinearMap_toContinuousLinearMapOfFiniteOfCompactSpace (f : M →ₗ[R] N) :
    (f.toContinuousLinearMapOfFiniteOfCompactSpace : M →ₗ[R] N) = f :=
  (rfl)

/-- Upgrading the zero linear map produces the zero continuous linear map. -/
@[simp]
theorem toContinuousLinearMapOfFiniteOfCompactSpace_zero :
    (0 : M →ₗ[R] N).toContinuousLinearMapOfFiniteOfCompactSpace = 0 := by
  ext
  simp

/-- Upgrading a sum of linear maps distributes over addition. -/
@[simp]
theorem toContinuousLinearMapOfFiniteOfCompactSpace_add (f g : M →ₗ[R] N) :
    (f + g).toContinuousLinearMapOfFiniteOfCompactSpace =
      f.toContinuousLinearMapOfFiniteOfCompactSpace +
        g.toContinuousLinearMapOfFiniteOfCompactSpace := by
  ext
  simp

/-- Upgrading a scalar multiple of a linear map commutes with scalar multiplication. -/
@[simp]
theorem toContinuousLinearMapOfFiniteOfCompactSpace_smul {S : Type*} [DistribSMul S N]
    [SMulCommClass R S N] [ContinuousConstSMul S N] (c : S) (f : M →ₗ[R] N) :
    (c • f).toContinuousLinearMapOfFiniteOfCompactSpace =
      c • f.toContinuousLinearMapOfFiniteOfCompactSpace := by
  ext
  simp

end LinearMap
