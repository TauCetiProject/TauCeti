/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.LinearAlgebra.Multilinear.Basic
public import Mathlib.Topology.Algebra.Module.ModuleTopology

/-!
# Multilinear maps out of finite free modules with the module topology

A multilinear map `f` out of a finite free module `M` over a topological commutative ring `R`,
with its module topology, into any topological `R`-module is continuous
(`IsModuleTopology.continuous_multilinearMap`): in a basis `b` of `M`,
`f x = ∑ r, (∏ k, b.repr (x k) (r k)) • f (b ∘ r)`, a finite sum of products of continuous
coordinates. This extends Mathlib's continuity of bilinear maps out of finite modules
(`IsModuleTopology.continuous_bilinear_of_finite_left`) to any finite number of variables.

## Main results

* `IsModuleTopology.continuous_multilinearMap`: a multilinear map out of a finite free module with
  its module topology is continuous.
-/

public section

open Module

namespace IsModuleTopology

variable {R ι M N : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [Finite ι]
  [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsModuleTopology R M] [Module.Free R M]
  [Module.Finite R M] [AddCommGroup N] [Module R N] [TopologicalSpace N] [ContinuousAdd N]
  [ContinuousSMul R N]

/-- **A multilinear map out of a finite free module with its module topology is continuous**: in
a basis it is a finite sum of products of the continuous coordinates. -/
theorem continuous_multilinearMap (f : (ι → M) →ₘₗ[R] N) : Continuous f := by
  classical
  have := Fintype.ofFinite ι
  let b := Free.chooseBasis R M
  have hcoord (k : ι) (i : Free.ChooseBasisIndex R M) :
      Continuous fun x : ι → M ↦ b.repr (x k) i :=
    (continuous_of_linearMap ((Finsupp.lapply i).comp b.repr.toLinearMap)).comp
      (continuous_apply k)
  have hf : ⇑f = fun x ↦ ∑ r : ι → Free.ChooseBasisIndex R M,
      (∏ k, b.repr (x k) (r k)) • f fun k ↦ b (r k) := by
    funext x
    conv_lhs => rw [show x = fun k ↦ ∑ i, b.repr (x k) i • b i from
      funext fun k ↦ (b.sum_repr (x k)).symm]
    rw [f.map_sum]
    simp only [f.map_smul_univ, RingHom.id_apply]
  rw [hf]
  exact continuous_finsetSum _ fun r _ ↦
    (continuous_finsetProd _ fun k _ ↦ hcoord k (r k)).smul continuous_const

end IsModuleTopology

