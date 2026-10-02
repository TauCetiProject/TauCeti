/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Module.GeneralLinearGroup
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Continuity of extension of scalars

Let `K → L` be a continuous homomorphism of commutative semirings carrying topologies and let
`V` be a `K`-module. Extension of scalars sends an endomorphism of `V` to an endomorphism of
`L ⊗[K] V`. This operation is continuous for the canonical module topologies: it is semilinear
with respect to `K → L`. Consequently scalar extension also gives a continuous homomorphism
between the corresponding general linear groups.

These results provide the topological infrastructure for localizing matrix-defined point groups.

## Main results

* `LinearMap.continuous_baseChange`: scalar extension of endomorphisms is continuous.
* `LinearEquiv.continuous_baseChange`: scalar extension of linear automorphisms is continuous.
-/

public section

open scoped TensorProduct

namespace LinearMap

universe u v w

variable {K : Type u} {L : Type v} {V : Type w}
  [CommSemiring K] [CommSemiring L] [Algebra K L]
  [TopologicalSpace K] [TopologicalSpace L]
  [AddCommMonoid V] [Module K V]

/-- Extension of scalars is continuous on endomorphism spaces equipped with their canonical
module topologies, provided the scalar homomorphism is continuous. -/
@[fun_prop]
theorem continuous_baseChange (hKL : Continuous (algebraMap K L)) :
    Continuous (fun f : Module.End K V => f.baseChange L) := by
  let F : Module.End K V →ₛₗ[algebraMap K L] Module.End L (L ⊗[K] V) :=
    { (Module.End.baseChangeHom K L V).toLinearMap with
      map_smul' := fun c f =>
        (map_smul (Module.End.baseChangeHom K L V) c f).trans
          (IsScalarTower.algebraMap_smul L c (f.baseChange L)).symm }
  let _ : ContinuousAdd (Module.End L (L ⊗[K] V)) :=
    IsModuleTopology.toContinuousAdd L _
  exact IsModuleTopology.continuous_of_linearMapₛₗ hKL F

end LinearMap

namespace LinearEquiv

universe u v w

variable {K : Type u} {L : Type v} {V : Type w}
  [CommSemiring K] [CommSemiring L] [Algebra K L]
  [TopologicalSpace K] [TopologicalSpace L]
  [AddCommMonoid V] [Module K V] [ContinuousMul (Module.End K V)]

/-- Extension of scalars is continuous on general linear groups in their forward-and-inverse
topologies, provided the scalar homomorphism is continuous. -/
@[fun_prop]
theorem continuous_baseChange (hKL : Continuous (algebraMap K L)) :
    Continuous (fun e : V ≃ₗ[K] V => e.baseChange K L V V) := by
  rw [TauCeti.continuous_linearEquiv_iff]
  constructor
  · exact ((LinearMap.continuous_baseChange (V := V) hKL).comp
        TauCeti.continuous_linearEquiv_toLinearMap).congr fun e =>
          (LinearEquiv.coe_baseChange K L V V e).symm
  · have h := (LinearMap.continuous_baseChange (V := V) hKL).comp
        (TauCeti.continuous_linearEquiv_toLinearMap.comp continuous_inv)
    refine h.congr fun e => ?_
    exact congrArg LinearEquiv.toLinearMap (LinearEquiv.baseChange_inv K L V e).symm

end LinearEquiv
