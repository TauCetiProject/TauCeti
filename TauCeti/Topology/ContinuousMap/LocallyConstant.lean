/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousMap.LocallyConstant
public import Mathlib.Topology.UniformSpace.CompactConvergence
import Mathlib.Topology.Separation.DisjointCover

/-!
# Density of locally constant functions

On a profinite space `X`, every continuous function to a uniform space is a uniform limit of
locally constant functions: `LocallyConstant.denseRange_toContinuousMap`. This is the density
statement used to extend functionals from locally constant test functions to all continuous
ones, for instance to extend the coefficients of measures on profinite spaces.

`ContinuousMap.intCastLocallyConstant` casts integer-valued continuous functions to locally
constant functions with values in any type with an integer cast.
-/

public section

namespace LocallyConstant

variable {X V : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [TotallyDisconnectedSpace X] [UniformSpace V]

/-- On a profinite space, locally constant functions are dense in the continuous functions to a
uniform space, for the topology of uniform convergence. -/
theorem denseRange_toContinuousMap :
    DenseRange (fun f : LocallyConstant X V ↦ (f : C(X, V))) := by
  refine fun f ↦ (mem_closure_iff_nhds_basis
    (nhds_basis_uniformity' ContinuousMap.hasBasis_compactConvergenceUniformity_of_compact)).mpr
    fun S hS ↦ ?_
  obtain ⟨n, q, g, hq, hqg⟩ :=
    ContinuousMap.exists_finite_approximation_of_mem_nhds_diagonal f
      (nhdsSet_diagonal_le_uniformity hS)
  exact ⟨_, ⟨⟨g ∘ q, (IsLocallyConstant.of_discrete g).comp_continuous hq⟩, rfl⟩, hqg⟩

end LocallyConstant

namespace ContinuousMap

/-- Cast an integer-valued continuous function to a locally constant function. -/
def intCastLocallyConstant {X R : Type*} [TopologicalSpace X] [IntCast R]
    (f : C(X, ℤ)) : LocallyConstant X R :=
  ⟨fun x ↦ (f x : R), ((IsLocallyConstant.iff_continuous _).mpr f.continuous).comp Int.cast⟩

/-- The locally constant integer cast agrees pointwise with the integer cast. -/
@[simp]
theorem intCastLocallyConstant_apply {X R : Type*} [TopologicalSpace X] [IntCast R]
    (f : C(X, ℤ)) (x : X) : f.intCastLocallyConstant (R := R) x = (f x : R) :=
  (rfl)

end ContinuousMap
