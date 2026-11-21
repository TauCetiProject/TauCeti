/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.BilinearMap.Alternating
public import TauCeti.Topology.Algebra.Module.FiniteDimension

/-!
# Alternating bilinear maps as continuous two-forms

On a finite-dimensional Hausdorff topological vector space over a complete nontrivially normed
field, an alternating bilinear map is the same as a continuous alternating two-form. The linear
equivalence `TauCeti.alternatingBilinMapEquivContinuousAlternatingMap` preserves evaluation on
an ordered pair and commutes with pullback along continuous linear maps. It does not alternatize a
bilinear map: there is no factor of two.

Taking the coefficient space to be the scalar field identifies alternating bilinear forms
(`LinearMap.BilinForm`) with continuous two-forms. Thus the same form can be used in both the
bilinear symplectic API and the continuous alternating differential-form API. The construction
uses `TauCeti.alternatingBilinMapEquiv` and `AlternatingMap.toContinuousAlternatingMap`.
-/

public section

variable (𝕜 V N : Type*) [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [ContinuousSMul 𝕜 V] [T2Space V] [FiniteDimensional 𝕜 V]
  [AddCommGroup N] [Module 𝕜 N] [TopologicalSpace N] [ContinuousAdd N] [ContinuousSMul 𝕜 N]

namespace TauCeti

/-- Alternating bilinear maps on a finite-dimensional space, identified with continuous
alternating two-forms by their unchanged evaluation on ordered pairs. -/
def alternatingBilinMapEquivContinuousAlternatingMap :
    alternatingBilinMap 𝕜 V N ≃ₗ[𝕜] V [⋀^Fin 2]→L[𝕜] N :=
  (alternatingBilinMapEquiv 𝕜 V N).trans AlternatingMap.toContinuousAlternatingMap

variable {𝕜 V N}

/-- Passing from an alternating bilinear map to a continuous two-form preserves evaluation. -/
@[simp]
theorem alternatingBilinMapEquivContinuousAlternatingMap_apply
    (B : alternatingBilinMap 𝕜 V N) (v : Fin 2 → V) :
    alternatingBilinMapEquivContinuousAlternatingMap 𝕜 V N B v = B.val (v 0) (v 1) := by
  simp [alternatingBilinMapEquivContinuousAlternatingMap]

/-- The inverse identification reads a continuous two-form on an ordered pair. -/
@[simp]
theorem alternatingBilinMapEquivContinuousAlternatingMap_symm_apply
    (A : V [⋀^Fin 2]→L[𝕜] N) (x y : V) :
    ((alternatingBilinMapEquivContinuousAlternatingMap 𝕜 V N).symm A).val x y = A ![x, y] := by
  simp [alternatingBilinMapEquivContinuousAlternatingMap]

end TauCeti

namespace ContinuousLinearMap

open TauCeti

variable {𝕜 V N} {W : Type*} [AddCommGroup W] [Module 𝕜 W] [TopologicalSpace W]
  [IsTopologicalAddGroup W] [ContinuousSMul 𝕜 W] [T2Space W] [FiniteDimensional 𝕜 W]

/-- The bilinear/two-form identification is natural under continuous linear pullback. -/
@[simp]
theorem alternatingBilinMapEquivContinuousAlternatingMap_pullback (L : W →L[𝕜] V)
    (B : alternatingBilinMap 𝕜 V N) :
    alternatingBilinMapEquivContinuousAlternatingMap 𝕜 W N
        (L.toLinearMap.alternatingBilinMapPullback B) =
      (alternatingBilinMapEquivContinuousAlternatingMap 𝕜 V N B).compContinuousLinearMap L := by
  ext v
  simp

end ContinuousLinearMap
