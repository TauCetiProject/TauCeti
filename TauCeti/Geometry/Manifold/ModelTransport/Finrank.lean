/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ChartedSpace
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import TauCeti.Geometry.Manifold.ModelTransport.Homeomorph

/-!
# Recharting a topological manifold between finite-dimensional model spaces of equal dimension

Any two finite-dimensional Hausdorff topological vector spaces `E` and `E'` of equal dimension over
a complete nontrivially normed field `𝕜` (in possibly different universes) are related by
`ContinuousLinearEquiv.ofFinrankEq`. Postcomposing charts with that continuous linear equivalence
(`Homeomorph.chartedSpaceComp`) transports a `ChartedSpace E M` structure to `ChartedSpace E' M`
(`ChartedSpace.ofFinrankEq`),
allowing topological-manifold theorems proved with `E` and `M` in a common universe to be
transferred to arbitrary model-space universes.

## Main definitions and results

* `ChartedSpace.ofFinrankEq`: rechart `M` from `E` to `E'` when `finrank 𝕜 E = finrank 𝕜 E'`.
* `ChartedSpace.chartAt_ofFinrankEq` and `ChartedSpace.atlas_ofFinrankEq`: the preferred charts and
  atlas of `ChartedSpace.ofFinrankEq`.
-/

public section

noncomputable section

open scoped Manifold

namespace ChartedSpace

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul 𝕜 E] [T2Space E] [FiniteDimensional 𝕜 E]
  {E' : Type*} [AddCommGroup E'] [Module 𝕜 E'] [TopologicalSpace E'] [IsTopologicalAddGroup E']
  [ContinuousSMul 𝕜 E'] [T2Space E'] [FiniteDimensional 𝕜 E']

/-- Transport a `ChartedSpace E M` structure to `ChartedSpace E' M` along
`ContinuousLinearEquiv.ofFinrankEq` when `E` and `E'` have the same finite dimension over `𝕜`. -/
@[instance_reducible]
def ofFinrankEq (M : Type*) [TopologicalSpace M] [ChartedSpace E M]
    (h : Module.finrank 𝕜 E = Module.finrank 𝕜 E') : ChartedSpace E' M :=
  (ContinuousLinearEquiv.ofFinrankEq h).toHomeomorph.chartedSpaceComp M

/-- The preferred chart at `x` in `ChartedSpace.ofFinrankEq M h` is `chartAt E x` postcomposed with
`ContinuousLinearEquiv.ofFinrankEq h`. -/
theorem chartAt_ofFinrankEq {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
    (h : Module.finrank 𝕜 E = Module.finrank 𝕜 E') (x : M) :
    (letI := ofFinrankEq M h; chartAt E' x) =
      chartAt E x ≫ₕ
        (ContinuousLinearEquiv.ofFinrankEq h).toHomeomorph.toOpenPartialHomeomorph :=
  (ContinuousLinearEquiv.ofFinrankEq h).toHomeomorph.chartAt_chartedSpaceComp x

/-- The atlas of `ChartedSpace.ofFinrankEq M h` consists of the charts of `M` postcomposed with
`ContinuousLinearEquiv.ofFinrankEq h`. -/
theorem atlas_ofFinrankEq (M : Type*) [TopologicalSpace M] [ChartedSpace E M]
    (h : Module.finrank 𝕜 E = Module.finrank 𝕜 E') :
    (letI := ofFinrankEq M h; atlas E' M) =
      (· ≫ₕ (ContinuousLinearEquiv.ofFinrankEq h).toHomeomorph.toOpenPartialHomeomorph) ''
        atlas E M :=
  (ContinuousLinearEquiv.ofFinrankEq h).toHomeomorph.atlas_chartedSpaceComp M

end ChartedSpace
