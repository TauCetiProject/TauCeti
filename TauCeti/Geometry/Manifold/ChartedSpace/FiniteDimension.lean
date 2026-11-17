/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import TauCeti.Geometry.Manifold.ChartedSpace

/-!
# Re-charting manifolds modelled on finite-dimensional vector spaces

Any two finite-dimensional Hausdorff topological vector spaces `E` and `F` of the same dimension
over a complete nontrivially normed field `𝕜` are continuously linearly equivalent, even when they
live in different universes (`ContinuousLinearEquiv.ofFinrankEq`). Postcomposing the charts of a
charted space `X` modelled on `E` with this equivalence yields a charted-space structure on `X`
modelled on `F` (`ChartedSpace.ofFinrankEq`).

In particular, a topological manifold `X : Type w` modelled on a finite-dimensional real normed
space `E : Type u` can be re-charted on `ULift.{w} (Fin (Module.finrank ℝ E)) → ℝ` or
`EuclideanSpace ℝ (ULift.{w} (Fin (Module.finrank ℝ E)))` in the universe `w` of `X`, reducing
universe-polymorphic topological-manifold statements to the same-universe case.

## Main definitions and results

* `ChartedSpace.ofFinrankEq`: re-charts a charted space modelled on `E` onto any finite-dimensional
  Hausdorff topological vector space `F` of equal `Module.finrank 𝕜`.
* `ChartedSpace.ofFinrankEq_def`: `ofFinrankEq h` equals `transHomeomorph` along
  `ContinuousLinearEquiv.ofFinrankEq h`.
* `ChartedSpace.ofFinrankEq_chartAt` and `ChartedSpace.ofFinrankEq_atlas`: the preferred charts
  and atlas of `ChartedSpace.ofFinrankEq`.
-/

public section

namespace ChartedSpace

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [T2Space E] [FiniteDimensional 𝕜 E]
  {F : Type*} [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul 𝕜 F] [T2Space F] [FiniteDimensional 𝕜 F]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]

/-- Re-chart a space `X` modelled on a finite-dimensional Hausdorff topological vector space `E`
over a complete nontrivially normed field `𝕜` onto any finite-dimensional Hausdorff topological
vector space `F` of the same dimension, possibly in a different universe. -/
@[instance_reducible]
noncomputable def ofFinrankEq (h : Module.finrank 𝕜 E = Module.finrank 𝕜 F) :
    ChartedSpace F X :=
  transHomeomorph (ContinuousLinearEquiv.ofFinrankEq h).toHomeomorph

/-- `ChartedSpace.ofFinrankEq h` is obtained by transporting charts along
`ContinuousLinearEquiv.ofFinrankEq h`. -/
theorem ofFinrankEq_def (h : Module.finrank 𝕜 E = Module.finrank 𝕜 F) :
    ofFinrankEq (X := X) h =
      transHomeomorph (ContinuousLinearEquiv.ofFinrankEq h).toHomeomorph :=
  (rfl)

-- Neither `ofFinrankEq_chartAt` nor `ofFinrankEq_atlas` is tagged `@[simp]`: `simpNF` runs in
-- non-module mode where `ofFinrankEq` (`@[instance_reducible]`) unfolds to `transHomeomorph`,
-- reducing both LHSs via `transHomeomorph_chartAt` and `transHomeomorph_atlas`.

/-- The preferred chart of `ChartedSpace.ofFinrankEq h` at `x` is the original chart at `x`
postcomposed with `ContinuousLinearEquiv.ofFinrankEq h`. -/
@[mfld_simps]
theorem ofFinrankEq_chartAt (h : Module.finrank 𝕜 E = Module.finrank 𝕜 F) (x : X) :
    letI := ofFinrankEq (X := X) h
    chartAt F x =
      (chartAt E x).transHomeomorph (ContinuousLinearEquiv.ofFinrankEq h).toHomeomorph :=
  transHomeomorph_chartAt (ContinuousLinearEquiv.ofFinrankEq h).toHomeomorph x

/-- The atlas of `ChartedSpace.ofFinrankEq h` consists of the original charts postcomposed with
`ContinuousLinearEquiv.ofFinrankEq h`. -/
@[mfld_simps]
theorem ofFinrankEq_atlas (h : Module.finrank 𝕜 E = Module.finrank 𝕜 F) :
    letI := ofFinrankEq (X := X) h
    atlas F X =
      (·.transHomeomorph (ContinuousLinearEquiv.ofFinrankEq h).toHomeomorph) '' atlas E X :=
  transHomeomorph_atlas (ContinuousLinearEquiv.ofFinrankEq h).toHomeomorph

end ChartedSpace
