/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.Notation

/-!
# Smooth bump functions on `C^n` manifolds

Mathlib's `SmoothBumpFunction.contMDiff` shows that a smooth bump function on a smooth manifold is
smooth. A smooth bump function is supported in a single chart, where it is a smooth function read
in that chart, so on a `C^n` manifold, `n ≤ ∞`, it is `C^n`
(`SmoothBumpFunction.contMDiff_of_isManifold`).
-/

public section

open scoped ContDiff Manifold

namespace SmoothBumpFunction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] {c : M}

/-- A smooth bump function on a `C^n` manifold, `n ≤ ∞`, is `C^n`; Mathlib's
`SmoothBumpFunction.contMDiff` assumes a smooth manifold. -/
theorem contMDiff_of_isManifold {n : ℕ∞ω} [ENat.LEInfty n] [IsManifold I n M]
    (ρ : SmoothBumpFunction I c) : CMDiff n ρ := by
  refine contMDiff_of_tsupport fun y hy ↦ ?_
  have hy' := ρ.tsupport_subset_chartAt_source hy
  exact (((ρ.contDiffAt (n := ⊤)).of_le ENat.LEInfty.out).contMDiffAt.comp _
    (contMDiffAt_extChartAt' hy')).congr_of_eventuallyEq
      (ρ.eqOn_source.eventuallyEq_of_mem <| (chartAt H c).open_source.mem_nhds hy')

end SmoothBumpFunction
