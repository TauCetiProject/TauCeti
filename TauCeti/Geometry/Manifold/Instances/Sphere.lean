/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# Evaluation lemmas for the stereographic charts of the sphere

Mathlib charts the unit sphere of an `(n + 1)`-dimensional real inner product space by
stereographic projection, the preferred chart at `v` projecting from the antipode `-v`
(`EuclideanSpace.instChartedSpaceSphere`). This file records the two facts about these charts
that computations in a chart at a chosen point use: which stereographic projection the preferred
chart is, and that the extended chart at `v` sends `v` to the origin of the model space.

## Main results

* `TauCeti.chartAt_sphere`: the preferred chart at `v` is `stereographic' n (-v)`.
* `TauCeti.extChartAt_sphere_apply_self`: the preferred extended chart at `v` sends `v` to `0`.
-/

public section

open Function Metric Module
open scoped Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]

/-- The preferred chart of the sphere at `v` is the stereographic projection from `-v`. -/
theorem chartAt_sphere (v : sphere (0 : E) 1) :
    chartAt (EuclideanSpace ℝ (Fin n)) v = stereographic' n (-v) :=
  rfl

-- Not `@[simp]`: simp unfolds `extChartAt (𝓡 n) v v` to `chartAt _ v v` before this lemma can
-- fire, so it fails `simpNF`.
/-- The preferred extended chart of the sphere at `v` sends `v` to the origin. -/
theorem extChartAt_sphere_apply_self (v : sphere (0 : E) 1) : extChartAt (𝓡 n) v v = 0 := by
  rw [extChartAt_coe, modelWithCornersSelf_coe, id_comp, chartAt_sphere, stereographic',
    OpenPartialHomeomorph.trans_apply, stereographic_neg_apply,
    Homeomorph.toOpenPartialHomeomorph_apply, LinearIsometryEquiv.coe_toHomeomorph, map_zero]

end TauCeti
