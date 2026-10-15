/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Ball.Action

/-!
# Unit scalars acting on spheres

Mathlib's `Analysis.Normed.Module.Ball.Action`, due to Yury Kudryashov and Heather Macbeth, lets
the unit sphere of a normed field `𝕜` act on every sphere centred at zero in a normed `𝕜`-space.
This file records that the underlying vector of this action is scalar multiplication.

## Main declarations

* `TauCeti.Sphere.coe_sphere_smul`: Mathlib's action of unit scalars on a sphere is scalar
  multiplication.
-/

public section

namespace TauCeti

open Metric

namespace Sphere

/-- The coercion of Mathlib's action of the unit sphere of a normed field `𝕜` on a sphere of a
normed `𝕜`-space is scalar multiplication in the ambient space. -/
@[simp]
theorem coe_sphere_smul {𝕜 F : Type*} [NormedField 𝕜] [SeminormedAddCommGroup F]
    [NormedSpace 𝕜 F] {r : ℝ} (c : sphere (0 : 𝕜) 1) (x : sphere (0 : F) r) :
    ((c • x : sphere (0 : F) r) : F) = (c : 𝕜) • (x : F) :=
  (rfl)

end Sphere

end TauCeti
