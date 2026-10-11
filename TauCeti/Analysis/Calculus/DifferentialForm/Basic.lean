/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.DifferentialForm.Basic

/-!
# The exterior derivative within a set depends only on the germ of the set

The exterior derivative `extDerivWithin ω s x` of a differential form on a normed space is the
alternatization of `fderivWithin 𝕜 ω s x`, so, like the derivative, it only sees the set `s`
near `x`. These are the exterior-derivative versions of `fderivWithin_congr_set'` and
`fderivWithin_congr_set`; they are what makes the exterior derivative of forms on manifolds,
computed in charts, insensitive to the set away from the base point.
-/

public section

open Filter Set
open scoped Topology

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {n : ℕ} {ω : E → E [⋀^Fin n]→L[𝕜] F} {s t : Set E} {x : E}

namespace TauCeti

/-- The exterior derivative within a set does not change when the set is modified away from a
point `y`, as long as it is unchanged near the base point (punctured at `y`). -/
theorem extDerivWithin_congr_set' (y : E) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) :
    extDerivWithin ω s x = extDerivWithin ω t x := by
  rw [extDerivWithin, extDerivWithin, fderivWithin_congr_set' y h]

/-- The exterior derivative within a set only depends on the germ of the set at the base
point. -/
theorem extDerivWithin_congr_set (h : s =ᶠ[𝓝 x] t) :
    extDerivWithin ω s x = extDerivWithin ω t x :=
  extDerivWithin_congr_set' x <| h.filter_mono inf_le_left

end TauCeti

end
