/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Iterated derivatives of indicators of open sets

Cutting a function off outside an open set `s` does not change its iterated derivatives at points
of `s`, since the indicator agrees with the function near such a point
(`TauCeti.iteratedDeriv_indicator_of_mem`).
-/

public section

open scoped Topology

namespace TauCeti

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- On an open set `s`, the iterated derivatives of the indicator `s.indicator f` at a point of `s`
are those of `f`. -/
theorem iteratedDeriv_indicator_of_mem {s : Set 𝕜} (hs : IsOpen s) {f : 𝕜 → E} {x : 𝕜}
    (hx : x ∈ s) (j : ℕ) : iteratedDeriv j (s.indicator f) x = iteratedDeriv j f x := by
  refine Filter.EventuallyEq.iteratedDeriv_eq j ?_
  filter_upwards [hs.mem_nhds hx] with y hy
  exact Set.indicator_of_mem hy f

end TauCeti
