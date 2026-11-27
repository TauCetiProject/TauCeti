/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Filter.Map
public import Mathlib.Topology.Defs.Filter

/-!
# Limits of functions along a filter

`Filter.limUnder l f` depends only on the germ of `f` along `l`: functions which agree eventually
along `l` have the same `limUnder` (`Filter.limUnder_congr`). This holds for the junk value too,
so no convergence hypothesis is needed. Similarly, precomposing with a map pushes forward the
underlying filter (`Filter.limUnder_comp`).
-/

public section

namespace Filter

/-- Functions which agree eventually along `l` have the same limit along `l`. -/
theorem limUnder_congr {α X : Type*} [TopologicalSpace X] [Nonempty X] {l : Filter α}
    {f g : α → X} (h : f =ᶠ[l] g) : limUnder l f = limUnder l g :=
  congrArg lim (map_congr h)

/-- Precomposing with a map `φ` pushes forward the filter in `Filter.limUnder`. -/
theorem limUnder_comp {α β γ : Type*} {l : Filter α} [TopologicalSpace γ] [Nonempty γ]
    (g : β → γ) (φ : α → β) :
    limUnder l (g ∘ φ) = limUnder (l.map φ) g := by
  rw [limUnder, limUnder, Filter.map_map]

end Filter
