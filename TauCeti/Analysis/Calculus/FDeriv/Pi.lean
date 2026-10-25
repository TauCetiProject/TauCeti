/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Pi

/-!
# Differentiability of the coordinate slices of a function on a product

A function `f` on a finite product `∀ i, E i` which is differentiable at `y` is differentiable in
each variable separately: the slice `x ↦ f (update y i x)` through `y` in the `i`-th coordinate is
differentiable at `y i`.

## Main declarations

* `DifferentiableWithinAt.comp_update`: the slice of a function differentiable within a set, within
  any set of coordinates which `update y i` maps into it.
* `DifferentiableAt.comp_update`: the slice of a function differentiable at a point.
-/

public section

open Function

namespace TauCeti

variable {𝕜 ι : Type*} [NontriviallyNormedField 𝕜] [Finite ι] [DecidableEq ι]
  {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f : (∀ i, E i) → F} {y : ∀ i, E i}

/-- A function differentiable within `s` at `y` is differentiable in its `i`-th variable: the slice
`x ↦ f (update y i x)` is differentiable at `y i` within any set `t` that `update y i` maps into
`s`. -/
theorem _root_.DifferentiableWithinAt.comp_update {s : Set (∀ i, E i)}
    (h : DifferentiableWithinAt 𝕜 f s y) (i : ι) {t : Set (E i)}
    (hst : Set.MapsTo (update y i) t s) :
    DifferentiableWithinAt 𝕜 (fun x => f (update y i x)) t (y i) := by
  have := Fintype.ofFinite ι
  refine DifferentiableWithinAt.comp (y i) ?_
    (hasFDerivAt_update (𝕜 := 𝕜) y (y i)).differentiableAt.differentiableWithinAt hst
  rwa [update_eq_self]

/-- A function differentiable at `y` is differentiable in its `i`-th variable: the slice
`x ↦ f (update y i x)` is differentiable at `y i`. -/
theorem _root_.DifferentiableAt.comp_update (h : DifferentiableAt 𝕜 f y) (i : ι) :
    DifferentiableAt 𝕜 (fun x => f (update y i x)) (y i) := by
  simpa only [differentiableWithinAt_univ] using
    h.differentiableWithinAt.comp_update i (Set.mapsTo_univ _ Set.univ)

end TauCeti
