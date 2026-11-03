/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Curves which are an affine line outside a compact set

A curve `f : ℝ → F` which agrees with the affine line `s ↦ p + s • e` for `|s| ≥ R` has velocity
`e` at every parameter with `|s| > R` (`TauCeti.hasDerivAt_of_eq_line`). Such curves are the
arcs fixed near infinity which isotopies of arcs move.
-/

public section

namespace TauCeti

open Filter

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A map which is the affine line `s ↦ p + s • e` for `|s| ≥ R` has velocity `e` for `|s| > R`. -/
theorem hasDerivAt_of_eq_line {f : ℝ → F} {p e : F} {R : ℝ}
    (hline : ∀ s, R ≤ |s| → f s = p + s • e) {s : ℝ} (hs : R < |s|) : HasDerivAt f e s := by
  have hl : HasDerivAt (fun s : ℝ => p + s • e) e s := by
    simpa using ((hasDerivAt_id s).smul_const e).const_add p
  refine hl.congr_of_eventuallyEq ?_
  filter_upwards [(isOpen_lt continuous_const continuous_abs).mem_nhds hs] with x hx
  exact hline x hx.le

end TauCeti
