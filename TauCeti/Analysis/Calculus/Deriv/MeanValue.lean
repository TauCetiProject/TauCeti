/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Monotonicity from a pointwise nonnegative derivative

Mathlib's `monotoneOn_of_hasDerivWithinAt_nonneg` asks for continuity on a convex set `D ⊆ ℝ` and
for derivatives within `interior D` at each interior point
(`HasDerivWithinAt f (f' x) (interior D) x`). When the function has a derivative (`HasDerivAt`)
at every point of `D`, both hypotheses follow, and `TauCeti.monotoneOn_of_hasDerivAt_nonneg`
packages this common special case; as in Mathlib, the derivative need only be nonnegative on
`interior D`.
-/

public section

namespace TauCeti

/-- A function with a derivative at every point of a convex set `D ⊆ ℝ`, nonnegative on the
interior of `D`, is monotone on `D`. -/
theorem monotoneOn_of_hasDerivAt_nonneg {D : Set ℝ} (hD : Convex ℝ D) {f f' : ℝ → ℝ}
    (hf : ∀ x ∈ D, HasDerivAt f (f' x) x) (hf' : ∀ x ∈ interior D, 0 ≤ f' x) :
    MonotoneOn f D :=
  monotoneOn_of_hasDerivWithinAt_nonneg hD
    (fun x hx => (hf x hx).continuousAt.continuousWithinAt)
    (fun x hx => (hf x (interior_subset hx)).hasDerivWithinAt) hf'

end TauCeti
