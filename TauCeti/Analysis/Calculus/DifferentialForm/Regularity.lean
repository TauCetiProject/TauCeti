/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.DifferentialForm.Basic

/-!
# Regularity of the exterior derivative

The exterior derivative of a `C^(r+1)` form is `C^r`. The relative statements use
`UniqueDiffOn`, not openness, so they apply to boundary and corner chart ranges.
In particular, the exterior derivative preserves smooth fixed-coefficient forms.
Neither the model space nor the coefficient space needs to be finite-dimensional or complete.

We use Mathlib's `ContinuousAlternatingMap.alternatizeUncurryFinCLM`: the exterior derivative
is this continuous linear map applied to the derivative of the form. Thus regularity follows
from the corresponding regularity of `fderivWithin` without a new alternatization construction.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 14.
-/

public section

namespace TauCeti

open ContinuousAlternatingMap

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {k : ℕ} {r p : WithTop ℕ∞} {ω : E → E [⋀^Fin k]→L[𝕜] F}
  {s : Set E} {x : E}

/-- A `C^p` form has a `C^r` exterior derivative within a unique-differentiability set
at a point of that set, provided `r + 1 ≤ p`. -/
theorem contDiffWithinAt_extDerivWithin (hω : ContDiffWithinAt 𝕜 p ω s x)
    (hs : UniqueDiffOn 𝕜 s) (hrp : r + 1 ≤ p) (hx : x ∈ s) :
    ContDiffWithinAt 𝕜 r (extDerivWithin ω s) s x := by
  simpa +unfoldPartialApp only [Function.comp_def, alternatizeUncurryFinCLM_apply,
    extDerivWithin] using
    (alternatizeUncurryFinCLM 𝕜 E F).contDiff.comp_contDiffWithinAt
      (hω.fderivWithin_right hs hrp hx)

/-- A `C^p` form on a unique-differentiability set has a `C^r` exterior derivative
within that set, provided `r + 1 ≤ p`. This includes smooth forms by taking `r = p = ∞`. -/
theorem contDiffOn_extDerivWithin (hω : ContDiffOn 𝕜 p ω s)
    (hs : UniqueDiffOn 𝕜 s) (hrp : r + 1 ≤ p) :
    ContDiffOn 𝕜 r (extDerivWithin ω s) s :=
  fun x hx ↦ contDiffWithinAt_extDerivWithin (hω x hx) hs hrp hx

/-- A `C^p` form has a `C^r` exterior derivative at a point, provided `r + 1 ≤ p`. -/
theorem contDiffAt_extDeriv (hω : ContDiffAt 𝕜 p ω x) (hrp : r + 1 ≤ p) :
    ContDiffAt 𝕜 r (extDeriv ω) x := by
  rw [← contDiffWithinAt_univ] at hω ⊢
  simpa only [extDerivWithin_univ] using
    contDiffWithinAt_extDerivWithin hω uniqueDiffOn_univ hrp (Set.mem_univ x)

/-- A `C^p` form has a `C^r` exterior derivative, provided `r + 1 ≤ p`.
In particular, the exterior derivative preserves smooth forms. -/
theorem contDiff_extDeriv (hω : ContDiff 𝕜 p ω) (hrp : r + 1 ≤ p) :
    ContDiff 𝕜 r (extDeriv ω) :=
  contDiff_iff_contDiffAt.mpr fun _ ↦ contDiffAt_extDeriv hω.contDiffAt hrp

end TauCeti
