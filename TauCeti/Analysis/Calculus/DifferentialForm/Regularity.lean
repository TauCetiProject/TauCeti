/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import TauCeti.Analysis.Calculus.ContDiff.ContinuousAlternatingMap

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

/-- A `C^(n+1)` differential form has a `C^n` exterior derivative within a set with
unique derivatives; this is `contDiffOn_extDerivWithin` with `p = n + 1`, and covers
`n = ∞` and `n = ω`. -/
theorem contDiffOn_extDerivWithin_succ {n : WithTop ℕ∞}
    (hs : UniqueDiffOn 𝕜 s) (hω : ContDiffOn 𝕜 (n + 1) ω s) :
    ContDiffOn 𝕜 n (extDerivWithin ω s) s :=
  contDiffOn_extDerivWithin hω hs le_rfl

/-- A `C^p` form has a `C^r` exterior derivative at a point, provided `r + 1 ≤ p`. -/
theorem contDiffAt_extDeriv (hω : ContDiffAt 𝕜 p ω x) (hrp : r + 1 ≤ p) :
    ContDiffAt 𝕜 r (extDeriv ω) x := by
  rw [← contDiffWithinAt_univ] at hω ⊢
  simpa only [extDerivWithin_univ] using
    contDiffWithinAt_extDerivWithin hω uniqueDiffOn_univ hrp (Set.mem_univ x)

/-- Pulling back a `C^r` differential form by a `C^(r+1)` map gives a `C^r` form at a point.
Only the analytic order requires the arity factorial to be nonzero in the scalar field. -/
theorem _root_.ContDiffAt.differentialForm_pullback
    {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    {f : E → F} {η : F → F [⋀^Fin k]→L[𝕜] G}
    (hf : ContDiffAt 𝕜 (r + 1) f x) (hη : ContDiffAt 𝕜 r η (f x))
    (hr : r = ⊤ → (k.factorial : 𝕜) ≠ 0 := by
      intro h
      first | exact NeZero.ne _ | cases h) :
    ContDiffAt 𝕜 r (fun y ↦ (η (f y)).compContinuousLinearMap (fderiv 𝕜 f y)) x := by
  exact ((ContinuousAlternatingMap.contDiff_compContinuousLinearMapCLM
    (𝕜 := 𝕜) (E := E) (F := F) (G := G) (ι := Fin k) r
    (by simpa using hr)).contDiffAt.comp x
    (hf.fderiv_right le_rfl)).clm_apply
      (hη.comp x (hf.of_le le_self_add))

/-- A `C^p` form has a `C^r` exterior derivative, provided `r + 1 ≤ p`.
In particular, the exterior derivative preserves smooth forms. -/
theorem contDiff_extDeriv (hω : ContDiff 𝕜 p ω) (hrp : r + 1 ≤ p) :
    ContDiff 𝕜 r (extDeriv ω) :=
  contDiff_iff_contDiffAt.mpr fun _ ↦ contDiffAt_extDeriv hω.contDiffAt hrp

end TauCeti
