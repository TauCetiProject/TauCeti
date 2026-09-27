/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.DifferentialForm.Basic

/-!
# The exterior derivative of a constant differential form

A differential form on a normed space which does not depend on the base point has exterior
derivative zero, within any set and at any point. This complements the linearity lemmas of
`Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`, which cover the `0`-form case only
(`extDerivWithin_constOfIsEmpty`), and is what makes constant two-forms on a vector space closed.

## Main declarations

* `ContinuousAlternatingMap.extDerivWithin_const` and `ContinuousAlternatingMap.extDeriv_const`:
  the exterior derivative of a constant form vanishes.
-/

public section

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {n : ℕ}

namespace ContinuousAlternatingMap

/-- The exterior derivative within a set of a constant differential form vanishes. -/
@[simp]
theorem extDerivWithin_const (ω : E [⋀^Fin n]→L[𝕜] F) (s : Set E) (x : E) :
    extDerivWithin (fun _ ↦ ω) s x = 0 := by
  rw [extDerivWithin, fderivWithin_fun_const, Pi.zero_apply,
    ← alternatizeUncurryFinCLM_apply, ContinuousLinearMap.map_zero]

/-- The exterior derivative of a constant differential form vanishes. -/
@[simp]
theorem extDeriv_const (ω : E [⋀^Fin n]→L[𝕜] F) (x : E) :
    extDeriv (fun _ ↦ ω) x = 0 := by
  rw [← extDerivWithin_univ, extDerivWithin_const]

end ContinuousAlternatingMap

end
