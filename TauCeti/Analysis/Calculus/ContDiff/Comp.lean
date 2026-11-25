/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# Smoothness of iterates

The iterate of a map which is `Cⁿ` along an orbit is `Cⁿ` at its starting point
(`TauCeti.contDiffAt_iterate`), as in the differentiable case `TauCeti.differentiableAt_iterate`.
The starting point need not be fixed.

## Main results

* `TauCeti.contDiffAt_iterate`: iterates are `Cⁿ` along `Cⁿ` orbits.
-/

public section

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

namespace TauCeti

/-- **Iterates are `Cⁿ` along `Cⁿ` orbits.** If `f` is `Cⁿ` at the first `k` points `f^[j] x`,
`j < k`, of the orbit of `x`, then `f^[k]` is `Cⁿ` at `x`. The point `x` need not be fixed. -/
theorem contDiffAt_iterate {n : WithTop ℕ∞} {f : E → E} {x : E} :
    ∀ {k : ℕ}, (∀ j < k, ContDiffAt 𝕜 n f (f^[j] x)) → ContDiffAt 𝕜 n f^[k] x
  | 0, _ => contDiffAt_id
  | k + 1, h => by
    rw [Function.iterate_succ']
    exact (h k (by omega)).comp x (contDiffAt_iterate fun j hj ↦ h j (by omega))

end TauCeti
