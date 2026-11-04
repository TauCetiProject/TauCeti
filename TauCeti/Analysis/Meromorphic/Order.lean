/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Normed.Module.Convex

/-!
# Finite meromorphic order on closed discs from boundary conditions

On a nonempty closed disc `closedBall c R` over `ℝ` or `ℂ` (`RCLike 𝕜`), the boundary point
`c + R` lies on `sphere c R` and `closedBall c R` is convex, hence preconnected. Consequently,
if a meromorphic function on `closedBall c R` has finite meromorphic order at every point of
`sphere c R` — in particular, if an analytic function on `closedBall c R` does not vanish on
`sphere c R` — then `MeromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected` propagates finite
meromorphic order to every point of `closedBall c R`.

## Main results

* `MeromorphicOn.meromorphicOrderAt_ne_top_of_forall_mem_sphere`: finite meromorphic order on the
  bounding sphere propagates throughout the closed disc.
* `AnalyticOnNhd.meromorphicOrderAt_ne_top_of_forall_mem_sphere_ne_zero`: an analytic function on
  a closed disc that does not vanish on the bounding sphere has finite meromorphic order throughout
  the closed disc.
-/

public section

open Metric

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {f : 𝕜 → E} {c : 𝕜} {R : ℝ}

/-- If `f` is meromorphic on `closedBall c R` and has finite meromorphic order at every point of
the bounding sphere `sphere c R`, then `f` has finite meromorphic order throughout
`closedBall c R`. -/
theorem MeromorphicOn.meromorphicOrderAt_ne_top_of_forall_mem_sphere
    (hf : MeromorphicOn f (closedBall c R))
    (hsphere : ∀ ζ ∈ sphere c R, meromorphicOrderAt f ζ ≠ ⊤)
    {z : 𝕜} (hz : z ∈ closedBall c R) : meromorphicOrderAt f z ≠ ⊤ := by
  have hR : 0 ≤ R := dist_nonneg.trans (mem_closedBall.1 hz)
  have hmem : c + (R : 𝕜) ∈ sphere c R := by simp [abs_of_nonneg hR]
  exact hf.meromorphicOrderAt_ne_top_of_isPreconnected
    (convex_closedBall c R).isPreconnected (sphere_subset_closedBall hmem) hz (hsphere _ hmem)

/-- If `f` is analytic on `closedBall c R` and nonvanishing on the bounding sphere `sphere c R`,
then `f` has finite meromorphic order throughout `closedBall c R`. -/
theorem AnalyticOnNhd.meromorphicOrderAt_ne_top_of_forall_mem_sphere_ne_zero
    (hf : AnalyticOnNhd 𝕜 f (closedBall c R))
    (hsphere : ∀ ζ ∈ sphere c R, f ζ ≠ 0)
    {z : 𝕜} (hz : z ∈ closedBall c R) : meromorphicOrderAt f z ≠ ⊤ :=
  hf.meromorphicOn.meromorphicOrderAt_ne_top_of_forall_mem_sphere
    (fun ζ hζ ↦ by
      rw [(hf ζ (sphere_subset_closedBall hζ)).meromorphicOrderAt_eq,
        (hf ζ (sphere_subset_closedBall hζ)).analyticOrderAt_eq_zero.2 (hsphere ζ hζ)]
      exact WithTop.zero_ne_top) hz

end
