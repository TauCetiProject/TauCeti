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
# Meromorphic order from limits and boundary conditions

A nonzero limit of `(z - c) • f z` at `c` detects an exact simple pole of `f`.

On a nonempty closed disc `closedBall c R` over `ℝ` or `ℂ` (`RCLike 𝕜`), the boundary point
`c + R` lies on `sphere c R` and `closedBall c R` is convex, hence preconnected. Consequently,
if a meromorphic function on `closedBall c R` has finite meromorphic order at every point of
`sphere c R` — in particular, if an analytic function on `closedBall c R` does not vanish on
`sphere c R` — then `MeromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected` propagates finite
meromorphic order to every point of `closedBall c R`.

## Main results

* `MeromorphicAt.meromorphicOrderAt_eq_neg_one_of_tendsto_sub_smul`: a nonzero residue limit
  forces meromorphic order exactly `-1`.
* `MeromorphicOn.meromorphicOrderAt_ne_top_of_forall_mem_sphere`: finite meromorphic order on the
  bounding sphere propagates throughout the closed disc.
* `AnalyticOnNhd.meromorphicOrderAt_ne_top_of_forall_mem_sphere_ne_zero`: an analytic function on
  a closed disc that does not vanish on the bounding sphere has finite meromorphic order throughout
  the closed disc.
-/

public section

open Filter Metric Topology

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {f : 𝕜 → E} {c : 𝕜} {R : ℝ}

/-- A meromorphic function has an exact simple pole if multiplying by the displacement from
that point gives a nonzero punctured limit. -/
theorem MeromorphicAt.meromorphicOrderAt_eq_neg_one_of_tendsto_sub_smul
    (hf : MeromorphicAt f c) {a : E} (ha : a ≠ 0)
    (hlim : Tendsto (fun z ↦ (z - c) • f z) (𝓝[≠] c) (𝓝 a)) :
    meromorphicOrderAt f c = (-1 : ℤ) := by
  have hm : MeromorphicAt (fun z : 𝕜 ↦ z - c) c := by fun_prop
  have h := (tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero (hm.smul hf)).mp
    ⟨a, ha, hlim⟩
  rw [meromorphicOrderAt_smul hm hf, meromorphicOrderAt_id_sub_const] at h
  exact (WithTop.add_left_inj (by simp : (1 : WithTop ℤ) ≠ ⊤)).mp
    (h.trans (by norm_num : (0 : WithTop ℤ) = 1 + (-1 : ℤ)))

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
