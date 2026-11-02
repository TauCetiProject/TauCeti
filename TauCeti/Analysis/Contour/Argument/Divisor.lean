/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Meromorphic.Divisor
public import TauCeti.Analysis.Contour.Argument.Principle

/-!
# The argument principle against the divisor

`TauCeti.Contour.argumentPrinciple` asks its caller for the data of the counting problem: a finite
set `S` collecting the nonzero-order points, an order function `ord`, and proofs that the two agree
and that `S` is exhaustive. Mathlib's `MeromorphicOn.divisor` already packages exactly that data —
`MeromorphicOn.divisor_apply` evaluates it to `(meromorphicOrderAt f z).untop₀`, and
`MeromorphicOn.divisor_ball_support_finite` supplies the finiteness from the same
`MeromorphicOn f (closedBall c R)` hypothesis the argument principle already assumes. This file
restates the argument principle against that API, so callers that already speak `divisor` need not
rebuild the finset and the order function by hand.

The only hypothesis this adds is `hsphere`: the bounding circle carries no zeros or poles. It does
double duty.

* It confines the nonzero-order points to the *open* disc, so a divisor taken over `ball c R` still
  accounts for every such point of `closedBall c R`.
* It rules out order `⊤`. This matters because `(⊤ : WithTop ℤ).untop₀ = 0`, so at a point where `f`
  vanishes identically the divisor reads `0` while the order does not, and the exhaustiveness
  obligation of `argumentPrinciple` would fail exactly there. No separate hypothesis is needed:
  `closedBall c R` is convex, hence preconnected, and the sphere is nonempty as `0 < R`, so
  `MeromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected` propagates the finite order at a
  boundary point to the whole disc.

## Main results

* `TauCeti.Contour.argumentPrinciple_divisor` —
  `∮_{C(c,R)} logDeriv f = 2πi · ∑ᶠ z, divisor f (ball c R) z`, the argument principle with the
  counting data taken from `MeromorphicOn.divisor`. The conclusion uses the canonical finitely
  supported sum `∑ᶠ`, which is well defined because the divisor vanishes off `ball c R`; the
  finiteness witness `MeromorphicOn.divisor_ball_support_finite` stays inside the proof rather than
  appearing in the statement.

## References

* N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized Residue
  Theorem*, arXiv:1808.00997.
-/

public section

open Metric

namespace TauCeti.Contour

/-- **The argument principle, against the divisor.** For `f` meromorphic on the closed disc
`C(c, R)` with no zero or pole on the bounding circle, the contour integral of the logarithmic
derivative is `2πi` times the sum of `MeromorphicOn.divisor` over the open disc.

This is `TauCeti.Contour.argumentPrinciple` with the finite set and the order function supplied by
Mathlib's divisor API rather than by the caller. -/
theorem argumentPrinciple_divisor {f : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : MeromorphicOn f (closedBall c R))
    (hsphere : ∀ z ∈ sphere c R, meromorphicOrderAt f z = 0) :
    circleIntegral (logDeriv f) c R
      = 2 * (Real.pi : ℂ) * Complex.I *
        (∑ᶠ z, ((MeromorphicOn.divisor f (ball c R) z : ℤ) : ℂ)) := by
  have hfb : MeromorphicOn f (ball c R) := hf.mono_set ball_subset_closedBall
  set S := (MeromorphicOn.divisor_ball_support_finite hf).toFinset
  rw [finsum_eq_finsetSum_of_support_subset _ (s := S) fun z hz => by simpa [S] using hz]
  have hxs : c + (R : ℂ) ∈ sphere c R := by simp [abs_of_pos hR]
  have htop : ∀ z ∈ closedBall c R, meromorphicOrderAt f z ≠ ⊤ := fun z hz =>
    hf.meromorphicOrderAt_ne_top_of_isPreconnected (convex_closedBall c R).isPreconnected
      (sphere_subset_closedBall hxs) hz (by simp [hsphere _ hxs])
  refine argumentPrinciple hR S _ hf (fun z hz => ?_) (fun z hz hord => ?_) fun z hz => ?_
  · exact (MeromorphicOn.divisor f (ball c R)).supportWithinDomain (by simpa [S] using hz)
  · have hzball : z ∈ ball c R := by
      rw [← closedBall_sdiff_sphere]; exact ⟨hz, fun h => hord (hsphere z h)⟩
    simpa [S, hfb, hzball, WithTop.untop₀_eq_zero, htop z hz] using hord
  · have hzball := (MeromorphicOn.divisor f (ball c R)).supportWithinDomain (by simpa [S] using hz)
    rw [MeromorphicOn.divisor_apply hfb hzball,
      WithTop.coe_untop₀_of_ne_top (htop z (ball_subset_closedBall hzball))]

end TauCeti.Contour
