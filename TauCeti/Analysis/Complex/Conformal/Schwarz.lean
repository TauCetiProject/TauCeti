/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Schwarz

/-!
# A strict form of the Schwarz lemma

Schwarz's lemma bounds the derivative at the centre of a ball by `R₂ / R₁` when a holomorphic
map into a strictly convex complex normed space sends `ball c R₁` into `closedBall (g c) R₂`.
This file records the **strict** form: the bound is attained only by an injective map, so a
non-injective one has `‖deriv g c‖ < R₂ / R₁`.

## The argument

Mathlib's `Complex.norm_deriv_le_div_of_mapsTo_ball` gives `‖deriv g c‖ ≤ R₂ / R₁`. In the equality
case `Complex.affine_of_mapsTo_ball_of_norm_dslope_eq_div` — the equality case of Schwarz, which
needs the codomain `E` to be strictly convex — forces `g` to be the affine map
`z ↦ g c + (z - c) • deriv g c` on the ball. The slope is a nonzero vector, having norm
`R₂ / R₁ > 0`, so that map is injective, contradicting the hypothesis.

Both radii must be positive. With `R₂ = 0` the target is the single point `g c`, so `g` is constant
and *not* injective, while the claimed bound `‖deriv g c‖ < 0` is false.

## Main statements

* `TauCeti.norm_deriv_lt_div_of_not_injOn` — the strict bound.
* `TauCeti.norm_deriv_lt_one_of_not_injOn` — its equal-radius form.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 6 §1.2.
-/

public section

namespace TauCeti

open Complex Set Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [StrictConvexSpace ℝ E]

/-- **Strict Schwarz lemma.** A holomorphic map of `ball c R₁` into `closedBall (g c) R₂` that is
**not** injective has `‖deriv g c‖ < R₂ / R₁`.

Both radii must be positive: for `R₂ = 0` the map is constant, so it is not injective and the
strict bound fails. -/
theorem norm_deriv_lt_div_of_not_injOn {g : ℂ → E} {c : ℂ} {R₁ R₂ : ℝ} (hR₁ : 0 < R₁)
    (hR₂ : 0 < R₂) (hgd : DifferentiableOn ℂ g (ball c R₁))
    (hgm : MapsTo g (ball c R₁) (closedBall (g c) R₂)) (hgi : ¬ InjOn g (ball c R₁)) :
    ‖deriv g c‖ < R₂ / R₁ := by
  refine (norm_deriv_le_div_of_mapsTo_ball hgd hgm hR₁).lt_of_ne fun heq ↦ hgi ?_
  -- In the equality case Schwarz forces `g z = g c + (z - c) • dslope g c c` on the ball; the
  -- slope has norm `R₂ / R₁ > 0`, so it is nonzero and this affine map is injective.
  have hds : ‖dslope g c c‖ = R₂ / R₁ := by rwa [dslope_same]
  have haff := affine_of_mapsTo_ball_of_norm_dslope_eq_div hgd hgm (mem_ball_self hR₁) hds
  have hd₀ : dslope g c c ≠ 0 := norm_pos_iff.mp (hds ▸ div_pos hR₂ hR₁)
  intro z hz w hw hzw
  rw [haff hz, haff hw, add_right_inj] at hzw
  exact sub_left_inj.mp (smul_left_injective ℂ hd₀ hzw)

/-- **Strict Schwarz lemma, equal radii.** A holomorphic map of `ball c R` into
`closedBall (g c) R` that is **not** injective has `‖deriv g c‖ < 1`. -/
theorem norm_deriv_lt_one_of_not_injOn {g : ℂ → E} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hgd : DifferentiableOn ℂ g (ball c R)) (hgm : MapsTo g (ball c R) (closedBall (g c) R))
    (hgi : ¬ InjOn g (ball c R)) : ‖deriv g c‖ < 1 :=
  (norm_deriv_lt_div_of_not_injOn hR hR hgd hgm hgi).trans_eq (div_self hR.ne')

end TauCeti
