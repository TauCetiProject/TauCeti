/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Order.Interval.Set.OrdConnected
public import Mathlib.Topology.OpenPartialHomeomorph.Defs

/-!
# Twist maps of an open strip

Fix a period `ℓ > 0` and a nonempty open interval `J` of heights, with endpoints
`-∞ ≤ a < b ≤ ∞`. A *twist lift on the open strip* `ℝ × J` is a homeomorphism `F = (F₁, F₂)` of
the strip that commutes with the deck translation `(x, y) ↦ (x + ℓ, y)`, twists positively
(`y ↦ F₁(x, y)` is strictly increasing for every `x`), and preserves the two ends of the strip
uniformly in `x`: `F₂(x, y) → a` as `y → a` and `F₂(x, y) → b` as `y → b`. These replace the
boundary lines of a twist lift of a closed strip. A *monotone twist map* is moreover a `C¹`
diffeomorphism of the strip with `∂F₁/∂y > 0` everywhere (Katok–Hasselblatt, *Introduction to the
Modern Theory of Dynamical Systems*, Section 9.3; Herman, *Sur les courbes invariantes par les
difféomorphismes de l'anneau*, Chapitre I, 1.2, for the derivative form: a diffeomorphism turning
the vertical).

## Main definitions

* `TauCeti.IsOpenStripTwistLift ℓ J F`: `F` is a positive twist lift with period `ℓ` on the open
  strip `ℝ × J`.
* `TauCeti.IsMonotoneTwistMap ℓ J F`: `F` is a monotone twist map of the open strip `ℝ × J`.

## Implementation notes

As for `TauCeti.IsPoincareBirkhoffLift`, a homeomorphism of the strip is an
`OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ)` whose source and target are the strip `univ ×ˢ J`, so that
its derivative is Mathlib's `fderiv` on the plane. Since the endpoints of `J` may be infinite, the
convergence at the ends is stated through the heights in `J` themselves: `F₂(x, y) → a` as
`y → a`, uniformly in `x`, says that for every height `c ∈ J` there is a height `d ∈ J` with
`F₂(x, y) < c` whenever `y < d`, for all `x`; for `J` an open interval this is convergence to the
lower end, finite or not. The upper end is symmetric.

## References

* A. Katok and B. Hasselblatt, *Introduction to the Modern Theory of Dynamical Systems*,
  Cambridge University Press, 1995, Section 9.3.
* M. R. Herman, *Sur les courbes invariantes par les difféomorphismes de l'anneau, Vol. 1*,
  Astérisque 103–104, 1983, Chapitre I, 1.2.
-/

public section

open Set

namespace TauCeti

/-- A *positive twist lift* with period `ℓ > 0` on the open strip `ℝ × J`, for `J` a nonempty open
interval: a homeomorphism `F` of the strip (an open partial homeomorphism of the plane with source
and target `univ ×ˢ J`) commuting with the deck translation `(x, y) ↦ (x + ℓ, y)`, with
`y ↦ F₁(x, y)` strictly increasing for every `x`, which preserves both ends of the strip uniformly
in `x`: `F₂(x, y)` tends to the lower end of `J` as `y` does, and to the upper end as `y` does
(Katok–Hasselblatt, Section 9.3). -/
structure IsOpenStripTwistLift (ℓ : ℝ) (J : Set ℝ) (F : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ)) :
    Prop where
  /-- The period is positive. -/
  period_pos : 0 < ℓ
  /-- The interval of heights is nonempty. -/
  nonempty : J.Nonempty
  /-- The interval of heights is open. -/
  isOpen : IsOpen J
  /-- The set of heights is an interval. -/
  ordConnected : J.OrdConnected
  /-- `F` is defined on the whole strip `ℝ × J`. -/
  source_eq : F.source = univ ×ˢ J
  /-- `F` maps the strip `ℝ × J` onto itself. -/
  target_eq : F.target = univ ×ˢ J
  /-- `F` commutes with the deck translation `(x, y) ↦ (x + ℓ, y)`. -/
  apply_add_period : ∀ x, ∀ y ∈ J, F (x + ℓ, y) = F (x, y) + (ℓ, 0)
  /-- Positive twist: the first coordinate of `F` is strictly increasing on every vertical. -/
  strictMonoOn_fst : ∀ x, StrictMonoOn (fun y => (F (x, y)).1) J
  /-- `F` preserves the lower end of the strip, uniformly in `x`. -/
  lower_end : ∀ c ∈ J, ∃ d ∈ J, ∀ x, ∀ y ∈ J, y < d → (F (x, y)).2 < c
  /-- `F` preserves the upper end of the strip, uniformly in `x`. -/
  upper_end : ∀ c ∈ J, ∃ d ∈ J, ∀ x, ∀ y ∈ J, d < y → c < (F (x, y)).2

/-- A *monotone twist map* with period `ℓ` of the open strip `ℝ × J`: a positive twist lift on the
open strip which is a `C¹` diffeomorphism of the strip with `∂F₁/∂y > 0` everywhere, so that it
turns every vertical to the right (Katok–Hasselblatt, Section 9.3; Herman, Chapitre I, 1.2). -/
structure IsMonotoneTwistMap (ℓ : ℝ) (J : Set ℝ) (F : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ)) :
    Prop extends IsOpenStripTwistLift ℓ J F where
  /-- `F` is `C¹` on the strip. -/
  contDiffOn : ContDiffOn ℝ 1 F (univ ×ˢ J)
  /-- The inverse of `F` is `C¹` on the strip. -/
  contDiffOn_symm : ContDiffOn ℝ 1 F.symm (univ ×ˢ J)
  /-- The derivative `∂F₁/∂y` is positive on the strip. -/
  fderiv_fst_pos : ∀ p ∈ univ ×ˢ J, 0 < (fderiv ℝ F p (0, 1)).1

end TauCeti
