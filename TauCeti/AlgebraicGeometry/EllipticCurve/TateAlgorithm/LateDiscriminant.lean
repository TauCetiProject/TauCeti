/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.TateAlgorithm.InvariantDivisibility
import Mathlib.Tactic.Ring

/-!
# Discriminant bounds in the last branches of Tate's algorithm

In the triple-root branch of Tate's algorithm, the successive normal forms at Steps 8, 9,
and 10 force the discriminant to be divisible by the eighth, ninth, and tenth powers of the
uniformiser, respectively. These are the lower bounds on the discriminant valuation used when
the reduction symbols `IV*`, `III*`, and `II*` are assigned an algorithmic Ogg exponent.

The bounds are polynomial identities and hold over an arbitrary commutative ring. In particular,
they do not need a discrete valuation ring, a perfect residue field, or minimality. The
normal-form constructions under those hypotheses are in `TateAlgorithm.TripleRoot`.

## Reference

J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, IV.9,
Steps 8–10 of Tate's algorithm.
-/

public section

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (ϖ : R)

/-- In the Step 8 normal form of Tate's algorithm, the discriminant is divisible by `ϖ⁸`.
The hypotheses on the coefficients are exactly those produced by the triple-root translation. -/
theorem pow_eight_dvd_Δ_of_stepEight (h₁ : ϖ ∣ W.a₁) (h₂ : ϖ ^ 2 ∣ W.a₂)
    (h₃ : ϖ ^ 2 ∣ W.a₃) (h₄ : ϖ ^ 3 ∣ W.a₄) (h₆ : ϖ ^ 4 ∣ W.a₆) :
    ϖ ^ 8 ∣ W.Δ := by
  obtain ⟨u, hu⟩ := W.pow_two_dvd_b₂ ϖ h₁ h₂
  obtain ⟨v, hv⟩ := W.pow_three_dvd_b₄ ϖ h₁ h₃ h₄
  obtain ⟨w, hw⟩ := W.pow_four_dvd_b₆ ϖ h₃ h₆
  obtain ⟨z, hz⟩ := W.pow_six_dvd_b₈ ϖ h₁ h₂ h₃ h₄ h₆
  refine ⟨-(ϖ ^ 2 * u ^ 2 * z) - 8 * ϖ * v ^ 3 - 27 * w ^ 2 +
    9 * ϖ * u * v * w, ?_⟩
  rw [Δ, hu, hv, hw, hz]
  ring

/-- In the Step 9 normal form of Tate's algorithm, the discriminant is divisible by `ϖ⁹`.
The stronger divisibility of `a₃` and `a₆` raises that of `b₆` from `ϖ⁴` to `ϖ⁵`. -/
theorem pow_nine_dvd_Δ_of_stepNine (h₁ : ϖ ∣ W.a₁) (h₂ : ϖ ^ 2 ∣ W.a₂)
    (h₃ : ϖ ^ 3 ∣ W.a₃) (h₄ : ϖ ^ 3 ∣ W.a₄) (h₆ : ϖ ^ 5 ∣ W.a₆) :
    ϖ ^ 9 ∣ W.Δ := by
  obtain ⟨u, hu⟩ := W.pow_two_dvd_b₂ ϖ h₁ h₂
  have h₃' : ϖ ^ 2 ∣ W.a₃ := (pow_dvd_pow ϖ (by norm_num)).trans h₃
  have h₆' : ϖ ^ 4 ∣ W.a₆ := (pow_dvd_pow ϖ (by norm_num)).trans h₆
  obtain ⟨v, hv⟩ := W.pow_three_dvd_b₄ ϖ h₁ h₃' h₄
  obtain ⟨z, hz⟩ := W.pow_six_dvd_b₈ ϖ h₁ h₂ h₃' h₄ h₆'
  obtain ⟨s, hs⟩ := h₃
  obtain ⟨t, ht⟩ := h₆
  have hb₆ : ϖ ^ 5 ∣ W.b₆ := by
    refine ⟨ϖ * s ^ 2 + 4 * t, ?_⟩
    rw [b₆, hs, ht]
    ring
  obtain ⟨w, hw⟩ := hb₆
  refine ⟨-(ϖ * u ^ 2 * z) - 8 * v ^ 3 - 27 * ϖ * w ^ 2 +
    9 * ϖ * u * v * w, ?_⟩
  rw [Δ, hu, hv, hw, hz]
  ring

/-- In the Step 10 normal form of Tate's algorithm, the discriminant is divisible by `ϖ¹⁰`.
The extra divisibility of `a₄` raises the bounds on both `b₄` and `b₈`. -/
theorem pow_ten_dvd_Δ_of_stepTen (h₁ : ϖ ∣ W.a₁) (h₂ : ϖ ^ 2 ∣ W.a₂)
    (h₃ : ϖ ^ 3 ∣ W.a₃) (h₄ : ϖ ^ 4 ∣ W.a₄) (h₆ : ϖ ^ 5 ∣ W.a₆) :
    ϖ ^ 10 ∣ W.Δ := by
  obtain ⟨u, hu⟩ := W.pow_two_dvd_b₂ ϖ h₁ h₂
  obtain ⟨s, hs⟩ := h₁
  obtain ⟨t, ht⟩ := h₂
  obtain ⟨r, hr⟩ := h₃
  obtain ⟨q, hq⟩ := h₄
  obtain ⟨p, hp⟩ := h₆
  have hb₄ : ϖ ^ 4 ∣ W.b₄ := by
    refine ⟨2 * q + s * r, ?_⟩
    rw [b₄, hs, hr, hq]
    ring
  have hb₆ : ϖ ^ 5 ∣ W.b₆ := by
    refine ⟨ϖ * r ^ 2 + 4 * p, ?_⟩
    rw [b₆, hr, hp]
    ring
  have hb₈ : ϖ ^ 7 ∣ W.b₈ := by
    refine ⟨s ^ 2 * p + 4 * t * p - ϖ * s * r * q + ϖ * t * r ^ 2 - ϖ * q ^ 2,
      ?_⟩
    rw [b₈, hs, ht, hr, hq, hp]
    ring
  obtain ⟨v, hv⟩ := hb₄
  obtain ⟨w, hw⟩ := hb₆
  obtain ⟨z, hz⟩ := hb₈
  refine ⟨-(ϖ * u ^ 2 * z) - 8 * ϖ ^ 2 * v ^ 3 - 27 * w ^ 2 +
    9 * ϖ * u * v * w, ?_⟩
  rw [Δ, hu, hv, hw, hz]
  ring

end WeierstrassCurve

end
