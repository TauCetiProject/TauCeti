/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.Tactic.Ring

/-!
# Divisibility of Weierstrass invariants in Tate normal forms

The coefficient bounds in the late branches of Tate's algorithm imply these bounds on the
Weierstrass invariants. They are polynomial identities over any commutative ring. The bounds on
`b₄`, `b₆`, and `b₈` carry an exponent shift `n`, so that one statement covers both the Step 8
normal form and the stronger Step 10 normal form. The Step 8–10 discriminant bounds in
`TateAlgorithm.LateDiscriminant` use them.

## Reference

J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, IV.9,
Steps 8–10 of Tate's algorithm.
-/

public section

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (ϖ : R)

/-- If `ϖ ∣ a₁` and `ϖ² ∣ a₂`, then `ϖ² ∣ b₂`. -/
theorem pow_two_dvd_b₂ (h₁ : ϖ ∣ W.a₁) (h₂ : ϖ ^ 2 ∣ W.a₂) :
    ϖ ^ 2 ∣ W.b₂ := by
  obtain ⟨u, hu⟩ := h₁
  obtain ⟨v, hv⟩ := h₂
  refine ⟨u ^ 2 + 4 * v, ?_⟩
  rw [b₂, hu, hv]
  ring

/-- If `ϖ ∣ a₁`, `ϖⁿ ∣ a₃`, and `ϖⁿ⁺¹ ∣ a₄`, then `ϖⁿ⁺¹ ∣ b₄`. -/
theorem pow_add_one_dvd_b₄ {n : ℕ} (h₁ : ϖ ∣ W.a₁) (h₃ : ϖ ^ n ∣ W.a₃)
    (h₄ : ϖ ^ (n + 1) ∣ W.a₄) : ϖ ^ (n + 1) ∣ W.b₄ := by
  obtain ⟨u, hu⟩ := h₁
  obtain ⟨v, hv⟩ := h₃
  obtain ⟨w, hw⟩ := h₄
  refine ⟨2 * w + u * v, ?_⟩
  rw [b₄, hu, hv, hw]
  ring

/-- If `ϖⁿ⁺² ∣ a₃` and `ϖⁿ⁺⁴ ∣ a₆`, then `ϖⁿ⁺⁴ ∣ b₆`. -/
theorem pow_add_four_dvd_b₆ {n : ℕ} (h₃ : ϖ ^ (n + 2) ∣ W.a₃) (h₆ : ϖ ^ (n + 4) ∣ W.a₆) :
    ϖ ^ (n + 4) ∣ W.b₆ := by
  obtain ⟨u, hu⟩ := h₃
  obtain ⟨v, hv⟩ := h₆
  refine ⟨ϖ ^ n * u ^ 2 + 4 * v, ?_⟩
  rw [b₆, hu, hv]
  ring

/-- If `ϖ ∣ a₁`, `ϖ² ∣ a₂`, `ϖⁿ⁺² ∣ a₃`, `ϖⁿ⁺³ ∣ a₄`, and `ϖⁿ⁺⁴ ∣ a₆`, then `ϖⁿ⁺⁶ ∣ b₈`.
The case `n = 0` is the Step 8 normal form, and `n = 1` is the Step 10 normal form. -/
theorem pow_add_six_dvd_b₈ {n : ℕ} (h₁ : ϖ ∣ W.a₁) (h₂ : ϖ ^ 2 ∣ W.a₂)
    (h₃ : ϖ ^ (n + 2) ∣ W.a₃) (h₄ : ϖ ^ (n + 3) ∣ W.a₄) (h₆ : ϖ ^ (n + 4) ∣ W.a₆) :
    ϖ ^ (n + 6) ∣ W.b₈ := by
  obtain ⟨u, hu⟩ := h₁
  obtain ⟨v, hv⟩ := h₂
  obtain ⟨w, hw⟩ := h₃
  obtain ⟨x, hx⟩ := h₄
  obtain ⟨y, hy⟩ := h₆
  refine ⟨u ^ 2 * y + 4 * v * y + ϖ ^ n * (v * w ^ 2 - u * w * x - x ^ 2), ?_⟩
  rw [b₈, hu, hv, hw, hx, hy]
  ring

end WeierstrassCurve

end
