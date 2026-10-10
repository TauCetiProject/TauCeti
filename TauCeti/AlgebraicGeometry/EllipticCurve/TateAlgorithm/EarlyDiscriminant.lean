/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass

/-!
# Discriminant bounds in the early additive branches of Tate's algorithm

The first additive tests of Tate's algorithm inspect `a₆`, `b₈`, and `b₆` in turn. Failure of
each test forces the discriminant to be divisible by `ϖ³`, `ϖ⁴`, and `ϖ⁵`, respectively. These
bounds supply the discriminant input to the algorithmic Ogg exponent and to the eventual
case distinction by reduction symbol. They hold in every residue characteristic; exact
valuations require separate analysis of wild reduction in characteristics two and three.

The first theorem starts with the singular-at-the-origin normal form produced by Step 2.
The later theorems use the invariant divisibilities tested in Steps 4 and 5. In the last
case `4 b₈ = b₂ b₆ - b₄²` forces the extra divisibility of `b₄` even in residue
characteristic two.

Reference: J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, IV.9.
-/

public section

namespace TauCeti

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (ϖ : R)

/-- In the additive Step 2 normal form, `ϖ` divides `b₄` and `b₆`, and `ϖ²` divides
`b₈`. The last assertion uses `ϖ ∣ b₂` as well as the singularity at the origin. -/
theorem _root_.WeierstrassCurve.tateStepTwo_invariant_divisibilities
    (hb₂ : ϖ ∣ W.b₂) (h₃ : ϖ ∣ W.a₃) (h₄ : ϖ ∣ W.a₄) (h₆ : ϖ ∣ W.a₆) :
    ϖ ∣ W.b₄ ∧ ϖ ∣ W.b₆ ∧ ϖ ^ 2 ∣ W.b₈ := by
  obtain ⟨B₂, hB₂⟩ := hb₂
  obtain ⟨A₃, hA₃⟩ := h₃
  obtain ⟨A₄, hA₄⟩ := h₄
  obtain ⟨A₆, hA₆⟩ := h₆
  refine ⟨⟨W.a₁ * A₃ + 2 * A₄, ?_⟩, ⟨ϖ * A₃ ^ 2 + 4 * A₆, ?_⟩,
    ⟨B₂ * A₆ - W.a₁ * A₃ * A₄ + W.a₂ * A₃ ^ 2 - A₄ ^ 2, ?_⟩⟩
  · rw [WeierstrassCurve.b₄, hA₃, hA₄]; ring
  · rw [WeierstrassCurve.b₆, hA₃, hA₆]; ring
  · rw [WeierstrassCurve.b₂] at hB₂
    rw [WeierstrassCurve.b₈, hA₃, hA₄, hA₆]
    linear_combination (ϖ * A₆) * hB₂

/-- The additive Step 2 normal form has discriminant divisible by `ϖ²`. -/
theorem _root_.WeierstrassCurve.pow_two_dvd_Δ_of_tateStepTwo
    (hb₂ : ϖ ∣ W.b₂) (h₃ : ϖ ∣ W.a₃) (h₄ : ϖ ∣ W.a₄) (h₆ : ϖ ∣ W.a₆) :
    ϖ ^ 2 ∣ W.Δ := by
  obtain ⟨hb₄, hb₆, hb₈⟩ := W.tateStepTwo_invariant_divisibilities ϖ hb₂ h₃ h₄ h₆
  obtain ⟨B₂, hB₂⟩ := hb₂
  obtain ⟨B₄, hB₄⟩ := hb₄
  obtain ⟨B₆, hB₆⟩ := hb₆
  obtain ⟨B₈, hB₈⟩ := hb₈
  refine ⟨-ϖ ^ 2 * B₂ ^ 2 * B₈ - 8 * ϖ * B₄ ^ 3 - 27 * B₆ ^ 2 +
    9 * ϖ * B₂ * B₄ * B₆, ?_⟩
  rw [WeierstrassCurve.Δ, hB₂, hB₄, hB₆, hB₈]
  ring

/-- If the Step 3 test fails (`ϖ² ∣ a₆`), the discriminant is divisible by `ϖ³`.
The coefficient conditions are those of the Step 2 normal form. -/
theorem _root_.WeierstrassCurve.pow_three_dvd_Δ_of_tateStepThree
    (hb₂ : ϖ ∣ W.b₂) (h₃ : ϖ ∣ W.a₃) (h₄ : ϖ ∣ W.a₄) (h₆ : ϖ ^ 2 ∣ W.a₆) :
    ϖ ^ 3 ∣ W.Δ := by
  have h₆one : ϖ ∣ W.a₆ := (dvd_pow_self ϖ (by decide : 2 ≠ 0)).trans h₆
  have hb₈ : ϖ ^ 2 ∣ W.b₈ :=
    (W.tateStepTwo_invariant_divisibilities ϖ hb₂ h₃ h₄ h₆one).2.2
  obtain ⟨B₂, hB₂⟩ := hb₂
  obtain ⟨A₃, hA₃⟩ := h₃
  obtain ⟨A₄, hA₄⟩ := h₄
  obtain ⟨A₆, hA₆⟩ := h₆
  have hB₄ : W.b₄ = ϖ * (W.a₁ * A₃ + 2 * A₄) := by
    rw [WeierstrassCurve.b₄, hA₃, hA₄]; ring
  have hB₆ : W.b₆ = ϖ ^ 2 * (A₃ ^ 2 + 4 * A₆) := by
    rw [WeierstrassCurve.b₆, hA₃, hA₆]; ring
  obtain ⟨B₈, hB₈⟩ := hb₈
  refine ⟨-ϖ * B₂ ^ 2 * B₈ - 8 * (W.a₁ * A₃ + 2 * A₄) ^ 3 -
    27 * ϖ * (A₃ ^ 2 + 4 * A₆) ^ 2 +
    9 * ϖ * B₂ * (W.a₁ * A₃ + 2 * A₄) * (A₃ ^ 2 + 4 * A₆), ?_⟩
  rw [WeierstrassCurve.Δ, hB₂, hB₄, hB₆, hB₈]
  ring

/-- At Step 4, the failed `b₈` test forces `ϖ² ∣ b₄` from
`4 b₈ = b₂ b₆ - b₄²`. No restriction on the residue characteristic is needed. -/
theorem _root_.WeierstrassCurve.pow_two_dvd_b₄_of_tateStepFour
    [IsDomain R]
    (hϖ : Prime ϖ) (hb₂ : ϖ ∣ W.b₂) (hb₆ : ϖ ^ 2 ∣ W.b₆)
    (hb₈ : ϖ ^ 3 ∣ W.b₈) : ϖ ^ 2 ∣ W.b₄ := by
  have heq : W.b₄ ^ 2 = W.b₂ * W.b₆ - 4 * W.b₈ := by
    linear_combination W.b_relation
  have hsq : ϖ ^ 3 ∣ W.b₄ ^ 2 := by
    rw [heq]
    obtain ⟨B₂, hB₂⟩ := hb₂
    obtain ⟨B₆, hB₆⟩ := hb₆
    obtain ⟨B₈, hB₈⟩ := hb₈
    refine ⟨B₂ * B₆ - 4 * B₈, ?_⟩
    rw [hB₂, hB₆, hB₈]
    ring
  have hp : ϖ ∣ W.b₄ := hϖ.dvd_of_dvd_pow
    ((dvd_pow_self ϖ (by decide : 3 ≠ 0)).trans hsq)
  obtain ⟨B₄, hB₄⟩ := hp
  have hB₄sq : ϖ ∣ B₄ ^ 2 := by
    rw [hB₄, mul_pow] at hsq
    rw [show ϖ ^ 3 = ϖ ^ 2 * ϖ by ring] at hsq
    exact (mul_dvd_mul_iff_left (pow_ne_zero 2 hϖ.ne_zero)).1 hsq
  obtain ⟨C₄, hC₄⟩ := hϖ.dvd_of_dvd_pow hB₄sq
  exact ⟨C₄, by rw [hB₄, hC₄]; ring⟩

/-- If the Step 4 test fails (`ϖ³ ∣ b₈`), then `ϖ⁴` divides the discriminant.
The `ϖ² ∣ b₆` hypothesis already follows from the failed Step 3 test. -/
theorem _root_.WeierstrassCurve.pow_four_dvd_Δ_of_tateStepFour
    [IsDomain R]
    (hϖ : Prime ϖ) (hb₂ : ϖ ∣ W.b₂) (hb₆ : ϖ ^ 2 ∣ W.b₆)
    (hb₈ : ϖ ^ 3 ∣ W.b₈) : ϖ ^ 4 ∣ W.Δ := by
  have hb₄ := W.pow_two_dvd_b₄_of_tateStepFour ϖ hϖ hb₂ hb₆ hb₈
  obtain ⟨B₂, hB₂⟩ := hb₂
  obtain ⟨B₄, hB₄⟩ := hb₄
  obtain ⟨B₆, hB₆⟩ := hb₆
  obtain ⟨B₈, hB₈⟩ := hb₈
  refine ⟨-ϖ * B₂ ^ 2 * B₈ - 8 * ϖ ^ 2 * B₄ ^ 3 - 27 * B₆ ^ 2 +
    9 * ϖ * B₂ * B₄ * B₆, ?_⟩
  rw [WeierstrassCurve.Δ, hB₂, hB₄, hB₆, hB₈]
  ring

/-- If the Step 5 test also fails (`ϖ³ ∣ b₆`), then `ϖ⁵` divides the discriminant.
This is the discriminant bound at the entry to Step 6, before its normalising change of
variables. -/
theorem _root_.WeierstrassCurve.pow_five_dvd_Δ_of_tateStepFive
    [IsDomain R] (hϖ : Prime ϖ) (hb₂ : ϖ ∣ W.b₂) (hb₆ : ϖ ^ 3 ∣ W.b₆)
    (hb₈ : ϖ ^ 3 ∣ W.b₈) : ϖ ^ 5 ∣ W.Δ := by
  have hb₆two : ϖ ^ 2 ∣ W.b₆ :=
    (pow_dvd_pow ϖ (by decide : 2 ≤ 3)).trans hb₆
  have hb₄ := W.pow_two_dvd_b₄_of_tateStepFour ϖ hϖ hb₂ hb₆two hb₈
  obtain ⟨B₂, hB₂⟩ := hb₂
  obtain ⟨B₄, hB₄⟩ := hb₄
  obtain ⟨B₆, hB₆⟩ := hb₆
  obtain ⟨B₈, hB₈⟩ := hb₈
  refine ⟨-B₂ ^ 2 * B₈ - 8 * ϖ * B₄ ^ 3 - 27 * ϖ * B₆ ^ 2 +
    9 * ϖ * B₂ * B₄ * B₆, ?_⟩
  rw [WeierstrassCurve.Δ, hB₂, hB₄, hB₆, hB₈]
  ring

end TauCeti

end
