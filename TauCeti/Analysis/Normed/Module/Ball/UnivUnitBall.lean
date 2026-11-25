/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
public import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Module
import TauCeti.Analysis.Real.Sqrt

/-!
# A Lipschitz estimate for the radial map onto the unit ball

Mathlib's `OpenPartialHomeomorph.univUnitBall` sends a vector `x` of a real seminormed space to
`(√(1 + ‖x‖²))⁻¹ • x`, a point of the open unit ball. This file proves that it is Lipschitz with a
constant that improves far from the origin:

`‖univUnitBall x - univUnitBall y‖ ≤ 2 ‖x - y‖ / √(1 + ‖x‖²)`

(`OpenPartialHomeomorph.norm_univUnitBall_sub_le`). The gain `1 / √(1 + ‖x‖²)` is what makes the
map useful for comparing functions with polynomial growth: if `‖f - g‖ ≤ δ (1 + ‖g‖)` everywhere,
then `univUnitBall ∘ f` and `univUnitBall ∘ g` are uniformly within `4 δ`
(`OpenPartialHomeomorph.norm_univUnitBall_sub_le_of_norm_sub_le`). Both follow from an estimate
on `‖A⁻¹ a' - B⁻¹ b'‖`, with `A = √(1 + ‖a‖²)` and `B = √(1 + ‖b‖²)`
(`TauCeti.norm_inv_sqrt_smul_sub_inv_sqrt_smul_le`), which also compares rescalings of vectors
`a'`, `b'` other than `a`, `b` (`TauCeti.norm_inv_sqrt_smul_sub_inv_sqrt_smul_le_of_norm_sub_le`).
The estimate rests on the fact that `t ↦ √(1 + t²)` is `1`-Lipschitz on the real line
(`Real.abs_sqrt_one_add_sq_sub_sqrt_one_add_sq_le_abs_sub`).

In a real inner product space, `⟪univUnitBall a, (√(1 + ‖a‖²))⁻¹ • x⟫ = (1 + ‖a‖²)⁻¹ ⟪a, x⟫`
(`OpenPartialHomeomorph.inner_univUnitBall_inv_sqrt_smul`), which writes
`(1 + ‖a‖²)⁻¹ ⟪a, x⟫` through `univUnitBall a` and a rescaling to which the estimates above apply.
Under the hypotheses of the uniform closeness of rescalings, `(1 + ‖a‖²)⁻¹ ⟪a, a'⟫` and
`(1 + ‖b‖²)⁻¹ ⟪b, b'⟫` are within `(24 C + 12) δ`
(`TauCeti.abs_inv_one_add_norm_sq_mul_inner_sub_le`).

For `f` a complex polynomial, `univUnitBall ∘ f` is the section `exp(u₀) f` of the background
amplitude `u₀ = -log (1 + ‖f‖²) / 2` used to construct plane vortices with prescribed zeros.
-/

public section

open Metric InnerProductSpace

namespace TauCeti

/-- If `‖a - b‖ ≤ δ (1 + ‖b‖)` with `δ ≤ 1 / 2`, then `(1 + ‖b‖) / 4 ≤ √(1 + ‖a‖²)`. -/
theorem one_add_norm_div_four_le_sqrt_one_add_norm_sq {E : Type*} [SeminormedAddGroup E]
    {a b : E} {δ : ℝ} (hδ : δ ≤ 1 / 2) (h : ‖a - b‖ ≤ δ * (1 + ‖b‖)) :
    (1 + ‖b‖) / 4 ≤ √(1 + ‖a‖ ^ 2) := by
  have h₁ := Real.one_add_div_two_le_sqrt_one_add_sq ‖a‖
  have h₂ := norm_le_norm_add_norm_sub a b
  nlinarith [norm_nonneg b]

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Comparing two radial rescalings.** With `A = √(1 + ‖a‖²)` and `B = √(1 + ‖b‖²)`,
`‖A⁻¹ a' - B⁻¹ b'‖ ≤ ‖a' - b'‖ / A + ‖a - b‖ ‖b'‖ / (A B)`. For `a' = a` and `b' = b` this compares
`univUnitBall a` with `univUnitBall b`. -/
theorem norm_inv_sqrt_smul_sub_inv_sqrt_smul_le (a b a' b' : E) :
    ‖(√(1 + ‖a‖ ^ 2))⁻¹ • a' - (√(1 + ‖b‖ ^ 2))⁻¹ • b'‖ ≤
      ‖a' - b'‖ / √(1 + ‖a‖ ^ 2) + ‖a - b‖ * ‖b'‖ / (√(1 + ‖a‖ ^ 2) * √(1 + ‖b‖ ^ 2)) := by
  set A := √(1 + ‖a‖ ^ 2)
  set B := √(1 + ‖b‖ ^ 2)
  have hA : 0 < A := Real.sqrt_pos.2 (by positivity)
  have hB : 0 < B := Real.sqrt_pos.2 (by positivity)
  -- `|B - A| ≤ |‖b‖ - ‖a‖| ≤ ‖a - b‖`.
  have hBA : |B - A| ≤ ‖a - b‖ :=
    (Real.abs_sqrt_one_add_sq_sub_sqrt_one_add_sq_le_abs_sub _ _).trans
      (by rw [abs_sub_comm]; exact abs_norm_sub_norm_le a b)
  have hsplit : A⁻¹ • a' - B⁻¹ • b' = A⁻¹ • (a' - b') + (A⁻¹ - B⁻¹) • b' := by module
  rw [hsplit]
  refine (norm_add_le _ _).trans (add_le_add (le_of_eq ?_) ?_)
  · rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hA, inv_mul_eq_div]
  · rw [norm_smul, Real.norm_eq_abs, inv_sub_inv hA.ne' hB.ne', abs_div,
      abs_of_pos (mul_pos hA hB), div_mul_eq_mul_div]
    gcongr

/-- **Uniform closeness of radial rescalings.** With `A = √(1 + ‖a‖²)` and `B = √(1 + ‖b‖²)`: if
`‖a - b‖ ≤ δ (1 + ‖b‖)`, `‖a' - b'‖ ≤ δ (1 + ‖b‖)` and `‖b'‖ ≤ C (1 + ‖b‖)`, with
`δ ≤ 1 / 2`, then `‖A⁻¹ a' - B⁻¹ b'‖ ≤ (4 + 8 C) δ`. This is the companion of
`OpenPartialHomeomorph.norm_univUnitBall_sub_le_of_norm_sub_le` for vectors `a'`, `b'`, such as
derivatives, of at most the size of `b`. -/
theorem norm_inv_sqrt_smul_sub_inv_sqrt_smul_le_of_norm_sub_le {a b a' b' : E} {δ C : ℝ}
    (hδ : δ ≤ 1 / 2) (ha : ‖a - b‖ ≤ δ * (1 + ‖b‖)) (ha' : ‖a' - b'‖ ≤ δ * (1 + ‖b‖))
    (hb' : ‖b'‖ ≤ C * (1 + ‖b‖)) :
    ‖(√(1 + ‖a‖ ^ 2))⁻¹ • a' - (√(1 + ‖b‖ ^ 2))⁻¹ • b'‖ ≤ (4 + 8 * C) * δ := by
  have hδ0 : 0 ≤ δ := nonneg_of_mul_nonneg_left ((norm_nonneg _).trans ha) (by positivity)
  have hC : 0 ≤ C := nonneg_of_mul_nonneg_left ((norm_nonneg _).trans hb') (by positivity)
  refine (norm_inv_sqrt_smul_sub_inv_sqrt_smul_le a b a' b').trans ?_
  set A := √(1 + ‖a‖ ^ 2)
  set B := √(1 + ‖b‖ ^ 2)
  have hA : (1 + ‖b‖) / 4 ≤ A := one_add_norm_div_four_le_sqrt_one_add_norm_sq hδ ha
  have hB : (1 + ‖b‖) / 2 ≤ B := Real.one_add_div_two_le_sqrt_one_add_sq _
  have hA0 : 0 < A := lt_of_lt_of_le (by positivity) hA
  have hB0 : 0 < B := lt_of_lt_of_le (by positivity) hB
  have h₁ : ‖a' - b'‖ / A ≤ 4 * δ := by
    rw [div_le_iff₀ hA0]
    nlinarith
  have h₂ : ‖a - b‖ * ‖b'‖ / (A * B) ≤ 8 * C * δ := by
    rw [div_le_iff₀ (mul_pos hA0 hB0)]
    have hAB : (1 + ‖b‖) ^ 2 / 8 ≤ A * B := by
      nlinarith [mul_le_mul hA hB (by positivity) hA0.le]
    have := mul_le_mul ha hb' (norm_nonneg _) (by positivity)
    nlinarith [mul_nonneg hδ0 hC]
  linarith

end TauCeti

namespace OpenPartialHomeomorph

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

/-- `univUnitBall` takes values in the closed unit ball. -/
theorem norm_univUnitBall_le (x : E) : ‖univUnitBall x‖ ≤ 1 :=
  (mem_ball_zero_iff.1 (univUnitBall.map_source (Set.mem_univ x))).le

/-- **A Lipschitz estimate for `univUnitBall`.** The radial map
`x ↦ (√(1 + ‖x‖²))⁻¹ • x` onto the open unit ball satisfies
`‖univUnitBall x - univUnitBall y‖ ≤ 2 ‖x - y‖ / √(1 + ‖x‖²)`. -/
theorem norm_univUnitBall_sub_le (x y : E) :
    ‖univUnitBall x - univUnitBall y‖ ≤ 2 * ‖x - y‖ / √(1 + ‖x‖ ^ 2) := by
  have hB : 0 < √(1 + ‖y‖ ^ 2) := Real.sqrt_pos.2 (by positivity)
  have hyB : ‖y‖ ≤ √(1 + ‖y‖ ^ 2) := Real.le_sqrt_of_sq_le (by linarith)
  -- The second term of the general estimate is at most the first, since `‖y‖ ≤ √(1 + ‖y‖²)`.
  have hcoef : ‖x - y‖ * ‖y‖ / (√(1 + ‖x‖ ^ 2) * √(1 + ‖y‖ ^ 2)) ≤ ‖x - y‖ / √(1 + ‖x‖ ^ 2) := by
    rw [mul_div_mul_comm]
    exact mul_le_of_le_one_right (by positivity) ((div_le_one hB).2 hyB)
  simp only [univUnitBall_apply]
  calc _ ≤ _ := TauCeti.norm_inv_sqrt_smul_sub_inv_sqrt_smul_le x y x y
    _ ≤ ‖x - y‖ / √(1 + ‖x‖ ^ 2) + ‖x - y‖ / √(1 + ‖x‖ ^ 2) := add_le_add_right hcoef _
    _ = 2 * ‖x - y‖ / √(1 + ‖x‖ ^ 2) := by ring

/-- **Uniform closeness under `univUnitBall`.** If `‖x - y‖ ≤ δ (1 + ‖y‖)`, then
`‖univUnitBall x - univUnitBall y‖ ≤ 4 δ`: an error that grows at most like `y` becomes uniformly
small after the radial map onto the unit ball. -/
theorem norm_univUnitBall_sub_le_of_norm_sub_le {x y : E} {δ : ℝ}
    (h : ‖x - y‖ ≤ δ * (1 + ‖y‖)) : ‖univUnitBall x - univUnitBall y‖ ≤ 4 * δ := by
  have hB : 0 < √(1 + ‖y‖ ^ 2) := Real.sqrt_pos.2 (by positivity)
  have hδ : 0 ≤ δ := nonneg_of_mul_nonneg_left ((norm_nonneg _).trans h) (by positivity)
  rw [norm_sub_rev]
  refine (norm_univUnitBall_sub_le y x).trans ?_
  have hy := Real.one_add_div_two_le_sqrt_one_add_sq ‖y‖
  rw [div_le_iff₀ hB, norm_sub_rev]
  nlinarith

/-- Pairing with `univUnitBall a` and rescaling the second vector by the same factor
`(√(1 + ‖a‖²))⁻¹` turns the inner product with `a` into `(1 + ‖a‖²)⁻¹ ⟪a, x⟫`. -/
theorem inner_univUnitBall_inv_sqrt_smul {F : Type*} [SeminormedAddCommGroup F]
    [InnerProductSpace ℝ F] (a x : F) :
    ⟪univUnitBall a, (√(1 + ‖a‖ ^ 2))⁻¹ • x⟫_ℝ = (1 + ‖a‖ ^ 2)⁻¹ * ⟪a, x⟫_ℝ := by
  rw [univUnitBall_apply, real_inner_smul_left, real_inner_smul_right, ← mul_assoc, ← mul_inv,
    Real.mul_self_sqrt (by positivity)]

end OpenPartialHomeomorph

namespace TauCeti

variable {F : Type*} [SeminormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- **Uniform closeness of normalized inner products.** If `‖a - b‖ ≤ δ (1 + ‖b‖)`,
`‖a' - b'‖ ≤ δ (1 + ‖b‖)` and `‖b'‖ ≤ C (1 + ‖b‖)`, with `δ ≤ 1 / 2`, then
`(1 + ‖a‖²)⁻¹ ⟪a, a'⟫` and `(1 + ‖b‖²)⁻¹ ⟪b, b'⟫` differ by at most `(24 C + 12) δ`. This is the
inner-product companion of `TauCeti.norm_inv_sqrt_smul_sub_inv_sqrt_smul_le_of_norm_sub_le`. -/
theorem abs_inv_one_add_norm_sq_mul_inner_sub_le {a b a' b' : F} {δ C : ℝ}
    (hδ : δ ≤ 1 / 2) (ha : ‖a - b‖ ≤ δ * (1 + ‖b‖)) (ha' : ‖a' - b'‖ ≤ δ * (1 + ‖b‖))
    (hb' : ‖b'‖ ≤ C * (1 + ‖b‖)) :
    |(1 + ‖a‖ ^ 2)⁻¹ * ⟪a, a'⟫_ℝ - (1 + ‖b‖ ^ 2)⁻¹ * ⟪b, b'⟫_ℝ| ≤ (24 * C + 12) * δ := by
  have hδ0 : 0 ≤ δ := nonneg_of_mul_nonneg_left ((norm_nonneg _).trans ha) (by positivity)
  have hC : 0 ≤ C := nonneg_of_mul_nonneg_left ((norm_nonneg _).trans hb') (by positivity)
  set A := √(1 + ‖a‖ ^ 2)
  set B := √(1 + ‖b‖ ^ 2)
  set G := OpenPartialHomeomorph.univUnitBall (E := F)
  have hA : (1 + ‖b‖) / 4 ≤ A := one_add_norm_div_four_le_sqrt_one_add_norm_sq hδ ha
  have hA0 : 0 < A := lt_of_lt_of_le (by positivity) hA
  -- The three estimates: on `G a - G b`, on `a' / A` and on `a' / A - b' / B`.
  have hG : ‖G a - G b‖ ≤ 4 * δ :=
    OpenPartialHomeomorph.norm_univUnitBall_sub_le_of_norm_sub_le ha
  have hGb : ‖G b‖ ≤ 1 := OpenPartialHomeomorph.norm_univUnitBall_le b
  have hk : ‖A⁻¹ • a'‖ ≤ 4 * (C + δ) := by
    have := norm_le_norm_add_norm_sub' a' b'
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hA0, inv_mul_le_iff₀ hA0]
    nlinarith
  have hk' := norm_inv_sqrt_smul_sub_inv_sqrt_smul_le_of_norm_sub_le hδ ha ha' hb'
  -- Split the difference of inner products and estimate each term.
  rw [← OpenPartialHomeomorph.inner_univUnitBall_inv_sqrt_smul,
    ← OpenPartialHomeomorph.inner_univUnitBall_inv_sqrt_smul]
  have hsplit : ⟪G a, A⁻¹ • a'⟫_ℝ - ⟪G b, B⁻¹ • b'⟫_ℝ =
      ⟪G a - G b, A⁻¹ • a'⟫_ℝ + ⟪G b, A⁻¹ • a' - B⁻¹ • b'⟫_ℝ := by
    rw [inner_sub_left, inner_sub_right]
    abel
  rw [hsplit]
  have e₁ := abs_real_inner_le_norm (G a - G b) (A⁻¹ • a')
  have e₂ := abs_real_inner_le_norm (G b) (A⁻¹ • a' - B⁻¹ • b')
  have m₁ := mul_le_mul hG hk (by positivity) (by positivity)
  have m₂ := mul_le_mul hGb hk' (by positivity) zero_le_one
  calc _ ≤ |⟪G a - G b, A⁻¹ • a'⟫_ℝ| + |⟪G b, A⁻¹ • a' - B⁻¹ • b'⟫_ℝ| := abs_add_le _ _
    _ ≤ 4 * δ * (4 * (C + δ)) + 1 * ((4 + 8 * C) * δ) := by linarith
    _ ≤ (24 * C + 12) * δ := by nlinarith

end TauCeti
