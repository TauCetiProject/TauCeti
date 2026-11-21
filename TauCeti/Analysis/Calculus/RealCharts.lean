/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Algebra.Order.Group.Pointwise.Interval
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Real.Sqrt

/-!
# Elementary real charts for one-dimensional changes of variables

This file records reusable calculus facts about elementary real charts that recur in density and
special-function computations. The order-theoretic facts hold in any linearly ordered field and
the derivative formulas in any nontrivially normed field; only the image computations that take
square roots are specific to `ℝ`.

## Main results

* `TauCeti.strictMonoOn_div_one_sub`, `TauCeti.image_div_one_sub_Ioo`, and
  `TauCeti.hasDerivAt_div_one_sub` describe the chart `u ↦ u / (1 - u)` on intervals below `1`;
* `TauCeti.div_one_sub_factors` rewrites affine factors in this chart over any field, and
  `TauCeti.div_one_sub_Ioo_chart` collects the facts for a monotone change of variables;
* `TauCeti.image_sq_div_const_Ioi`, `TauCeti.injOn_sq_div_const_Ioi`, and
  `TauCeti.hasDerivAt_sq_div_const` describe the square chart `z ↦ z ^ 2 / ν` on positive
  half-lines;
* `TauCeti.image_add_mul_div_sq_add_Ioi` describes the chart `t ↦ c + p q / (t ^ 2 + p)` on the
  positive half-line.
-/

public section

namespace TauCeti

open Set

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-! ### The chart `u ↦ u / (1 - u)` -/

/-- Rewrite the affine factors `1 + v` and `1 + v - z * v` for `v = u / (1 - u)`. -/
lemma div_one_sub_factors {K : Type*} [Field K] {u : K} (hu : 1 - u ≠ 0) (z : K) :
    1 + u / (1 - u) = (1 - u)⁻¹ ∧
      1 + u / (1 - u) - z * (u / (1 - u)) = (1 - z * u) * (1 - u)⁻¹ := by
  have h : 1 + u / (1 - u) = (1 - u)⁻¹ := by
    rw [one_add_div hu, sub_add_cancel, one_div]
  exact ⟨h, by rw [h, div_eq_mul_inv, sub_mul, one_mul, mul_assoc]⟩

/-- The chart `u ↦ u / (1 - u)` is strictly increasing on `(-∞, 1)`. -/
lemma strictMonoOn_div_one_sub : StrictMonoOn (fun u : α => u / (1 - u)) (Iio 1) := by
  intro u hu v hv huv
  rw [div_lt_div_iff₀ (sub_pos.2 hu) (sub_pos.2 hv)]
  nlinarith

/-- The chart `u ↦ u / (1 - u)` carries `(u₀, 1)` onto `(u₀ / (1 - u₀), ∞)` for `u₀ < 1`. -/
lemma image_div_one_sub_Ioo {u0 : α} (hu1 : u0 < 1) :
    (fun u : α => u / (1 - u)) '' Ioo u0 1 = Ioi (u0 / (1 - u0)) := by
  have heq : EqOn (fun u : α => u / (1 - u)) ((· - 1) ∘ (·⁻¹) ∘ (1 - ·)) (Ioo u0 1) :=
    fun u hu => by
      have : (1 : α) - u ≠ 0 := (sub_pos.2 hu.2).ne'
      simp only [Function.comp_apply]
      field_simp
      ring
  have h0 : (0 : α) < 1 - u0 := sub_pos.2 hu1
  rw [heq.image_eq, image_comp, image_comp, image_const_sub_Ioo, sub_self, image_inv_eq_inv,
    inv_Ioo_0_left h0, image_sub_const_Ioi]
  congr 1
  field_simp
  ring

/-- The derivative of the chart `u ↦ u / (1 - u)` is `(1 - u) ^ (-2)`. -/
lemma hasDerivAt_div_one_sub {u : 𝕜} (hu : u ≠ 1) :
    HasDerivAt (fun t : 𝕜 => t / (1 - t)) ((1 - u) ^ 2)⁻¹ u :=
  ((hasDerivAt_id' u).div ((hasDerivAt_id' u).const_sub 1)
    (sub_ne_zero.2 hu.symm)).congr_deriv (by ring)

/-- The image, within-interval derivative, and monotonicity of the chart `u ↦ u / (1 - u)`
on `(ρ, 1)`, for monotone changes of variables. -/
lemma div_one_sub_Ioo_chart [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] {ρ : 𝕜} (hρ : ρ < 1) :
    (fun u : 𝕜 => u / (1 - u)) '' Ioo ρ 1 = Ioi (ρ / (1 - ρ)) ∧
      (∀ u ∈ Ioo ρ 1, HasDerivWithinAt (fun t : 𝕜 => t / (1 - t))
        ((1 - u) ^ 2)⁻¹ (Ioo ρ 1) u) ∧
      MonotoneOn (fun u : 𝕜 => u / (1 - u)) (Ioo ρ 1) :=
  ⟨image_div_one_sub_Ioo hρ,
    fun _ hu => (hasDerivAt_div_one_sub hu.2.ne).hasDerivWithinAt,
    strictMonoOn_div_one_sub.monotoneOn.mono Ioo_subset_Iio_self⟩

/-! ### The square chart on the positive half-line -/

/-- The square chart `z ↦ z ^ 2 / ν` carries `(y, ∞)` onto `(y ^ 2 / ν, ∞)` for
`0 ≤ y` and `0 < ν`. -/
lemma image_sq_div_const_Ioi {ν : ℝ} (hν : 0 < ν) {y : ℝ} (hy : 0 ≤ y) :
    (fun z : ℝ => z ^ 2 / ν) '' Ioi y = Ioi (y ^ 2 / ν) := by
  ext w
  simp only [mem_image, mem_Ioi]
  constructor
  · rintro ⟨z, hz, rfl⟩
    gcongr
  · intro hw
    have hνw : y ^ 2 < ν * w := by rwa [← div_lt_iff₀' hν]
    refine ⟨√(ν * w), (Real.lt_sqrt hy).2 hνw, ?_⟩
    rw [Real.sq_sqrt ((sq_nonneg y).trans hνw.le)]
    field_simp

/-- The chart `z ↦ z ^ 2 / ν` is injective on the positive half-line for nonzero `ν`. -/
lemma injOn_sq_div_const_Ioi {ν : α} (hν : ν ≠ 0) :
    InjOn (fun z : α => z ^ 2 / ν) (Ioi 0) := fun _ hz _ hw h =>
  (pow_left_strictMonoOn₀ two_ne_zero).injOn (mem_Ici.2 (le_of_lt hz)) (mem_Ici.2 (le_of_lt hw))
    ((div_left_inj₀ hν).1 h)

/-- The derivative of the chart `z ↦ z ^ 2 / ν`. -/
lemma hasDerivAt_sq_div_const (ν z : 𝕜) :
    HasDerivAt (fun x : 𝕜 => x ^ 2 / ν) (2 * z / ν) z := by
  simpa using (hasDerivAt_pow 2 z).div_const ν

/-! ### The chart `t ↦ c + p q / (t ^ 2 + p)` -/

/-- For `0 < p` and `0 < q`, the chart `t ↦ c + p q / (t ^ 2 + p)` carries `(0, ∞)` onto
`(c, c + q)`. -/
lemma image_add_mul_div_sq_add_Ioi {c p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    (fun t : ℝ ↦ c + p * q / (t ^ 2 + p)) '' Ioi 0 = Ioo c (c + q) := by
  have hsq := image_sq_div_const_Ioi one_pos (y := 0) le_rfl
  have hcomp : (fun t : ℝ ↦ c + p * q / (t ^ 2 + p)) =
      (c + ·) ∘ (p * q * ·) ∘ (·⁻¹) ∘ (· + p) ∘ (fun t : ℝ ↦ t ^ 2 / 1) := by
    ext t
    simp [div_eq_mul_inv]
  simp only [hcomp, image_comp, hsq, image_add_const_Ioi, image_inv_eq_inv]
  rw [inv_Ioi₀ (by simpa using hp), image_mul_left_Ioo (by positivity), image_const_add_Ioo]
  simp [mul_right_comm p q, hp.ne']

end TauCeti
