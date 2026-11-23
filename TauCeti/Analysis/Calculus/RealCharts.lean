/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.JacobianOneDim
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
* `TauCeti.integral_Ioi_eq_integral_div_one_sub` and
  `TauCeti.integrableOn_Ioi_iff_integrableOn_div_one_sub` give substitution formulas for this chart;
* `TauCeti.image_sq_div_const_Ioi`, `TauCeti.injOn_sq_div_const_Ioi`, and
  `TauCeti.hasDerivAt_sq_div_const` describe the square chart `z ↦ z ^ 2 / ν` on positive
  half-lines;
* `TauCeti.image_add_mul_div_sq_add_Ioi` describes the chart `t ↦ c + p q / (t ^ 2 + p)` on the
  positive half-line.
-/

public section

namespace TauCeti

open Set MeasureTheory

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-! ### The chart `u ↦ u / (1 - u)` -/

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

/-- The substitution `v = u / (1 - u)` identifies integration over the ray starting at
`ρ / (1 - ρ)` with integration over `(ρ, 1)`, including totalized integrals without convergence
hypotheses. The positive Jacobian is `(1 - u)⁻²`. -/
theorem integral_Ioi_eq_integral_div_one_sub {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f : ℝ → F) {ρ : ℝ} (hρ : ρ < 1) :
    ∫ v in Ioi (ρ / (1 - ρ)), f v =
      ∫ u in Ioo ρ 1, ((1 - u) ^ 2)⁻¹ • f (u / (1 - u)) := by
  rw [← image_div_one_sub_Ioo hρ]
  exact integral_image_eq_integral_deriv_smul_of_monotoneOn measurableSet_Ioo
    (fun u hu ↦ (hasDerivAt_div_one_sub hu.2.ne).hasDerivWithinAt)
    (strictMonoOn_div_one_sub.monotoneOn.mono Ioo_subset_Iio_self) f

/-- Absolute integrability is preserved by the substitution `v = u / (1 - u)` from `(ρ, 1)`
onto the ray starting at `ρ / (1 - ρ)`, with its Jacobian included in the pulled-back function. -/
theorem integrableOn_Ioi_iff_integrableOn_div_one_sub {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f : ℝ → F) {ρ : ℝ} (hρ : ρ < 1) :
    IntegrableOn f (Ioi (ρ / (1 - ρ))) ↔
      IntegrableOn (fun u ↦ ((1 - u) ^ 2)⁻¹ • f (u / (1 - u))) (Ioo ρ 1) := by
  rw [← image_div_one_sub_Ioo hρ]
  exact integrableOn_image_iff_integrableOn_deriv_smul_of_monotoneOn measurableSet_Ioo
    (fun u hu ↦ (hasDerivAt_div_one_sub hu.2.ne).hasDerivWithinAt)
    (strictMonoOn_div_one_sub.monotoneOn.mono Ioo_subset_Iio_self) f

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
