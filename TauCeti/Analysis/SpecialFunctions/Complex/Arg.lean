/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# The argument of a quotient, and rotations onto the nonpositive real axis

Mathlib computes the argument of a quotient only modulo `2π` (`Complex.arg_div_coe_angle`), and
of a product exactly when the sum of the arguments lies in `(-π, π]`
(`Complex.arg_mul_eq_add_arg_iff`). This file records the analogue for quotients, and its most
common instance: for two points of the open upper half-plane the arguments lie in `(0, π)`, so
the argument of their quotient is the difference of their arguments. It also records that every
complex number is rotated onto the nonpositive real axis by the square of a unit complex number.
A sector `{|arg ((z - v) / b)| < α}` of half-opening `α ≤ π`, cut off by a punctured ball about its
vertex, is the image of an open rectangle in polar coordinates. Finally, the argument is smooth on
the slit plane, where its derivative is the imaginary part of that of the logarithm, and although it
jumps across the negative real axis, a smooth `2π`-periodic function of the argument is smooth on
the whole punctured plane: near the negative real axis it is computed from the argument of `-z`.
Since the argument is continuous on the slit plane and blind to positive real scaling,
`arg (f x) → arg Q` as soon as some positive real multiple of `f x` tends to `Q ∈ slitPlane`.

## Main results

* `Complex.arg_div_eq_sub_arg_iff`: `arg (x / y) = arg x - arg y` exactly when
  `arg x - arg y ∈ (-π, π]`.
* `Complex.arg_div_of_im_pos`: if `0 < x.im` and `0 < y.im`, then `arg (x / y) = arg x - arg y`.
* `Complex.abs_arg_div_comm`: swapping numerator and denominator preserves `|arg (x / y)|`.
* `Complex.exists_norm_eq_one_mul_sq_eq_neg_norm`: every `c` has a unit `ω` with `c ω² = -‖c‖`.
* `TauCeti.image_polar_rectangle_eq`: in polar coordinates about `v`, rotated and scaled by `b`,
  the punctured truncated sector `{|arg ((z - v) / b)| < α}`, `α ≤ π`, is the image of an open
  rectangle.
* `Complex.inv_exp_arg_mul_le_exp_pi_mul_abs`: `(exp (arg u * r))⁻¹ ≤ exp (π * |r|)`.
* `Complex.contDiffAt_arg`: the argument is smooth on the slit plane.
* `HasDerivAt.hasFDerivAt_arg`: the real derivative of `arg ∘ f` on the slit plane is the
  imaginary part of the logarithmic derivative of `f`.
* `Complex.tendsto_arg_of_tendsto_ofReal_mul`: if `c x * f x → Q ∈ slitPlane` with `c x > 0`
  eventually, then `arg (f x) → arg Q`.
* `ContDiff.contDiffAt_comp_arg`: a smooth `2π`-periodic function of the argument is smooth away
  from the origin.
-/

public section

open Real

namespace Complex

/-- The argument of a quotient is the difference of the arguments exactly when that difference
lies in `(-π, π]`. -/
theorem arg_div_eq_sub_arg_iff {x y : ℂ} (hx₀ : x ≠ 0) (hy₀ : y ≠ 0) :
    arg (x / y) = arg x - arg y ↔ arg x - arg y ∈ Set.Ioc (-π) π := by
  rw [← arg_coe_angle_toReal_eq_arg, arg_div_coe_angle hx₀ hy₀, ← Real.Angle.coe_sub,
    Real.Angle.toReal_coe_eq_self_iff_mem_Ioc]

/-- The argument of the quotient of two points of the open upper half-plane is the difference of
their arguments. -/
theorem arg_div_of_im_pos {x y : ℂ} (hx : 0 < x.im) (hy : 0 < y.im) :
    arg (x / y) = arg x - arg y :=
  (arg_div_eq_sub_arg_iff (fun h ↦ hx.ne' (by rw [h, zero_im]))
    (fun h ↦ hy.ne' (by rw [h, zero_im]))).2
    ⟨by linarith [arg_nonneg_iff.2 hx.le, arg_lt_pi_iff.2 (Or.inr hy.ne')],
      by linarith [arg_nonneg_iff.2 hy.le, arg_le_pi x]⟩

/-- Swapping numerator and denominator preserves the absolute value of the argument of a
quotient. -/
theorem abs_arg_div_comm (a b : ℂ) : |(a / b).arg| = |(b / a).arg| := by
  rw [← inv_div, abs_arg_inv]

/-- Every complex number `c` is rotated onto the nonpositive real axis by the square of a unit:
`c ω² = -‖c‖`. -/
theorem exists_norm_eq_one_mul_sq_eq_neg_norm (c : ℂ) :
    ∃ ω : ℂ, ‖ω‖ = 1 ∧ c * ω ^ 2 = -‖c‖ := by
  refine ⟨exp (((π - arg c) / 2 : ℝ) * I), norm_exp_ofReal_mul_I _, ?_⟩
  have h : (arg c : ℂ) * I + 2 * (((π - arg c) / 2 : ℝ) * I) = π * I := by
    push_cast
    ring
  calc c * exp (((π - arg c) / 2 : ℝ) * I) ^ 2
      = ‖c‖ * exp ((arg c : ℂ) * I + 2 * (((π - arg c) / 2 : ℝ) * I)) := by
        rw [exp_add, ← mul_assoc, norm_mul_exp_arg_mul_I, ← exp_nat_mul]
        norm_num
    _ = -‖c‖ := by
        rw [h, exp_pi_mul_I]
        ring

/-- The inverse of `exp (arg u * r)` is at most `exp (π * |r|)`. -/
theorem inv_exp_arg_mul_le_exp_pi_mul_abs (u : ℂ) (r : ℝ) :
    (Real.exp (u.arg * r))⁻¹ ≤ Real.exp (Real.pi * |r|) := by
  rw [← Real.exp_neg]
  apply Real.exp_le_exp.mpr
  calc -(u.arg * r) ≤ |u.arg * r| := neg_le_abs _
    _ = |u.arg| * |r| := abs_mul _ _
    _ ≤ Real.pi * |r| := by
      gcongr
      exact abs_arg_le_pi _

/-- The argument is smooth on the slit plane, where it is the imaginary part of the principal
logarithm. -/
theorem contDiffAt_arg {z : ℂ} (hz : z ∈ slitPlane) {n : WithTop ℕ∞} : ContDiffAt ℝ n arg z := by
  have h := (imCLM.contDiff.contDiffAt (n := n) (x := log z)).comp z
    ((contDiffAt_log hz (n := n)).restrict_scalars ℝ)
  exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w ↦ (log_im w).symm)

open Filter Topology in
/-- Positive real scaling does not move the argument: if `Q ∈ slitPlane`, eventually `0 < c x`,
and `c x * f x → Q`, then `arg (f x) → arg Q`. -/
theorem tendsto_arg_of_tendsto_ofReal_mul {α : Type*} {l : Filter α} {c : α → ℝ} {f : α → ℂ}
    {Q : ℂ} (hQ : Q ∈ slitPlane) (hc : ∀ᶠ x in l, 0 < c x)
    (h : Tendsto (fun x ↦ (c x : ℂ) * f x) l (𝓝 Q)) :
    Tendsto (fun x ↦ arg (f x)) l (𝓝 (arg Q)) :=
  ((continuousAt_arg hQ).tendsto.comp h).congr' (hc.mono fun _ hx ↦ arg_real_mul _ hx)

end Complex

/-- If `f` has complex derivative `f'` at `z` and `f z` lies in the slit plane, then the argument
`w ↦ arg (f w)` has real derivative `v ↦ Im (v * f' / f z)` at `z`, the imaginary part of the
derivative of `log ∘ f`. -/
theorem HasDerivAt.hasFDerivAt_arg {f : ℂ → ℂ} {f' z : ℂ} (hf : HasDerivAt f f' z)
    (hz : f z ∈ Complex.slitPlane) :
    HasFDerivAt (fun w ↦ Complex.arg (f w))
      (Complex.imCLM ∘L
        ((ContinuousLinearMap.toSpanSingleton ℂ (f' / f z)).restrictScalars ℝ)) z := by
  simpa only [Function.comp_def, Complex.imCLM_apply, Complex.log_im] using
    Complex.imCLM.hasFDerivAt.comp z ((hf.clog hz).hasFDerivAt.restrictScalars ℝ)

/-- A `2π`-periodic function of the argument of a nonzero complex number `z` may be computed from
the argument of `-z`, which differs from that of `z` by `π` modulo `2π`. -/
theorem Function.Periodic.apply_arg_eq_apply_arg_neg_add_pi {α : Type*} {g : ℝ → α}
    (hg : Function.Periodic g (2 * π)) {z : ℂ} (hz : z ≠ 0) :
    g (Complex.arg z) = g (Complex.arg (-z) + π) := by
  have h := Complex.arg_neg_coe_angle (neg_ne_zero.2 hz)
  rw [neg_neg, ← Real.Angle.coe_add, Real.Angle.angle_eq_iff_two_pi_dvd_sub] at h
  obtain ⟨k, hk⟩ := h
  rw [show Complex.arg z = Complex.arg (-z) + π + k * (2 * π) by linarith]
  exact hg.int_mul k _

/-- A smooth `2π`-periodic function of the argument is smooth away from the origin, although the
argument itself jumps across the negative real axis. -/
theorem ContDiff.contDiffAt_comp_arg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : ℝ → E} {n : WithTop ℕ∞} (hg : ContDiff ℝ n g) (hper : Function.Periodic g (2 * π))
    {z : ℂ} (hz : z ≠ 0) : ContDiffAt ℝ n (fun w ↦ g (Complex.arg w)) z := by
  rcases Complex.mem_slitPlane_or_neg_mem_slitPlane hz with h | h
  · exact hg.contDiffAt.comp z (Complex.contDiffAt_arg h)
  · have h' : ContDiffAt ℝ n (fun w : ℂ ↦ Complex.arg (-w) + π) z :=
      ((Complex.contDiffAt_arg h).comp z contDiff_neg.contDiffAt).add contDiffAt_const
    refine (hg.contDiffAt.comp z h').congr_of_eventuallyEq ?_
    filter_upwards [isOpen_ne.mem_nhds hz] with w hw
    exact hper.apply_arg_eq_apply_arg_neg_add_pi hw

namespace TauCeti

open Complex Metric Set

/-- In polar coordinates about `v`, rotated and scaled by `b`, the open sector
`{|arg ((z - v) / b)| < α}` of half-opening `α ≤ π`, cut off by the punctured ball of radius `δ`, is
the image of an open rectangle. -/
theorem image_polar_rectangle_eq {v b : ℂ} (hb : b ≠ 0) {δ α : ℝ} (hα : α ≤ Real.pi) :
    (fun p : ℝ × ℝ => v + b * ((p.1 : ℂ) * (Complex.cos (p.2 : ℂ) + Complex.sin (p.2 : ℂ) * I))) ''
        (Ioo 0 (δ / ‖b‖) ×ˢ Ioo (-α) α) =
      {z | z ∈ ball v δ ∧ z ≠ v ∧ |((z - v) / b).arg| < α} := by
  have hb' : 0 < ‖b‖ := norm_pos_iff.mpr hb
  ext z
  constructor
  · rintro ⟨⟨r, θ⟩, ⟨⟨hr, hrδ⟩, hθ⟩, rfl⟩
    have hdiv : (v + b * ((r : ℂ) * (Complex.cos (θ : ℂ) + Complex.sin (θ : ℂ) * I)) - v) / b =
        (r : ℂ) * (Complex.cos (θ : ℂ) + Complex.sin (θ : ℂ) * I) := by
      field_simp
      ring
    have hnorm : ‖v + b * ((r : ℂ) * (Complex.cos (θ : ℂ) + Complex.sin (θ : ℂ) * I)) - v‖ =
        ‖b‖ * r := by
      rw [add_sub_cancel_left, norm_mul, norm_mul, norm_real, norm_cos_add_sin_mul_I,
        Real.norm_of_nonneg hr.le, mul_one]
    refine ⟨?_, fun h => ?_, ?_⟩
    · rw [mem_ball, dist_eq_norm, hnorm]
      rwa [lt_div_iff₀' hb'] at hrδ
    · beta_reduce at h
      rw [h, sub_self, norm_zero] at hnorm
      exact (mul_pos hb' hr).ne' hnorm.symm
    · rw [hdiv, arg_mul_cos_add_sin_mul_I hr ⟨by linarith [hθ.1, hθ.2], by linarith [hθ.2]⟩]
      exact abs_lt.mpr hθ
  · rintro ⟨hzb, hzv, harg⟩
    have hw : (z - v) / b ≠ 0 := div_ne_zero (sub_ne_zero.mpr hzv) hb
    refine ⟨(‖(z - v) / b‖, ((z - v) / b).arg), ⟨⟨norm_pos_iff.mpr hw, ?_⟩, abs_lt.mp harg⟩, ?_⟩
    · rw [norm_div, div_lt_div_iff_of_pos_right hb', ← dist_eq_norm]
      exact mem_ball.mp hzb
    · simp only [norm_mul_cos_add_sin_mul_I]
      field_simp
      ring

end TauCeti
