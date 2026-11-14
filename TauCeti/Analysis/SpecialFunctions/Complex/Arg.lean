/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import TauCeti.Analysis.Complex.SlitPlane

/-!
# The argument of a quotient, and rotations onto the nonpositive real axis

Mathlib computes the argument of a quotient only modulo `2π` (`Complex.arg_div_coe_angle`), and
of a product exactly when the sum of the arguments lies in `(-π, π]`
(`Complex.arg_mul_eq_add_arg_iff`). This file records the analogue for quotients, and its most
common instances: two points of the open upper half-plane, of the open lower half-plane or of the
open right half-plane have arguments in a common open interval of length `π`, so the argument of
their quotient is the difference of their arguments. It also records that every
complex number is rotated onto the nonpositive real axis by the square of a unit complex number,
and computes the argument of `-e^{2iφ}` when `φ` is not a multiple of `π`.
A sector `{|arg ((z - v) / b)| < α}` of half-opening `α`, cut off by a punctured ball about its
vertex, is the image of an open rectangle in polar coordinates. On the slit plane `|arg z| < π`,
rotating `z` by `-arg z / 2` lands in the open right half-plane, and the exponential maps the
horizontal strip `|im x| < π` into the slit plane. Finally, the
argument is smooth on the slit plane, where its derivative is the imaginary part of that of the
logarithm, and although it jumps across the negative real axis, a smooth `2π`-periodic function of
the argument is smooth on the whole punctured plane: near the negative real axis it is computed
from the argument of `-z`.
Since the argument is continuous on the slit plane and blind to positive real scaling,
`arg (f x) → arg Q` as soon as some positive real multiple of `f x` tends to `Q ∈ slitPlane`.

## Main results

* `Complex.arg_div_eq_sub_arg_iff`: `arg (x / y) = arg x - arg y` exactly when
  `arg x - arg y ∈ (-π, π]`.
* `Complex.arg_div_of_im_pos`: if `0 < x.im` and `0 < y.im`, then `arg (x / y) = arg x - arg y`.
* `Complex.arg_div_of_im_neg`: if `x.im < 0` and `y.im < 0`, then `arg (x / y) = arg x - arg y`.
* `Complex.arg_div_of_re_pos`: if `0 < x.re` and `0 < y.re`, then `arg (x / y) = arg x - arg y`.
* `Complex.arg_eq_pi_div_two_sub_arctan_of_im_pos`: in the open upper half-plane,
  `arg w = π / 2 - arctan (re w / im w)`.
* `Complex.abs_arg_div_comm`: swapping numerator and denominator preserves `|arg (x / y)|`.
* `Complex.exists_norm_eq_one_mul_sq_eq_neg_norm`: every `c` has a unit `ω` with `c ω² = -‖c‖`.
* `Complex.exp_arg_mul_I`: `exp (i arg z) = z / |z|` for `z ≠ 0`.
* `Complex.contDiffOn_div_norm_pow`: `(z / |z|)^m` is smooth away from the origin.
* `TauCeti.image_polar_rectangle_eq`: in polar coordinates about `v`, rotated and scaled by `b`,
  the punctured truncated sector `{|arg ((z - v) / b)| < α}`, `α ≤ π`, is the image of an open
  rectangle.
* `Complex.arg_neg_exp_of_div_pi_ne`: if `φ / π` is not an integer, then
  `arg (-e^{2iφ}) = 2φ - π - 2π⌊φ / π⌋`.
* `Complex.inv_exp_arg_mul_le_exp_pi_mul_abs`: `(exp (arg u * r))⁻¹ ≤ exp (π * |r|)`.
* `Complex.abs_arg_lt_pi_of_mem_slitPlane`, `Complex.abs_arg_div_two_lt_pi_div_two`: on the slit
  plane `|arg z| < π`, and whenever `arg z ≠ π`, `|arg z / 2| < π / 2`.
* `Complex.one_le_re_one_add_ofReal_mul_exp_mul_I`,
  `Complex.one_add_ofReal_mul_exp_mul_I_mem_slitPlane`: shifted rays `1 + r e^{iθ}` (`r ≥ 0`) have
  real part at least `1` when `|θ| ≤ π / 2` and lie in `slitPlane` when `|θ| < π`.
* `Complex.re_mul_exp_neg_arg_div_two_mul_I_pos`,
  `Complex.mem_slitPlane_of_abs_le_of_re_mul_exp_mul_I_pos`,
  `Complex.re_mul_exp_mul_I_pos_of_mem_uIcc`: bisecting-ray positivity on `slitPlane` and angular
  convexity of `{θ ∈ [-π / 2, π / 2] | 0 < (z * e^{iθ}).re}`.
* `Complex.exp_mem_slitPlane_of_abs_im_lt`: `exp x` lies in the slit plane when `|im x| < π`.
* `Complex.contDiffAt_arg`: the argument is smooth on the slit plane.
* `Complex.tendsto_arg_of_tendsto_ofReal_mul`: if `c x * f x → Q ∈ slitPlane` with `c x > 0`
  eventually, then `arg (f x) → arg Q`.
* `HasDerivAt.hasFDerivAt_arg`: the real derivative of `arg ∘ f` on the slit plane is the
  imaginary part of the logarithmic derivative of `f`.
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

/-- The argument of the quotient of two points of the open lower half-plane is the difference of
their arguments. -/
theorem arg_div_of_im_neg {x y : ℂ} (hx : x.im < 0) (hy : y.im < 0) :
    arg (x / y) = arg x - arg y :=
  (arg_div_eq_sub_arg_iff (fun h ↦ hx.ne (by rw [h, zero_im]))
    (fun h ↦ hy.ne (by rw [h, zero_im]))).2
    ⟨by linarith [neg_pi_lt_arg x, arg_neg_iff.2 hy],
      by linarith [arg_neg_iff.2 hx, neg_pi_lt_arg y]⟩

/-- The argument of the quotient of two points of the open right half-plane is the difference of
their arguments. -/
theorem arg_div_of_re_pos {x y : ℂ} (hx : 0 < x.re) (hy : 0 < y.re) :
    arg (x / y) = arg x - arg y := by
  have hx' := abs_lt.1 (abs_arg_lt_pi_div_two_iff.2 (Or.inl hx))
  have hy' := abs_lt.1 (abs_arg_lt_pi_div_two_iff.2 (Or.inl hy))
  exact (arg_div_eq_sub_arg_iff (fun h ↦ hx.ne' (by rw [h, zero_re]))
    (fun h ↦ hy.ne' (by rw [h, zero_re]))).2 ⟨by linarith, by linarith⟩

/-- Swapping numerator and denominator preserves the absolute value of the argument of a
quotient. -/
theorem abs_arg_div_comm (a b : ℂ) : |(a / b).arg| = |(b / a).arg| := by
  rw [← inv_div, abs_arg_inv]

/-- A complex number in the open upper half-plane has argument within `π / 2` of `π / 2`. -/
theorem abs_arg_sub_pi_div_two_lt_of_im_pos {w : ℂ} (hw : 0 < w.im) :
    |w.arg - Real.pi / 2| < Real.pi / 2 := by
  have hpos : 0 < w.arg := by
    have hne : w.arg ≠ 0 := by
      intro h
      exact hw.ne' (arg_eq_zero_iff.mp h).2
    exact lt_of_le_of_ne (arg_nonneg_iff.mpr hw.le) (Ne.symm hne)
  have hlt := arg_lt_pi_iff.mpr (Or.inr hw.ne')
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

/-- In the open upper half-plane the argument is measured from the imaginary axis by an arctangent:
`arg w = π / 2 - arctan (re w / im w)`. -/
theorem arg_eq_pi_div_two_sub_arctan_of_im_pos {w : ℂ} (hw : 0 < w.im) :
    w.arg = π / 2 - Real.arctan (w.re / w.im) := by
  obtain ⟨h1, h2⟩ := abs_lt.1 (abs_arg_sub_pi_div_two_lt_of_im_pos hw)
  rw [Real.arctan_eq_of_tan_eq (x := π / 2 - w.arg) ?_ ⟨by linarith, by linarith⟩]
  · ring
  · rw [Real.tan_pi_div_two_sub, tan_arg, inv_div]

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

/-- If `φ / π` is not an integer, then `-e^{2iφ} = e^{iψ}` for the angle
`ψ = 2φ - π - 2π⌊φ / π⌋`, which lies in `(-π, π)`, so `ψ` is the argument of `-e^{2iφ}`. -/
theorem arg_neg_exp_of_div_pi_ne {φ : ℝ} (hφ : ∀ k : ℤ, φ / π ≠ k) :
    arg (-exp (↑(2 * φ) * I)) = 2 * φ - π - 2 * π * ⌊φ / π⌋ := by
  set x := φ / π with hx
  have hlt : (⌊x⌋ : ℝ) < x := lt_of_le_of_ne (Int.floor_le x) fun h => hφ _ h.symm
  have hlt' : x < ⌊x⌋ + 1 := Int.lt_floor_add_one x
  set ψ := 2 * φ - π - 2 * π * ⌊x⌋ with hψ
  have hφx : φ = x * π := by rw [hx]; field_simp
  have hψlo : -π < ψ := by
    rw [hψ, hφx]; nlinarith [pi_pos]
  have hψhi : ψ < π := by
    rw [hψ, hφx]; nlinarith [pi_pos]
  have hneg : -exp (↑(2 * φ) * I) = exp (↑ψ * I) := by
    have h2φ : (2 * φ : ℝ) = ψ + π + ⌊x⌋ * (2 * π) := by rw [hψ]; ring
    rw [h2φ]
    push_cast
    rw [add_mul, add_mul, exp_add, exp_add, exp_pi_mul_I, mul_assoc (⌊x⌋ : ℂ),
      exp_int_mul_two_pi_mul_I]
    ring
  rw [hneg, arg_exp_mul_I, (toIocMod_eq_self _).2 ⟨hψlo, by linarith⟩]

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

/-- The unit complex number `exp (i arg z)` is `z / |z|` for `z ≠ 0`. -/
theorem exp_arg_mul_I {z : ℂ} (hz : z ≠ 0) : exp (arg z * I) = z / (‖z‖ : ℂ) := by
  rw [eq_div_iff (ofReal_ne_zero.2 (norm_ne_zero_iff.2 hz)), mul_comm]
  exact norm_mul_exp_arg_mul_I z

/-- The power `(z / |z|)^m` of the unit direction is smooth away from the origin. -/
theorem contDiffOn_div_norm_pow (m : ℕ) {N : WithTop ℕ∞} :
    ContDiffOn ℝ N (fun z : ℂ ↦ (z / (‖z‖ : ℂ)) ^ m) {0}ᶜ := by
  intro z hz
  have hz : z ≠ 0 := hz
  have hn : ContDiffAt ℝ N (fun w : ℂ ↦ (‖w‖ : ℂ)) z :=
    ofRealCLM.contDiff.contDiffAt.comp z (contDiffAt_norm ℂ hz)
  have hp : ContDiffAt ℝ N (fun w : ℂ ↦ w / (‖w‖ : ℂ)) z := by
    simpa only [div_eq_mul_inv, Pi.inv_apply, id_eq] using
      contDiffAt_id.mul (hn.inv (ofReal_ne_zero.2 (norm_ne_zero_iff.2 hz)))
  exact (hp.pow m).contDiffWithinAt

/-- On the slit plane the argument lies strictly between `-π` and `π`. -/
theorem abs_arg_lt_pi_of_mem_slitPlane {z : ℂ} (hz : z ∈ slitPlane) : |arg z| < π :=
  abs_lt.2 ⟨neg_pi_lt_arg z, lt_of_le_of_ne (arg_le_pi z) (slitPlane_arg_ne_pi hz)⟩

/-- The exponential of a point of the horizontal strip `|im x| < π` lies in the slit plane. -/
theorem exp_mem_slitPlane_of_abs_im_lt {x : ℂ} (hx : |x.im| < π) : exp x ∈ slitPlane := by
  obtain ⟨h₁, h₂⟩ := abs_lt.1 hx
  rw [exp_mem_slitPlane, (toIocMod_eq_self _).2 ⟨h₁, by linarith [pi_pos]⟩]
  exact h₂.ne

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

/-- Along a ray in the closed right half-plane (`|θ| ≤ π / 2`, `0 ≤ r`), `1 + r * exp (θ * I)` has
real part at least `1`. -/
theorem one_le_re_one_add_ofReal_mul_exp_mul_I {θ r : ℝ} (hθ : |θ| ≤ π / 2) (hr : 0 ≤ r) :
    1 ≤ (1 + (r : ℂ) * exp ((θ : ℂ) * I)).re := by
  obtain ⟨h₁, h₂⟩ := abs_le.1 hθ
  have hcos : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc ⟨by linarith, h₂⟩
  have hre : (1 + (r : ℂ) * exp ((θ : ℂ) * I)).re = 1 + r * Real.cos θ := by
    simp [Complex.mul_re, exp_ofReal_mul_I_re]
  rw [hre]
  nlinarith

/-- Along any ray avoiding the negative real axis (`|θ| < π`, `0 ≤ r`), `1 + r * exp (θ * I)` lies
in the slit plane. -/
theorem one_add_ofReal_mul_exp_mul_I_mem_slitPlane {θ r : ℝ} (hθ : |θ| < π) (hr : 0 ≤ r) :
    1 + (r : ℂ) * exp ((θ : ℂ) * I) ∈ slitPlane := by
  rcases hr.eq_or_lt with rfl | hr
  · simp [slitPlane]
  rcases lt_trichotomy θ 0 with hneg | rfl | hpos
  · refine mem_slitPlane_iff.2 (Or.inr ?_)
    have hsin : Real.sin θ < 0 := Real.sin_neg_of_neg_of_neg_pi_lt hneg (abs_lt.1 hθ).1
    have him : (1 + (r : ℂ) * exp ((θ : ℂ) * I)).im = r * Real.sin θ := by
      simp [Complex.mul_im, exp_ofReal_mul_I_im]
    rw [him]
    exact (mul_neg_of_pos_of_neg hr hsin).ne
  · refine mem_slitPlane_iff.2 (Or.inl ?_)
    simp; linarith
  · refine mem_slitPlane_iff.2 (Or.inr ?_)
    have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hpos (abs_lt.1 hθ).2
    have him : (1 + (r : ℂ) * exp ((θ : ℂ) * I)).im = r * Real.sin θ := by
      simp [Complex.mul_im, exp_ofReal_mul_I_im]
    rw [him]
    exact (mul_pos hr hsin).ne'

/-- Away from the negative real axis (`arg z ≠ π`), half the principal argument lies strictly
between `-π / 2` and `π / 2`. -/
theorem abs_arg_div_two_lt_pi_div_two {z : ℂ} (hz : arg z ≠ π) : |arg z / 2| < π / 2 := by
  rw [abs_div, abs_two, div_lt_div_iff_of_pos_right two_pos]
  exact abs_lt.2 ⟨neg_pi_lt_arg z, (arg_le_pi z).lt_of_ne hz⟩

/-- Rotating a point `z` of the slit plane by `-arg z / 2` lands in the open right half-plane,
with real part `‖z‖ * cos (arg z / 2) > 0`. -/
theorem re_mul_exp_neg_arg_div_two_mul_I_pos {z : ℂ} (hz : z ∈ slitPlane) :
    0 < (z * exp ((-(arg z / 2) : ℝ) * I)).re := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  have hcos : 0 < Real.cos (arg z / 2) :=
    Real.cos_pos_of_mem_Ioo (abs_lt.1 (abs_arg_div_two_lt_pi_div_two (slitPlane_arg_ne_pi hz)))
  have hsum : (arg z : ℂ) * I + ((-(arg z / 2) : ℝ) : ℂ) * I = ((arg z / 2 : ℝ) : ℂ) * I := by
    push_cast; ring
  nth_rw 1 [(norm_mul_exp_arg_mul_I z).symm]
  rw [mul_assoc, ← exp_add, hsum, re_ofReal_mul, exp_ofReal_mul_I_re]
  exact mul_pos (norm_pos_iff.2 hz0) hcos

/-- If `z * exp (θ * I)` has positive real part for some angle `|θ| ≤ π / 2`, then `z` lies in the
slit plane. -/
theorem mem_slitPlane_of_abs_le_of_re_mul_exp_mul_I_pos {z : ℂ} {θ : ℝ}
    (hθ : |θ| ≤ π / 2) (hre : 0 < (z * exp ((θ : ℂ) * I)).re) : z ∈ slitPlane := by
  rcases hθ.lt_or_eq with hlt | heq
  · exact mul_div_cancel_right₀ z (exp_ne_zero _) ▸
      TauCeti.div_mem_slitPlane_of_re_pos
        (by rw [exp_ofReal_mul_I_re]; exact Real.cos_pos_of_mem_Ioo (abs_lt.1 hlt)) hre
  · refine mem_slitPlane_iff.2 (Or.inr fun him ↦ ?_)
    have hcos : Real.cos θ = 0 := by rw [← Real.cos_abs, heq, Real.cos_pi_div_two]
    have h0 : (z * exp ((θ : ℂ) * I)).re = 0 := by
      simp [Complex.mul_re, exp_ofReal_mul_I_re, hcos, him]
    exact hre.ne' h0

/-- For any two angles `θ₁, θ₂ ∈ [-π / 2, π / 2]` at which `z * exp (θ_i * I)` lies in the open
right half-plane, `z * exp (θ * I)` stays in the open right half-plane at every intermediate angle
`θ ∈ Set.uIcc θ₁ θ₂`. -/
theorem re_mul_exp_mul_I_pos_of_mem_uIcc {z : ℂ} {θ₁ θ₂ θ : ℝ}
    (hθ₁ : |θ₁| ≤ π / 2) (hre₁ : 0 < (z * exp ((θ₁ : ℂ) * I)).re)
    (hθ₂ : |θ₂| ≤ π / 2) (hre₂ : 0 < (z * exp ((θ₂ : ℂ) * I)).re)
    (hθ : θ ∈ Set.uIcc θ₁ θ₂) :
    0 < (z * exp ((θ : ℂ) * I)).re := by
  have hz : z ∈ slitPlane := mem_slitPlane_of_abs_le_of_re_mul_exp_mul_I_pos hθ₁ hre₁
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  have harg := abs_arg_lt_pi_of_mem_slitPlane hz
  have polar_re (y : ℝ) : (z * exp ((y : ℂ) * I)).re = ‖z‖ * Real.cos (arg z + y) := by
    have hsum : (arg z : ℂ) * I + (y : ℂ) * I = ((arg z + y : ℝ) : ℂ) * I := by push_cast; ring
    nth_rw 1 [(norm_mul_exp_arg_mul_I z).symm]
    rw [mul_assoc, ← exp_add, hsum, re_ofReal_mul, exp_ofReal_mul_I_re]
  have angle_lt {y : ℝ} (hy : |y| ≤ π / 2) (hpos : 0 < (z * exp ((y : ℂ) * I)).re) :
      |arg z + y| < π / 2 := by
    rw [polar_re, mul_pos_iff_of_pos_left (norm_pos_iff.2 hz0)] at hpos
    by_contra! hge
    have hub : |arg z + y| < 3 * π / 2 := by
      calc |arg z + y| ≤ |arg z| + |y| := abs_add_le _ _
        _ < π + π / 2 := add_lt_add_of_lt_of_le harg hy
        _ = 3 * π / 2 := by ring
    have hsin : 0 ≤ Real.sin (|arg z + y| - π / 2) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
    rw [Real.sin_sub_pi_div_two, Real.cos_abs] at hsin
    linarith
  obtain ⟨h₁l, h₁r⟩ := abs_lt.1 (angle_lt hθ₁ hre₁)
  obtain ⟨h₂l, h₂r⟩ := abs_lt.1 (angle_lt hθ₂ hre₂)
  rw [polar_re]
  rcases le_total θ₁ θ₂ with hle | hle
  · obtain ⟨hl, hr⟩ := (Set.uIcc_of_le hle ▸ hθ : θ ∈ Set.Icc θ₁ θ₂)
    exact mul_pos (norm_pos_iff.2 hz0) (Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩)
  · obtain ⟨hl, hr⟩ := (Set.uIcc_of_ge hle ▸ hθ : θ ∈ Set.Icc θ₂ θ₁)
    exact mul_pos (norm_pos_iff.2 hz0) (Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩)

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
`{|arg ((z - v) / b)| < α}` of half-opening `α`, cut off by the punctured ball of radius `δ`, is
the image of an open rectangle. -/
theorem image_polar_rectangle_eq {v b : ℂ} (hb : b ≠ 0) {δ α : ℝ} :
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
    · rw [hdiv]
      rcases le_or_gt α Real.pi with hα | hα
      · rw [arg_mul_cos_add_sin_mul_I hr ⟨by linarith [hθ.1, hθ.2], by linarith [hθ.2]⟩]
        exact abs_lt.mpr hθ
      · exact (abs_arg_le_pi _).trans_lt hα
  · rintro ⟨hzb, hzv, harg⟩
    have hw : (z - v) / b ≠ 0 := div_ne_zero (sub_ne_zero.mpr hzv) hb
    refine ⟨(‖(z - v) / b‖, ((z - v) / b).arg), ⟨⟨norm_pos_iff.mpr hw, ?_⟩, abs_lt.mp harg⟩, ?_⟩
    · rw [norm_div, div_lt_div_iff_of_pos_right hb', ← dist_eq_norm]
      exact mem_ball.mp hzb
    · simp only [norm_mul_cos_add_sin_mul_I]
      field_simp
      ring

end TauCeti
