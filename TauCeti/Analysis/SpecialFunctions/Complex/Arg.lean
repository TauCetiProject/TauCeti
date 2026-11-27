/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.Complex.Angle
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import TauCeti.Analysis.Complex.SlitPlane
import TauCeti.Analysis.SpecialFunctions.Trigonometric.Bounds
import TauCeti.Analysis.SpecialFunctions.Trigonometric.FiniteProduct

/-!
# The argument of a quotient, and rotations onto the nonpositive real axis

Mathlib computes the argument of a quotient only modulo `2π` (`Complex.arg_div_coe_angle`), and
of a product exactly when the sum of the arguments lies in `(-π, π]`
(`Complex.arg_mul_eq_add_arg_iff`). This file records the analogue for quotients, and its most
common instances: two points of the open upper half-plane, of the open lower half-plane or of the
open right half-plane have arguments in a common open interval of length `π`, so the argument of
their quotient is the difference of their arguments. Dually, the arguments of two points of the
slit plane whose imaginary parts have opposite signs add up to a value in `(-π, π)`, and in the
right half-plane those of `z - 1` and `z + 1` add up to a value in `(-π, π]`. It also records that
every complex number is rotated onto the nonpositive real axis by the square of a unit complex
number, and computes the argument of `-e^{2iφ}` when `φ` is not a multiple of `π`, and that of
`1 - e^{iθ}` for `0 < θ < 2π`.
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
In polar coordinates, `Im (z ^ m) = |z|^m sin(m arg z)` for every integer `m`.

## Main results

* `Complex.arg_div_eq_sub_arg_iff`: `arg (x / y) = arg x - arg y` exactly when
  `arg x - arg y ∈ (-π, π]`.
* `Complex.exists_arg_div_add_arg_eq`: in general `arg (x / y) + arg y` is `arg x` up to a multiple
  of `2π`.
* `Complex.arg_div_of_im_pos`: if `0 < x.im` and `0 < y.im`, then `arg (x / y) = arg x - arg y`.
* `Complex.arg_div_of_im_neg`: if `x.im < 0` and `y.im < 0`, then `arg (x / y) = arg x - arg y`.
* `Complex.arg_div_of_re_pos`: if `0 < x.re` and `0 < y.re`, then `arg (x / y) = arg x - arg y`.
* `Complex.arg_add_arg_mem_Ioo_of_im_mul_nonpos`: two points of the slit plane whose imaginary
  parts do not have the same strict sign have arguments adding up to a value in `(-π, π)`.
* `Complex.arg_sub_one_add_arg_add_one_mem_Ioc`: for `0 < re z`,
  `arg (z - 1) + arg (z + 1) ∈ (-π, π]`.
* `Complex.arg_eq_pi_div_two_sub_arctan_of_im_pos`: in the open upper half-plane,
  `arg w = π / 2 - arctan (re w / im w)`.
* `Complex.pi_div_two_sub_arg_le_div`: for `0 ≤ z.re` and `0 < z.im`,
  `π / 2 - arg z ≤ re z / im z`.
* `Complex.abs_arg_div_comm`: swapping numerator and denominator preserves `|arg (x / y)|`.
* `Complex.exists_norm_eq_one_mul_sq_eq_neg_norm`: every `c` has a unit `ω` with `c ω² = -‖c‖`.
* `Complex.exp_arg_mul_I`: `exp (i arg z) = z / |z|` for `z ≠ 0`.
* `Complex.contDiffOn_div_norm_pow`: `(z / |z|)^m` is smooth away from the origin.
* `TauCeti.image_polar_rectangle_eq`: in polar coordinates about `v`, rotated and scaled by `b`,
  the punctured truncated sector `{|arg ((z - v) / b)| < α}` is the image of an open rectangle.
* `Complex.arg_neg_exp_of_div_pi_ne`: if `φ / π` is not an integer, then
  `arg (-e^{2iφ}) = 2φ - π - 2π⌊φ / π⌋`.
* `Complex.arg_one_sub_exp_mul_I`: `arg (1 - exp (θ i)) = (θ - π) / 2` for `0 < θ < 2π`.
* `Complex.inv_exp_arg_mul_le_exp_pi_mul_abs`: `(exp (arg u * r))⁻¹ ≤ exp (π * |r|)`.
* `Complex.abs_arg_lt_pi_of_mem_slitPlane`, `Complex.abs_arg_div_two_le_pi_div_two`,
  `Complex.abs_arg_div_two_lt_pi_div_two`: `|arg z / 2| ≤ π / 2` for every `z`, with strict
  inequality when `arg z ≠ π` and `|arg z| < π` on `slitPlane`.
* `Complex.isOpen_slitPlane_inter_abs_arg_lt`: for any `α : ℝ`, the sector
  `{w : ℂ | w ∈ slitPlane ∧ |arg w| < α}` in the slit plane is open.
* `Complex.exists_mem_nhds_slitPlane_norm_and_arg_lt`: a point `w₀ ∈ slitPlane` with `|arg w₀| < α`
  has a neighborhood in `slitPlane` with norm bounded away from `0` and `∞` and `|arg w| ≤ α' < α`.
* `Complex.one_add_mul_cos_div_two_le_norm_one_add_ofReal_mul_exp_mul_I`,
  `Complex.norm_one_add_ofReal_mul_exp_mul_I_le`,
  `Complex.one_add_ofReal_mul_exp_mul_I_mem_slitPlane`: along polar rays `1 + r e^{iθ}`,
  the norm lies between `(1 + r) cos (θ / 2)` and `1 + |r|`, and `1 + r e^{iθ} ∈ slitPlane`
  when `|θ| < π` and `0 ≤ r`.
* `Complex.re_mul_exp_ofReal_mul_I_eq_norm_mul_cos`,
  `Complex.re_mul_exp_neg_arg_div_two_mul_I_pos`,
  `Complex.abs_arg_add_lt_pi_div_two_of_abs_le_of_re_mul_exp_mul_I_pos`,
  `Complex.mem_slitPlane_of_abs_le_of_re_mul_exp_mul_I_pos`,
  `Complex.re_mul_exp_mul_I_pos_of_mem_uIcc`: polar formula `(z * e^{iy}).re = ‖z‖ cos (arg z + y)`,
  bisecting-ray positivity on `slitPlane`, and angular convexity of `{θ | 0 < (z * e^{iθ}).re}`
  on intervals of length at most `π`.
* `Complex.exp_mem_slitPlane_of_abs_im_lt`: `exp x` lies in the slit plane when `|im x| < π`.
* `Complex.abs_arg_le_pi_div_two_mul_norm_sub_one`: on the unit circle, `|arg z| ≤ (π / 2) ‖z - 1‖`.
* `Complex.contDiffAt_arg`: the argument is smooth on the slit plane.
* `TauCeti.continuousAt_abs_arg`: `|arg z|`, the unoriented angle with `1`, is continuous away
  from the origin, across the negative real axis too.
* `Complex.tendsto_arg_of_tendsto_ofReal_mul`: if `c x * f x → Q ∈ slitPlane` with `c x > 0`
  eventually, then `arg (f x) → arg Q`.
* `Complex.im_zpow`: `Im (z ^ m) = |z|^m sin(m arg z)` for every integer `m`.
* `Complex.sin_arg_sub_arg_one_sub`: `sin (arg ξ - arg (1 - ξ)) = Im ξ / (|ξ| |1 - ξ|)`; for `ξ`
  in the upper half-plane, the sine of the angle at `ξ` of the triangle `0, 1, ξ`.
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

/-- The argument of a quotient plus that of the denominator is the argument of the numerator up
to a multiple of `2π`. -/
theorem exists_arg_div_add_arg_eq {x y : ℂ} (hx₀ : x ≠ 0) (hy₀ : y ≠ 0) :
    ∃ m : ℤ, arg (x / y) + arg y = arg x + 2 * π * m := by
  have h := arg_div_coe_angle hx₀ hy₀
  rw [← Real.Angle.coe_sub, Real.Angle.angle_eq_iff_two_pi_dvd_sub] at h
  obtain ⟨m, hm⟩ := h
  exact ⟨m, by linarith⟩

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

/-- A complex number has argument within `π / 2` of `π / 2`, that is, in `(0, π)`, exactly when
it lies in the open upper half-plane. -/
@[simp]
theorem abs_arg_sub_pi_div_two_lt_iff {w : ℂ} : |w.arg - π / 2| < π / 2 ↔ 0 < w.im := by
  rw [abs_sub_lt_iff]
  refine ⟨fun h ↦ ?_, fun hw ↦ ?_⟩
  · -- `0 < arg w` rules out the nonnegative real axis, and `arg w < π` the negative one
    have h₀ : 0 < w.arg := by linarith [h.2]
    refine (arg_nonneg_iff.1 h₀.le).lt_of_ne' fun him ↦ h₀.ne' (arg_eq_zero_iff.2 ⟨?_, him⟩)
    exact (arg_lt_pi_iff.1 (by linarith [h.1])).resolve_right (not_not.2 him)
  · have h₀ : 0 < w.arg :=
      (arg_nonneg_iff.2 hw.le).lt_of_ne' fun h ↦ hw.ne' (arg_eq_zero_iff.1 h).2
    have hπ := arg_lt_pi_iff.2 (Or.inr hw.ne')
    constructor <;> linarith

/-- In the open upper half-plane the argument is measured from the imaginary axis by an arctangent:
`arg w = π / 2 - arctan (re w / im w)`. -/
theorem arg_eq_pi_div_two_sub_arctan_of_im_pos {w : ℂ} (hw : 0 < w.im) :
    w.arg = π / 2 - Real.arctan (w.re / w.im) := by
  obtain ⟨h1, h2⟩ := abs_lt.1 (abs_arg_sub_pi_div_two_lt_iff.2 hw)
  rw [Real.arctan_eq_of_tan_eq (x := π / 2 - w.arg) ?_ ⟨by linarith, by linarith⟩]
  · ring
  · rw [Real.tan_pi_div_two_sub, tan_arg, inv_div]

/-- If `0 ≤ z.re` and `0 < z.im`, then `arg z` falls short of `π / 2` by at most
`re z / im z`. -/
theorem pi_div_two_sub_arg_le_div {z : ℂ} (hre : 0 ≤ z.re) (him : 0 < z.im) :
    π / 2 - z.arg ≤ z.re / z.im := by
  rw [arg_eq_pi_div_two_sub_arctan_of_im_pos him, sub_sub_cancel]
  exact Real.arctan_le_self (div_nonneg hre him.le)

/-- Every complex number `c` is rotated onto the nonpositive real axis by the square of a unit:
`c ω² = -‖c‖`. -/
theorem exists_norm_eq_one_mul_sq_eq_neg_norm (c : ℂ) :
    ∃ ω : ℂ, ‖ω‖ = 1 ∧ c * ω ^ 2 = -‖c‖ := by
  refine ⟨exp (((π - arg c) / 2 : ℝ) * I), norm_exp_ofReal_mul_I _, ?_⟩
  -- `c ω² = ‖c‖ e^{i arg c} e^{i (π - arg c)} = ‖c‖ e^{iπ}`
  have h : (arg c : ℂ) * I + (2 : ℕ) * (((π - arg c) / 2 : ℝ) * I) = π * I := by
    push_cast
    ring
  nth_rw 1 [← norm_mul_exp_arg_mul_I c]
  rw [mul_assoc, ← exp_natCast_mul, ← exp_add, h, exp_pi_mul_I]
  exact mul_neg_one _

/-- If `φ / π` is not an integer, then `-e^{2iφ} = e^{iψ}` for the angle
`ψ = 2φ - π - 2π⌊φ / π⌋`, which lies in `(-π, π)`, so `ψ` is the argument of `-e^{2iφ}`. -/
theorem arg_neg_exp_of_div_pi_ne {φ : ℝ} (hφ : ∀ k : ℤ, φ / π ≠ k) :
    arg (-exp (↑(2 * φ) * I)) = 2 * φ - π - 2 * π * ⌊φ / π⌋ := by
  -- `-e^{2iφ} = e^{i(2φ - π)}`, and `ψ` is the representative of `2φ - π` in `(-π, π]`
  rw [← exp_sub_pi_mul_I, ← sub_mul, ← ofReal_sub, arg_exp_mul_I, toIocMod_eq_iff]
  refine ⟨?_, ⌊φ / π⌋, by rw [zsmul_eq_mul]; ring⟩
  -- `ψ = 2π fract (φ / π) - π`, and `0 < fract (φ / π) < 1` as `φ / π` is not an integer
  have hψ : 2 * φ - π - 2 * π * ⌊φ / π⌋ = 2 * π * Int.fract (φ / π) - π := by
    rw [Int.fract]
    field_simp
    ring
  have hfr : 0 < Int.fract (φ / π) := Int.fract_pos.2 fun h ↦ hφ _ h
  rw [hψ]
  constructor <;> nlinarith [pi_pos, Int.fract_lt_one (φ / π)]

/-- The argument of `1 - exp (θ i)` for `0 < θ < 2π`: since
`1 - exp (θ i) = 2 sin (θ / 2) exp ((θ - π) i / 2)` with `sin (θ / 2) > 0`, it is `(θ - π) / 2`. -/
theorem arg_one_sub_exp_mul_I {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (2 * π)) :
    arg (1 - exp (θ * I)) = (θ - π) / 2 := by
  -- `1 - e^{iθ} = -2i e^{iθ/2} sin (θ/2) = 2 sin (θ/2) e^{i(θ - π)/2}`, with `sin (θ/2) > 0`
  have hfac : 1 - exp (θ * I) =
      ((2 * Real.sin (θ / 2) : ℝ) : ℂ) * exp (((θ - π) / 2 : ℝ) * I) := by
    rw [mul_comm (θ : ℂ) I, one_sub_exp_mul_I, show (((θ - π) / 2 : ℝ) : ℂ) * I =
      I * θ / 2 + -(π / 2) * I by push_cast; ring, Complex.exp_add, ← log_neg_I,
      exp_log (neg_ne_zero.2 I_ne_zero)]
    push_cast
    ring
  have hsin : 0 < Real.sin (θ / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2])
  rw [hfac, arg_ofReal_mul (by positivity), arg_exp_mul_I, toIocMod_eq_self]
  constructor <;> linarith [hθ.1, hθ.2, Real.pi_pos]

/-- The inverse of `exp (arg u * r)` is at most `exp (π * |r|)`. -/
theorem inv_exp_arg_mul_le_exp_pi_mul_abs (u : ℂ) (r : ℝ) :
    (Real.exp (u.arg * r))⁻¹ ≤ Real.exp (Real.pi * |r|) := by
  rw [← Real.exp_neg, Real.exp_le_exp]
  calc -(u.arg * r) ≤ |u.arg| * |r| := (neg_le_abs _).trans_eq (abs_mul _ _)
    _ ≤ Real.pi * |r| := by gcongr; exact abs_arg_le_pi _

/-- The unit complex number `exp (i arg z)` is `z / |z|` for `z ≠ 0`. -/
theorem exp_arg_mul_I {z : ℂ} (hz : z ≠ 0) : exp (arg z * I) = z / (‖z‖ : ℂ) := by
  rw [eq_div_iff (ofReal_ne_zero.2 (norm_ne_zero_iff.2 hz)), mul_comm]
  exact norm_mul_exp_arg_mul_I z

/-- The unit direction `z / |z|` is homogeneous of degree `0` under positive dilations. -/
theorem smul_div_norm_smul {t : ℝ} (ht : 0 < t) (z : ℂ) :
    t • z / (‖t • z‖ : ℂ) = z / (‖z‖ : ℂ) := by
  simpa [NormedSpace.normalize, real_smul, div_eq_inv_mul] using
    NormedSpace.normalize_smul_of_pos ht z

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

/-- The arguments of two points of the slit plane whose imaginary parts do not have the same strict
sign add up to a value in `(-π, π)`. -/
theorem arg_add_arg_mem_Ioo_of_im_mul_nonpos {x y : ℂ} (hx : x ∈ slitPlane) (hy : y ∈ slitPlane)
    (h : x.im * y.im ≤ 0) : arg x + arg y ∈ Set.Ioo (-π) π := by
  have hx' := abs_lt.1 (abs_arg_lt_pi_of_mem_slitPlane hx)
  have hy' := abs_lt.1 (abs_arg_lt_pi_of_mem_slitPlane hy)
  -- on the slit plane, `arg w ≤ 0` when `im w ≤ 0`, by conjugation
  have hle : ∀ {w : ℂ}, w ∈ slitPlane → w.im ≤ 0 → arg w ≤ 0 := fun {w} hw hw' => by
    have := arg_nonneg_iff.2 (by simpa using hw' : 0 ≤ ((starRingEnd ℂ) w).im)
    simp only [arg_conj, slitPlane_arg_ne_pi hw, ite_false] at this
    linarith
  rcases mul_nonpos_iff.1 h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · have := arg_nonneg_iff.2 h₁
    have := hle hy h₂
    constructor <;> linarith
  · have := hle hx h₁
    have := arg_nonneg_iff.2 h₂
    constructor <;> linarith

/-- In the right half-plane the arguments of `z - 1` and `z + 1` add up to a value in the principal
range `(-π, π]`. -/
theorem arg_sub_one_add_arg_add_one_mem_Ioc {z : ℂ} (hre : 0 < z.re) :
    arg (z - 1) + arg (z + 1) ∈ Set.Ioc (-π) π := by
  have hy : z + 1 ∈ slitPlane := mem_slitPlane_iff.2 (Or.inl (by simp; linarith))
  by_cases hz : z - 1 ∈ slitPlane
  · -- `(z² - 1) * conj (z + 1)` is a positive multiple of `z - 1`, and its two factors have
    -- imaginary parts of opposite signs
    have hp := sq_sub_one_mem_slitPlane hz hre
    have hc : (starRingEnd ℂ) (z + 1) ∈ slitPlane := conj_mem_slitPlane.2 hy
    have h := (arg_mul_eq_add_arg_iff (slitPlane_ne_zero hp) (slitPlane_ne_zero hc)).2
      (Set.Ioo_subset_Ioc_self (arg_add_arg_mem_Ioo_of_im_mul_nonpos hp hc (by
        simp only [sub_im, one_im, sub_zero, sq, mul_im, conj_im, add_im]
        nlinarith [mul_nonneg hre.le (mul_self_nonneg z.im)])))
    rw [show (z ^ 2 - 1) * (starRingEnd ℂ) (z + 1) = (z - 1) * ((normSq (z + 1) : ℝ) : ℂ) by
        rw [← mul_conj]; ring,
      arg_mul_ofReal _ (normSq_pos.2 (slitPlane_ne_zero hy))] at h
    simp only [arg_conj, slitPlane_arg_ne_pi hy, ite_false] at h
    rw [show arg (z - 1) + arg (z + 1) = arg (z ^ 2 - 1) by linarith]
    exact arg_mem_Ioc _
  · have him : z.im = 0 := by simpa using im_eq_zero_of_notMem_slitPlane hz
    rw [(arg_eq_zero_iff (z := z + 1)).2 ⟨by simp; linarith, by simp [him]⟩, add_zero]
    exact arg_mem_Ioc _

/-- For any `α : ℝ`, the sector `{w : ℂ | w ∈ slitPlane ∧ |arg w| < α}` in the slit plane is
open. -/
theorem isOpen_slitPlane_inter_abs_arg_lt (α : ℝ) :
    IsOpen {w : ℂ | w ∈ slitPlane ∧ |arg w| < α} :=
  continuousOn_arg.abs.isOpen_inter_preimage isOpen_slitPlane isOpen_Iio

open Filter Topology in
/-- Around any point `w₀ ∈ slitPlane` with `|arg w₀| < α`, there is a neighborhood contained in
`slitPlane` on which the norm is bounded away from `0` and `∞` and `|arg w|` stays bounded by a
constant `α' < α`. -/
theorem exists_mem_nhds_slitPlane_norm_and_arg_lt {w₀ : ℂ} {α : ℝ}
    (hw₀ : w₀ ∈ slitPlane) (harg : |arg w₀| < α) :
    ∃ U ∈ 𝓝 w₀, ∃ r₀ r₁ α' : ℝ,
      0 < r₀ ∧ α' < α ∧
      ∀ w ∈ U, w ∈ slitPlane ∧ r₀ ≤ ‖w‖ ∧ ‖w‖ ≤ r₁ ∧ |arg w| ≤ α' := by
  have hnorm_pos : 0 < ‖w₀‖ := norm_pos_iff.mpr (slitPlane_ne_zero hw₀)
  let r₀ := ‖w₀‖ / 2
  let r₁ := 2 * ‖w₀‖
  let α' := (|arg w₀| + α) / 2
  have hα'_gt : |arg w₀| < α' := by dsimp [α']; linarith
  have hU_slit : slitPlane ∈ 𝓝 w₀ := isOpen_slitPlane.mem_nhds hw₀
  have hU_lo : {w : ℂ | r₀ < ‖w‖} ∈ 𝓝 w₀ :=
    (isOpen_lt continuous_const continuous_norm).mem_nhds (by dsimp [r₀]; linarith)
  have hU_hi : {w : ℂ | ‖w‖ < r₁} ∈ 𝓝 w₀ :=
    (isOpen_lt continuous_norm continuous_const).mem_nhds (by dsimp [r₁]; linarith)
  have hU_arg : {w : ℂ | |arg w| < α'} ∈ 𝓝 w₀ :=
    (continuousAt_arg hw₀).abs.preimage_mem_nhds (Iio_mem_nhds hα'_gt)
  refine ⟨slitPlane ∩ {w | r₀ < ‖w‖} ∩ {w | ‖w‖ < r₁} ∩ {w | |arg w| < α'},
    inter_mem (inter_mem (inter_mem hU_slit hU_lo) hU_hi) hU_arg,
    r₀, r₁, α', by positivity, by dsimp [α']; linarith, ?_⟩
  rintro w ⟨⟨⟨hslit, hlo⟩, hhi⟩, harg'⟩
  exact ⟨hslit, le_of_lt hlo, le_of_lt hhi, le_of_lt harg'⟩

/-- The exponential of a point of the horizontal strip `|im x| < π` lies in the slit plane. -/
theorem exp_mem_slitPlane_of_abs_im_lt {x : ℂ} (hx : |x.im| < π) : exp x ∈ slitPlane := by
  obtain ⟨h₁, h₂⟩ := abs_lt.1 hx
  rw [exp_mem_slitPlane, (toIocMod_eq_self _).2 ⟨h₁, by linarith [pi_pos]⟩]
  exact h₂.ne

/-- **The argument near one on the unit circle.** A unit complex number `z` has
`|arg z| ≤ (π / 2) ‖z - 1‖`: writing `z = exp (i θ)` with `θ = arg z`, `‖z - 1‖ = 2 |sin (θ / 2)|`
and Jordan's inequality gives `|θ| / 2 ≤ (π / 2) sin (|θ| / 2)`. -/
theorem abs_arg_le_pi_div_two_mul_norm_sub_one {z : ℂ} (hz : ‖z‖ = 1) :
    |arg z| ≤ π / 2 * ‖z - 1‖ := by
  have hz' : ‖z - 1‖ = 2 * |Real.sin (arg z / 2)| := by
    conv_lhs => rw [← norm_mul_exp_arg_mul_I z, hz, ofReal_one, one_mul, mul_comm]
    rw [norm_exp_I_mul_ofReal_sub_one, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_two]
  have hj := TauCeti.le_pi_div_two_mul_sin (θ := |arg z| / 2) (by positivity)
    (by linarith [abs_arg_le_pi z])
  have hsin : Real.sin (|arg z| / 2) ≤ |Real.sin (arg z / 2)| := by
    rcases abs_cases (arg z) with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h]
    · exact le_abs_self _
    · rw [neg_div, Real.sin_neg]
      exact neg_le_abs _
  rw [hz']
  nlinarith [pi_pos]

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
  ((continuousAt_arg hQ).tendsto.comp h).congr' (hc.mono fun _ hx ↦ arg_ofReal_mul hx _)

/-- Rotating `1 + r * exp (θ * I)` by `exp (-(θ / 2) * I)` projects onto the bisecting direction,
giving `(1 + r) * cos (θ / 2) ≤ ‖1 + r * exp (θ * I)‖` for all real `θ` and `r`. -/
theorem one_add_mul_cos_div_two_le_norm_one_add_ofReal_mul_exp_mul_I (θ r : ℝ) :
    (1 + r) * Real.cos (θ / 2) ≤ ‖1 + (r : ℂ) * exp ((θ : ℂ) * I)‖ := by
  have hrot : (1 + (r : ℂ) * exp ((θ : ℂ) * I)) * exp ((-(θ / 2) : ℝ) * I) =
      exp ((-(θ / 2) : ℝ) * I) + (r : ℂ) * exp (((θ / 2) : ℝ) * I) := by
    rw [add_mul, one_mul, mul_assoc, ← exp_add, ← add_mul, ← ofReal_add, ← sub_eq_add_neg, sub_half]
  have hre : (exp ((-(θ / 2) : ℝ) * I) + (r : ℂ) * exp (((θ / 2) : ℝ) * I)).re =
      (1 + r) * Real.cos (θ / 2) := by
    rw [add_re, re_ofReal_mul, exp_ofReal_mul_I_re, exp_ofReal_mul_I_re, Real.cos_neg]; ring
  exact (hre ▸ re_le_norm _).trans_eq <| by
    rw [← hrot, norm_mul, norm_exp_ofReal_mul_I, mul_one]

/-- For any real angle `θ` and real scalar `r`, `‖1 + r * exp (θ * I)‖ ≤ 1 + |r|`. -/
theorem norm_one_add_ofReal_mul_exp_mul_I_le (θ r : ℝ) :
    ‖1 + (r : ℂ) * exp ((θ : ℂ) * I)‖ ≤ 1 + |r| :=
  (norm_add_le _ _).trans_eq (by simp [norm_exp_ofReal_mul_I])

/-- Along any ray avoiding the negative real axis (`|θ| < π`, `0 ≤ r`), `1 + r * exp (θ * I)` lies
in the slit plane. -/
theorem one_add_ofReal_mul_exp_mul_I_mem_slitPlane {θ r : ℝ} (hθ : |θ| < π) (hr : 0 ≤ r) :
    1 + (r : ℂ) * exp ((θ : ℂ) * I) ∈ slitPlane := by
  rcases hr.eq_or_lt with rfl | hr
  · simp [slitPlane]
  · simpa using TauCeti.ofReal_add_mem_slitPlane
      (TauCeti.ofReal_mul_mem_slitPlane hr (exp_mem_slitPlane_of_abs_im_lt (by simpa using hθ)))
      zero_le_one

/-- Half the principal argument of any complex number lies in `[-π / 2, π / 2]`. -/
theorem abs_arg_div_two_le_pi_div_two (z : ℂ) : |arg z / 2| ≤ π / 2 := by
  rw [abs_div, abs_two]
  exact div_le_div_of_nonneg_right (abs_arg_le_pi z) two_pos.le

/-- Away from the negative real axis (`arg z ≠ π`), half the principal argument lies strictly
between `-π / 2` and `π / 2`. -/
theorem abs_arg_div_two_lt_pi_div_two {z : ℂ} (hz : arg z ≠ π) : |arg z / 2| < π / 2 := by
  rw [abs_div, abs_two, div_lt_div_iff_of_pos_right two_pos]
  exact abs_lt.2 ⟨neg_pi_lt_arg z, (arg_le_pi z).lt_of_ne hz⟩

/-- In polar coordinates, the real part of `z * exp (y * I)` is `‖z‖ * cos (arg z + y)`. -/
theorem re_mul_exp_ofReal_mul_I_eq_norm_mul_cos (z : ℂ) (y : ℝ) :
    (z * exp ((y : ℂ) * I)).re = ‖z‖ * Real.cos (arg z + y) := by
  nth_rw 1 [(norm_mul_exp_arg_mul_I z).symm]
  rw [mul_assoc, ← exp_add, ← add_mul, ← ofReal_add, re_ofReal_mul, exp_ofReal_mul_I_re]

/-- Rotating a point `z` of the slit plane by `-arg z / 2` lands in the open right half-plane,
with real part `‖z‖ * cos (arg z / 2) > 0`. -/
theorem re_mul_exp_neg_arg_div_two_mul_I_pos {z : ℂ} (hz : z ∈ slitPlane) :
    0 < (z * exp ((-(arg z / 2) : ℝ) * I)).re := by
  rw [re_mul_exp_ofReal_mul_I_eq_norm_mul_cos, ← sub_eq_add_neg, sub_half]
  exact mul_pos (norm_pos_iff.2 (slitPlane_ne_zero hz))
    (Real.cos_pos_of_mem_Ioo (abs_lt.1 (abs_arg_div_two_lt_pi_div_two (slitPlane_arg_ne_pi hz))))

/-- If `z * exp (θ * I)` has positive real part for some angle `|θ| ≤ π / 2`, then
`|arg z + θ| < π / 2`. -/
theorem abs_arg_add_lt_pi_div_two_of_abs_le_of_re_mul_exp_mul_I_pos {z : ℂ} {θ : ℝ}
    (hθ : |θ| ≤ π / 2) (hre : 0 < (z * exp ((θ : ℂ) * I)).re) :
    |arg z + θ| < π / 2 := by
  have hz0 : z ≠ 0 := fun hz => by simp [hz] at hre
  rw [re_mul_exp_ofReal_mul_I_eq_norm_mul_cos, mul_pos_iff_of_pos_left (norm_pos_iff.2 hz0)]
    at hre
  by_contra! hge
  have hub : |arg z + θ| ≤ 3 * π / 2 :=
    (abs_add_le _ _).trans (by linarith [abs_arg_le_pi z])
  have hsin : 0 ≤ Real.sin (|arg z + θ| - π / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  rw [Real.sin_sub_pi_div_two, Real.cos_abs] at hsin
  linarith

/-- If `z * exp (θ * I)` has positive real part for some angle `|θ| ≤ π / 2`, then `z` lies in the
slit plane. -/
theorem mem_slitPlane_of_abs_le_of_re_mul_exp_mul_I_pos {z : ℂ} {θ : ℝ}
    (hθ : |θ| ≤ π / 2) (hre : 0 < (z * exp ((θ : ℂ) * I)).re) : z ∈ slitPlane := by
  have hz0 : z ≠ 0 := fun hz => by simp [hz] at hre
  have hlt := (abs_lt.1 (abs_arg_add_lt_pi_div_two_of_abs_le_of_re_mul_exp_mul_I_pos hθ hre)).2
  exact mem_slitPlane_iff_arg.2 ⟨by linarith [(abs_le.1 hθ).1], hz0⟩

/-- If `z * exp (θ₁ * I)` and `z * exp (θ₂ * I)` both have positive real part at two angles
separated by `|θ₁ - θ₂| ≤ π`, then `z * exp (θ * I)` stays in the open right half-plane at every
intermediate angle `θ ∈ Set.uIcc θ₁ θ₂`. -/
theorem re_mul_exp_mul_I_pos_of_mem_uIcc {z : ℂ} {θ₁ θ₂ θ : ℝ}
    (hθ₁₂ : |θ₁ - θ₂| ≤ π) (hre₁ : 0 < (z * exp ((θ₁ : ℂ) * I)).re)
    (hre₂ : 0 < (z * exp ((θ₂ : ℂ) * I)).re) (hθ : θ ∈ Set.uIcc θ₁ θ₂) :
    0 < (z * exp ((θ : ℂ) * I)).re := by
  set m : ℝ := (θ₁ + θ₂) / 2
  set w : ℂ := z * exp ((m : ℂ) * I)
  have hshift (y : ℝ) : (w * exp (((y - m : ℝ) : ℂ) * I)).re = (z * exp ((y : ℂ) * I)).re := by
    dsimp only [w]
    rw [mul_assoc, ← exp_add, ← add_mul, ← ofReal_add, add_sub_cancel]
  obtain ⟨h12l, h12r⟩ := abs_le.1 hθ₁₂
  have hδ₁ : |θ₁ - m| ≤ π / 2 := by rw [abs_le]; dsimp only [m]; constructor <;> linarith
  have hδ₂ : |θ₂ - m| ≤ π / 2 := by rw [abs_le]; dsimp only [m]; constructor <;> linarith
  have hre₁' : 0 < (w * exp (((θ₁ - m : ℝ) : ℂ) * I)).re := (hshift θ₁).symm ▸ hre₁
  have hw0 : w ≠ 0 := fun hw => by simp [hw] at hre₁'
  obtain ⟨h₁l, h₁r⟩ := abs_lt.1
    (abs_arg_add_lt_pi_div_two_of_abs_le_of_re_mul_exp_mul_I_pos hδ₁ hre₁')
  obtain ⟨h₂l, h₂r⟩ := abs_lt.1
    (abs_arg_add_lt_pi_div_two_of_abs_le_of_re_mul_exp_mul_I_pos hδ₂ ((hshift θ₂).symm ▸ hre₂))
  rw [← hshift θ, re_mul_exp_ofReal_mul_I_eq_norm_mul_cos]
  rcases Set.mem_uIcc.1 hθ with ⟨hl, hr⟩ | ⟨hl, hr⟩ <;>
    exact mul_pos (norm_pos_iff.2 hw0) (Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩)

/-- `Im (z ^ m) = |z|^m sin(m arg z)` for every integer `m`. -/
theorem im_zpow (z : ℂ) (m : ℤ) : (z ^ m).im = ‖z‖ ^ m * Real.sin (m * arg z) := by
  conv_lhs => rw [← norm_mul_exp_arg_mul_I z]
  rw [mul_zpow, ← exp_intCast_mul, ← ofReal_zpow, ← mul_assoc, ← ofReal_intCast, ← ofReal_mul,
    im_ofReal_mul, exp_ofReal_mul_I_im]

/-- `sin (arg ξ - arg (1 - ξ)) = Im ξ / (|ξ| |1 - ξ|)` for every `ξ`; both sides vanish at `ξ = 0`
and `ξ = 1`. For `ξ` in the upper half-plane, `π - arg ξ + arg (1 - ξ)` is the angle at `ξ` of the
triangle `0, 1, ξ`, so this is the sine of that angle. -/
theorem sin_arg_sub_arg_one_sub (ξ : ℂ) :
    Real.sin (arg ξ - arg (1 - ξ)) = ξ.im / (‖ξ‖ * ‖1 - ξ‖) := by
  rcases eq_or_ne ξ 0 with rfl | h₀
  · simp
  rcases eq_or_ne ξ 1 with rfl | h₁
  · simp
  have h₁ : 1 - ξ ≠ 0 := sub_ne_zero.2 (Ne.symm h₁)
  rw [Real.sin_sub, sin_arg, sin_arg, cos_arg h₀, cos_arg h₁]
  have : ‖ξ‖ ≠ 0 := norm_ne_zero_iff.2 h₀
  have : ‖1 - ξ‖ ≠ 0 := norm_ne_zero_iff.2 h₁
  field_simp
  simp
  ring

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

/-- The absolute value of the argument, the unoriented angle with `1`, is continuous away from
`0`, across the negative real axis too, where the argument itself jumps. -/
theorem continuousAt_abs_arg {w : ℂ} (hw : w ≠ 0) : ContinuousAt (fun z : ℂ => |z.arg|) w := by
  have hangle : ContinuousAt (fun z : ℂ => InnerProductGeometry.angle z 1) w :=
    (InnerProductGeometry.continuousAt_angle (x := (w, (1 : ℂ))) hw one_ne_zero).comp
      (f := fun z : ℂ => (z, (1 : ℂ))) (by fun_prop)
  refine hangle.congr ?_
  filter_upwards [isOpen_ne.mem_nhds hw] with z hz
  exact angle_one_right hz

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
