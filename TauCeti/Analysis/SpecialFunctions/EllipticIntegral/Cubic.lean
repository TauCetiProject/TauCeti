/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.EllipticIntegral.Legendre
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import TauCeti.Analysis.SpecialFunctions.EllipticIntegral.Algebraic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# Integrals of the inverse square root of a real cubic

Let `D` be a real cubic with leading coefficient `4` and distinct roots. The integral of
`D(x)^(-1/2)` over an interval on which `D` is positive, with endpoints at roots of `D` or at
`+∞`, is a multiple of a complete elliptic integral of the first kind. This file proves the three
classical cases, each as an identity between Lebesgue integrals of nonnegative functions in
`ℝ≥0∞`, so that the integrals are genuine (convergent) and not junk values.

* **Three real roots** `e₃ < e₂ < e₁`, `D(x) = 4(x - e₁)(x - e₂)(x - e₃)`, with modulus
  `k = √((e₂ - e₃)/(e₁ - e₃))`: both `∫_{(e₁, ∞)} D(x)^(-1/2) dx` and `∫_{(e₃, e₂)} D(x)^(-1/2) dx`
  equal `K(k) / √(e₁ - e₃)` (the first also when `e₃ = e₂`). The substitutions are
  `x = e₃ + (e₁ - e₃) / t²` and `x = e₃ + (e₂ - e₃) t²` for `t ∈ (0, 1)`, which turn both
  integrals into the algebraic form `∫₀¹ ((1 - t²)(1 - k² t²))^(-1/2) dt` of `K(k)`.
* **One real root** `e₁`, `D(x) = 4(x - e₁)((x - a)² + b²)` with `b ≠ 0` (or a double root
  `a < e₁`). With
  `A = √((e₁ - a)² + b²)` and modulus `k = √((A + a - e₁)/(2A))`, the integral
  `∫_{(e₁, ∞)} D(x)^(-1/2) dx` equals `K(k) / √A`. The substitution is
  `x = e₁ + A (1 - cos θ)/(1 + cos θ)` for `θ ∈ (0, π)`, which turns it into
  `(2√A)⁻¹ F(π, k) = K(k) / √A`.

The set where `D > 0` is `(e₃, e₂) ∪ (e₁, ∞)` in the first case and `(e₁, ∞)` in the second, so
these are the integrals defining the real period of an elliptic curve over `ℝ` whose
`2`-division polynomial `Ψ₂Sq` has these roots.

## Main statements

* `TauCeti.Real.lintegral_Ioi_inv_sqrt_cubic_eq_legendreK`: the unbounded interval, three real
  roots;
* `TauCeti.Real.lintegral_Ioo_inv_sqrt_cubic_eq_legendreK`: the bounded interval, three real roots;
* `TauCeti.Real.lintegral_Ioi_inv_sqrt_mul_sq_add_sq_eq_legendreK`: one real root.

## References

* P. F. Byrd and M. D. Friedman, *Handbook of Elliptic Integrals for Engineers and Scientists*,
  2nd ed., Springer, 1971, formulas 236.00 and 239.00.
* J. E. Cremona, *Algorithms for Modular Elliptic Curves*, 2nd ed., Cambridge, 1997, §3.7.
-/

public section

namespace TauCeti.Real

open _root_.Real MeasureTheory Set

/-- The pointwise identity behind each substitution: if the cubic at the substituted point is
`d² c p`, where `d` is the derivative of the substitution, then the transformed integrand is
`(√c)⁻¹ p^(-1/2)`. -/
private lemma ofReal_abs_mul_ofReal_inv_sqrt {d c p D : ℝ} (hd : d ≠ 0) (hc : 0 < c)
    (hp : 0 ≤ p) (hD : D = d ^ 2 * c * p) :
    ENNReal.ofReal |d| * ENNReal.ofReal (√D)⁻¹ =
      ENNReal.ofReal ((√c)⁻¹ * p ^ (-1 / 2 : ℝ)) := by
  rw [← ENNReal.ofReal_mul (abs_nonneg d), hD, sqrt_mul (by positivity), sqrt_mul (sq_nonneg _),
    sqrt_sq_eq_abs, neg_div, rpow_neg hp, ← sqrt_eq_rpow, mul_inv, mul_inv, mul_assoc,
    mul_inv_cancel_left₀ (abs_ne_zero.2 hd)]

/-- Pulling the constant `(√c)⁻¹` out of a Lebesgue integral of a real function. -/
private lemma lintegral_ofReal_inv_sqrt_mul {c : ℝ} (s : Set ℝ) (g : ℝ → ℝ) :
    ∫⁻ t in s, ENNReal.ofReal ((√c)⁻¹ * g t) =
      ENNReal.ofReal (√c)⁻¹ * ∫⁻ t in s, ENNReal.ofReal (g t) := by
  simp_rw [ENNReal.ofReal_mul (inv_nonneg.2 (sqrt_nonneg c))]
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- The change of variables shared by the two cases with three real roots: if `f` maps `(0, 1)`
injectively onto `S`, with derivative `f'`, and the cubic at `f t` is
`f'(t)² (e₁ - e₃)(1 - t²)(1 - k² t²)` with `k² = (e₂ - e₃)/(e₁ - e₃)`, then the integral over `S`
is `(√(e₁ - e₃))⁻¹` times the algebraic form of `K(k)`. -/
private lemma lintegral_eq_legendreK_of_subst {e₁ e₂ e₃ : ℝ} (h₃₂ : e₃ ≤ e₂) (h₂₁ : e₂ < e₁)
    {f f' : ℝ → ℝ} {S : Set ℝ} (himage : f '' Ioo 0 1 = S)
    (hf' : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivWithinAt f (f' t) (Ioo 0 1) t)
    (hf : InjOn f (Ioo 0 1)) (hf'0 : ∀ t ∈ Ioo (0 : ℝ) 1, f' t ≠ 0)
    (hD : ∀ t ∈ Ioo (0 : ℝ) 1, 4 * (f t - e₁) * (f t - e₂) * (f t - e₃) =
      f' t ^ 2 * (e₁ - e₃) * ((1 - t ^ 2) * (1 - (e₂ - e₃) / (e₁ - e₃) * t ^ 2))) :
    ∫⁻ x in S, ENNReal.ofReal (√(4 * (x - e₁) * (x - e₂) * (x - e₃)))⁻¹ =
      ENNReal.ofReal (legendreK √((e₂ - e₃) / (e₁ - e₃)) / √(e₁ - e₃)) := by
  have hc : 0 < e₁ - e₃ := by linarith
  have hq₀ : 0 ≤ (e₂ - e₃) / (e₁ - e₃) := div_nonneg (by linarith) hc.le
  have hq₁ : (e₂ - e₃) / (e₁ - e₃) < 1 := (div_lt_one hc).2 (by linarith)
  have hk : √((e₂ - e₃) / (e₁ - e₃)) ^ 2 = (e₂ - e₃) / (e₁ - e₃) := sq_sqrt hq₀
  have hK := ofReal_legendreK_eq_lintegral_algebraic (k := √((e₂ - e₃) / (e₁ - e₃)))
    (by rwa [hk])
  rw [hk] at hK
  have hp : ∀ t ∈ Ioo (0 : ℝ) 1,
      0 ≤ (1 - t ^ 2) * (1 - (e₂ - e₃) / (e₁ - e₃) * t ^ 2) := fun t ht ↦ by
    have ht' : t ^ 2 < 1 := by nlinarith [ht.1, ht.2]
    have hqt : (e₂ - e₃) / (e₁ - e₃) * t ^ 2 < 1 :=
      (mul_le_of_le_one_right hq₀ ht'.le).trans_lt hq₁
    exact mul_nonneg (by linarith) (by linarith)
  rw [← himage, lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioo hf' hf,
    setLIntegral_congr_fun measurableSet_Ioo fun t ht ↦ ofReal_abs_mul_ofReal_inv_sqrt
      (hf'0 t ht) hc (hp t ht) (hD t ht),
    lintegral_ofReal_inv_sqrt_mul, ← hK, ← ENNReal.ofReal_mul (inv_nonneg.2 (sqrt_nonneg _)),
    inv_mul_eq_div]

/-- **The integral over `(e₁, ∞)` for a cubic with three real roots.** For `e₃ ≤ e₂ < e₁`,
`∫_{(e₁, ∞)} (4(x - e₁)(x - e₂)(x - e₃))^(-1/2) dx = K(k) / √(e₁ - e₃)` with
`k = √((e₂ - e₃)/(e₁ - e₃))`. In particular the integral converges. -/
theorem lintegral_Ioi_inv_sqrt_cubic_eq_legendreK {e₁ e₂ e₃ : ℝ} (h₃₂ : e₃ ≤ e₂)
    (h₂₁ : e₂ < e₁) :
    ∫⁻ x in Ioi e₁, ENNReal.ofReal (√(4 * (x - e₁) * (x - e₂) * (x - e₃)))⁻¹ =
      ENNReal.ofReal (legendreK √((e₂ - e₃) / (e₁ - e₃)) / √(e₁ - e₃)) := by
  have hc : 0 < e₁ - e₃ := by linarith
  refine lintegral_eq_legendreK_of_subst h₃₂ h₂₁ (f := fun t ↦ e₃ + (e₁ - e₃) / t ^ 2)
    (f' := fun t ↦ -(2 * (e₁ - e₃) / t ^ 3)) ?_ (fun t ht ↦ ?_) ?_
    (fun t ht ↦ neg_ne_zero.2 (by have := ht.1; positivity)) fun t ht ↦ ?_
  · ext x
    refine ⟨?_, fun hx ↦ ?_⟩
    · rintro ⟨t, ⟨ht₀, ht₁⟩, rfl⟩
      have ht : t ^ 2 < 1 := by nlinarith
      dsimp only
      rw [mem_Ioi, ← sub_lt_iff_lt_add', lt_div_iff₀ (by positivity)]
      nlinarith
    · have hx₃ : 0 < x - e₃ := by rw [mem_Ioi] at hx; linarith
      refine ⟨√((e₁ - e₃) / (x - e₃)), ⟨sqrt_pos.2 (div_pos hc hx₃), ?_⟩, ?_⟩
      · rw [sqrt_lt' one_pos, one_pow, div_lt_one hx₃]
        rw [mem_Ioi] at hx
        linarith
      · simp only
        rw [sq_sqrt (div_pos hc hx₃).le]
        field_simp
        ring
  · have h := (HasDerivAt.div (hasDerivAt_const t (e₁ - e₃)) (hasDerivAt_pow 2 t)
      (pow_ne_zero 2 ht.1.ne')).const_add e₃
    have ht₀ := ht.1.ne'
    convert h.hasDerivWithinAt using 1
    field_simp
    ring
  · intro s hs t ht hst
    have hs₀ := hs.1
    have ht₀ := ht.1
    simp only [add_right_inj] at hst
    rw [div_eq_div_iff (by positivity) (by positivity)] at hst
    exact (pow_left_inj₀ hs₀.le ht₀.le two_ne_zero).1 (by nlinarith)
  · have ht₀ := ht.1
    field_simp
    ring

/-- **The integral over `(e₃, e₂)` for a cubic with three real roots.** For `e₃ < e₂ < e₁`,
`∫_{(e₃, e₂)} (4(x - e₁)(x - e₂)(x - e₃))^(-1/2) dx = K(k) / √(e₁ - e₃)` with
`k = √((e₂ - e₃)/(e₁ - e₃))`. In particular the integral converges. -/
theorem lintegral_Ioo_inv_sqrt_cubic_eq_legendreK {e₁ e₂ e₃ : ℝ} (h₃₂ : e₃ < e₂)
    (h₂₁ : e₂ < e₁) :
    ∫⁻ x in Ioo e₃ e₂, ENNReal.ofReal (√(4 * (x - e₁) * (x - e₂) * (x - e₃)))⁻¹ =
      ENNReal.ofReal (legendreK √((e₂ - e₃) / (e₁ - e₃)) / √(e₁ - e₃)) := by
  have hc : 0 < e₂ - e₃ := by linarith
  refine lintegral_eq_legendreK_of_subst h₃₂.le h₂₁ (f := fun t ↦ e₃ + (e₂ - e₃) * t ^ 2)
    (f' := fun t ↦ 2 * (e₂ - e₃) * t) ?_ (fun t ht ↦ ?_) ?_
    (fun t ht ↦ by have := ht.1; positivity) fun t ht ↦ ?_
  · ext x
    refine ⟨?_, fun hx ↦ ?_⟩
    · rintro ⟨t, ⟨ht₀, ht₁⟩, rfl⟩
      have ht : t ^ 2 < 1 := by nlinarith
      dsimp only
      exact ⟨by nlinarith [mul_pos hc (pow_pos ht₀ 2)], by nlinarith⟩
    · have hx₃ : 0 < x - e₃ := by linarith [hx.1]
      refine ⟨√((x - e₃) / (e₂ - e₃)), ⟨sqrt_pos.2 (div_pos hx₃ hc), ?_⟩, ?_⟩
      · rw [sqrt_lt' one_pos, one_pow, div_lt_one hc]
        linarith [hx.2]
      · simp only
        rw [sq_sqrt (div_pos hx₃ hc).le]
        field_simp
        ring
  · have h := ((hasDerivAt_pow 2 t).const_mul (e₂ - e₃)).const_add e₃
    convert h.hasDerivWithinAt using 1
    ring
  · intro s hs t ht hst
    simp only [add_right_inj, mul_right_inj' hc.ne'] at hst
    exact (pow_left_inj₀ hs.1.le ht.1.le two_ne_zero).1 hst
  · have hc₁ : e₁ - e₃ ≠ 0 := by linarith
    field_simp
    ring

/-- On `(0, π)`, both `1 - cos θ` and `1 + cos θ` are positive. -/
private lemma one_sub_cos_pos_and_one_add_cos_pos {θ : ℝ} (hθ : θ ∈ Ioo 0 π) :
    0 < 1 - cos θ ∧ 0 < 1 + cos θ := by
  have h₁ := cos_lt_cos_of_nonneg_of_le_pi le_rfl hθ.2.le hθ.1
  have h₂ := cos_lt_cos_of_nonneg_of_le_pi hθ.1.le le_rfl hθ.2
  rw [cos_zero] at h₁
  rw [cos_pi] at h₂
  constructor <;> linarith

/-- For `A > 0`, the substitution `x = e + A (1 - cos θ)/(1 + cos θ)` maps `(0, π)` onto
`(e, ∞)`. -/
private lemma image_Ioo_zero_pi_cos_subst {e A : ℝ} (hA : 0 < A) :
    (fun θ ↦ e + A * ((1 - cos θ) / (1 + cos θ))) '' Ioo 0 π = Ioi e := by
  ext x
  refine ⟨?_, fun hx ↦ ?_⟩
  · rintro ⟨θ, hθ, rfl⟩
    have h := one_sub_cos_pos_and_one_add_cos_pos hθ
    simp only [mem_Ioi, lt_add_iff_pos_right]
    exact mul_pos hA (div_pos h.1 h.2)
  · -- The preimage is `θ = arccos ((A - u)/(A + u))` with `u = x - e > 0`.
    have hu : 0 < x - e := sub_pos.2 hx
    have hy₁ : (A - (x - e)) / (A + (x - e)) < 1 := (div_lt_one (by linarith)).2 (by linarith)
    have hy₂ : -1 < (A - (x - e)) / (A + (x - e)) := by
      rw [lt_div_iff₀ (by linarith)]
      linarith
    refine ⟨arccos ((A - (x - e)) / (A + (x - e))), ⟨arccos_pos.2 hy₁, arccos_lt_pi.2 hy₂⟩, ?_⟩
    have : A + (x - e) ≠ 0 := by linarith
    simp only
    rw [cos_arccos hy₂.le hy₁.le]
    field_simp
    rw [show A + (x - e) - (A - (x - e)) = 2 * (x - e) by ring,
      show A + (x - e) + (A - (x - e)) = 2 * A by ring]
    field_simp
    ring

/-- For `A ≠ 0`, the substitution `x = e + A (1 - cos θ)/(1 + cos θ)` is injective on `(0, π)`. -/
private lemma injOn_cos_subst {e A : ℝ} (hA : A ≠ 0) :
    InjOn (fun θ ↦ e + A * ((1 - cos θ) / (1 + cos θ))) (Ioo 0 π) := by
  intro s hs t ht hst
  have h₁ := one_sub_cos_pos_and_one_add_cos_pos hs
  have h₂ := one_sub_cos_pos_and_one_add_cos_pos ht
  simp only [add_right_inj, mul_right_inj' hA] at hst
  rw [div_eq_div_iff h₁.2.ne' h₂.2.ne'] at hst
  exact injOn_cos (Ioo_subset_Icc_self hs) (Ioo_subset_Icc_self ht) (by linarith)

/-- For `k ^ 2 < 1`, the Lebesgue integral of the integrand of the first kind over `(0, π)` is
`F(π, k) = 2 K(k)`. -/
private lemma lintegral_Ioo_zero_pi_legendreF_integrand {k : ℝ} (hk : k ^ 2 < 1) :
    ∫⁻ θ in Ioo 0 π, ENNReal.ofReal ((1 - k ^ 2 * sin θ ^ 2) ^ (-1 / 2 : ℝ)) =
      ENNReal.ofReal (2 * legendreK k) := by
  have h2 : 2 * legendreK k = legendreF π k := by
    simpa [legendreF_zero] using (legendreF_add_pi hk 0).symm
  rw [h2, legendreF_def, intervalIntegral.integral_of_le pi_pos.le, integral_Ioc_eq_integral_Ioo,
    ofReal_integral_eq_lintegral_ofReal
      ((continuous_legendreF_integrand hk).integrableOn_Icc.mono_set Ioo_subset_Icc_self)
      (ae_of_all _ fun θ ↦ zero_le_one.trans (one_le_legendreF_integrand hk θ))]

/-- **The integral over `(e₁, ∞)` for a cubic with one real root.** For `b ≠ 0`, put
`A = √((e₁ - a)² + b²)` and `k = √((A + a - e₁)/(2A))`. Then
`∫_{(e₁, ∞)} (4(x - e₁)((x - a)² + b²))^(-1/2) dx = K(k) / √A`. In particular the integral
converges. The formula also holds for `b = 0` when the double root `a` lies below `e₁`; then
`A = e₁ - a` and `k = 0`. -/
theorem lintegral_Ioi_inv_sqrt_mul_sq_add_sq_eq_legendreK {e₁ a b : ℝ} (hb : b ≠ 0 ∨ a < e₁) :
    ∫⁻ x in Ioi e₁, ENNReal.ofReal (√(4 * (x - e₁) * ((x - a) ^ 2 + b ^ 2)))⁻¹ =
      ENNReal.ofReal (legendreK √((√((e₁ - a) ^ 2 + b ^ 2) + a - e₁) /
        (2 * √((e₁ - a) ^ 2 + b ^ 2))) / √(√((e₁ - a) ^ 2 + b ^ 2))) := by
  have hpos : 0 < (e₁ - a) ^ 2 + b ^ 2 := by
    rcases hb with hb | hb
    · positivity
    · have : e₁ - a ≠ 0 := by linarith
      positivity
  set A := √((e₁ - a) ^ 2 + b ^ 2)
  have hA2 : A ^ 2 = (e₁ - a) ^ 2 + b ^ 2 := sq_sqrt hpos.le
  have hA : 0 < A := sqrt_pos.2 hpos
  clear_value A
  -- The modulus: `0 ≤ k² < 1` because `e₁ - a ≤ A` and `a - e₁ < A`.
  set q := (A + a - e₁) / (2 * A)
  have hpA₁ : e₁ - a ≤ A :=
    (le_abs_self _).trans (abs_le_of_sq_le_sq (by nlinarith) hA.le)
  have hpA₂ : a - e₁ < A := by
    rcases hb with hb | hb
    · have hb2 : 0 < b ^ 2 := by positivity
      have : |e₁ - a| < A := abs_lt_of_sq_lt_sq (by linarith) hA.le
      linarith [neg_abs_le (e₁ - a)]
    · linarith
  have hq₀ : 0 ≤ q := div_nonneg (by linarith) (by positivity)
  have hq₁ : q < 1 := (div_lt_one (by positivity)).2 (by linarith)
  have hk : √q ^ 2 = q := sq_sqrt hq₀
  have hF := lintegral_Ioo_zero_pi_legendreF_integrand (k := √q) (by rwa [hk])
  rw [hk] at hF
  -- The substitution `x = e₁ + A (1 - cos θ)/(1 + cos θ)` and its derivative.
  set f : ℝ → ℝ := fun θ ↦ e₁ + A * ((1 - cos θ) / (1 + cos θ))
  set f' : ℝ → ℝ := fun θ ↦ A * (2 * sin θ / (1 + cos θ) ^ 2)
  have hderiv : ∀ θ ∈ Ioo 0 π, HasDerivWithinAt f (f' θ) (Ioo 0 π) θ := fun θ hθ ↦ by
    have hc := (one_sub_cos_pos_and_one_add_cos_pos hθ).2.ne'
    have h := ((((hasDerivAt_cos θ).const_sub 1).div ((hasDerivAt_cos θ).const_add 1)
      hc).const_mul A).const_add e₁
    convert h.hasDerivWithinAt using 1
    simp only [f']
    field_simp
    ring
  have hf'0 : ∀ θ ∈ Ioo 0 π, f' θ ≠ 0 := fun θ hθ ↦
    mul_ne_zero hA.ne' (div_ne_zero (mul_ne_zero two_ne_zero
      (sin_pos_of_pos_of_lt_pi hθ.1 hθ.2).ne')
      (pow_ne_zero 2 (one_sub_cos_pos_and_one_add_cos_pos hθ).2.ne'))
  -- The cubic at the substituted point, using `sin² θ = 1 - cos² θ` and `b² = A² - (e₁ - a)²`.
  have hD : ∀ θ ∈ Ioo 0 π, 4 * (f θ - e₁) * ((f θ - a) ^ 2 + b ^ 2) =
      f' θ ^ 2 * (4 * A) * (1 - q * sin θ ^ 2) := fun θ hθ ↦ by
    have hc := (one_sub_cos_pos_and_one_add_cos_pos hθ).2.ne'
    have hb2 : b ^ 2 = A ^ 2 - (e₁ - a) ^ 2 := by rw [hA2]; ring
    simp only [f, f', q, mul_pow, div_pow, sin_sq, hb2]
    field_simp
    ring
  have hp : ∀ θ ∈ Ioo 0 π, 0 ≤ 1 - q * sin θ ^ 2 := fun θ _ ↦ by
    nlinarith [mul_le_of_le_one_right hq₀ (sin_sq_le_one θ)]
  rw [← image_Ioo_zero_pi_cos_subst hA,
    lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioo hderiv (injOn_cos_subst hA.ne'),
    setLIntegral_congr_fun measurableSet_Ioo fun θ hθ ↦ ofReal_abs_mul_ofReal_inv_sqrt
      (hf'0 θ hθ) (by positivity) (hp θ hθ) (hD θ hθ),
    lintegral_ofReal_inv_sqrt_mul, hF, ← ENNReal.ofReal_mul (inv_nonneg.2 (sqrt_nonneg _)),
    sqrt_mul zero_le_four, show (4 : ℝ) = 2 ^ 2 by norm_num, sqrt_sq zero_le_two]
  congr 1
  field_simp

end TauCeti.Real
