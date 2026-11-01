/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.EllipticIntegral.Gauss
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# Integrals of the inverse square root of a real cubic with three real roots

Let `e₃ < e₂ < e₁` be real and `D(x) = 4 (x - e₁) (x - e₂) (x - e₃)`. The cubic `D` is positive
exactly on `(e₃, e₂)` and on `(e₁, ∞)`, and on each of these intervals the integral of
`D(x)^(-1/2)` is the same complete elliptic integral of the first kind:

  `∫_{(e₁, ∞)} D(x)^(-1/2) dx = ∫_{(e₃, e₂)} D(x)^(-1/2) dx = K(k) / √(e₁ - e₃)`,

with modulus `k = √((e₂ - e₃) / (e₁ - e₃))`. Each is half the integral of `|dx / y|` over one of
the two components of the real points of the curve `y² = D(x)`, and together they evaluate the
real period of a Weierstrass curve over `ℝ` whose `2`-torsion polynomial has three real roots.

Both integrals are stated as Lebesgue integrals of `ENNReal.ofReal (√(D x))⁻¹`, so that the
finiteness of the left side is part of the statement.

The proof reduces both integrals to `TauCeti.agmIntegral √(e₁ - e₂) √(e₁ - e₃)`. On `(e₁, ∞)` the
substitution is `x = e₁ + t²`; on `(e₃, e₂)` it is `x = e₃ + (e₁ - e₃) (e₂ - e₃) / (t² + e₁ - e₃)`,
the composite of `u = e₁ + t²` with the Möbius involution `u ↦ e₃ + (e₁ - e₃) (e₂ - e₃) / (u - e₃)`,
which exchanges `e₁` with `e₂` and `e₃` with `∞`.
In both cases `D(x(t)) = x′(t)² (t² + e₁ - e₂) (t² + e₁ - e₃)`. Gauss's theorem then identifies
the AGM integral with `K(k) / √(e₁ - e₃)`.

## Main results

* `TauCeti.Real.lintegral_Ioi_inv_sqrt_cubic_eq_agmIntegral` and
  `TauCeti.Real.lintegral_Ioo_inv_sqrt_cubic_eq_agmIntegral`: both integrals equal the AGM
  integral of the axes `√(e₁ - e₂)` and `√(e₁ - e₃)`.
* `TauCeti.Real.lintegral_Ioi_inv_sqrt_cubic_eq_legendreK` and
  `TauCeti.Real.lintegral_Ioo_inv_sqrt_cubic_eq_legendreK`: both integrals equal
  `K(k) / √(e₁ - e₃)`.

## References

* P. F. Byrd and M. D. Friedman, *Handbook of Elliptic Integrals for Engineers and Scientists*,
  2nd ed., Springer, 1971, formulas 236.00 and 239.00.
* NIST *Digital Library of Mathematical Functions*, §19.29, <https://dlmf.nist.gov/19.29>.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace TauCeti.Real

open _root_.Real

/-- If a substitution `x = f(t)` on `t > 0` satisfies `D(f t) = f′(t)² (t² + a²)(t² + b²)` with
`f′(t) ≠ 0`, then the integral of `D(x)^(-1/2)` over the image of `f` is the AGM integral
of the axes `a` and `b`. -/
private theorem lintegral_image_inv_sqrt_eq_agmIntegral {f f' D : ℝ → ℝ} {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hf : ∀ t ∈ Ioi (0 : ℝ), HasDerivWithinAt f (f' t) (Ioi 0) t)
    (hinj : InjOn f (Ioi 0)) (hf' : ∀ t ∈ Ioi (0 : ℝ), f' t ≠ 0)
    (hD : ∀ t ∈ Ioi (0 : ℝ), D (f t) = f' t ^ 2 * ((t ^ 2 + a ^ 2) * (t ^ 2 + b ^ 2))) :
    ∫⁻ x in f '' Ioi 0, ENNReal.ofReal (√(D x))⁻¹ = ENNReal.ofReal (agmIntegral a b) := by
  rw [lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi hf hinj, agmIntegral_def,
    ofReal_integral_eq_lintegral_ofReal (integrableOn_agmIntegrand_Ioi_of_pos ha hb)
      (Filter.Eventually.of_forall fun _ ↦ by positivity)]
  refine setLIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
  have habs : 0 < |f' t| := abs_pos.2 (hf' t ht)
  rw [← ENNReal.ofReal_mul habs.le, hD t ht, sqrt_mul (sq_nonneg _), sqrt_sq_eq_abs]
  congr 1
  field_simp

variable {e₁ e₂ e₃ : ℝ}

/-- **The cubic integral over `(e₁, ∞)` is an AGM integral.** For `e₂, e₃ < e₁`,
`∫_{(e₁, ∞)} (4 (x - e₁)(x - e₂)(x - e₃))^(-1/2) dx` is the AGM integral of the axes
`√(e₁ - e₂)` and `√(e₁ - e₃)`. -/
theorem lintegral_Ioi_inv_sqrt_cubic_eq_agmIntegral (h₂ : e₂ < e₁) (h₃ : e₃ < e₁) :
    ∫⁻ x in Ioi e₁, ENNReal.ofReal (√(4 * (x - e₁) * (x - e₂) * (x - e₃)))⁻¹ =
      ENNReal.ofReal (agmIntegral √(e₁ - e₂) √(e₁ - e₃)) := by
  have himage : (fun t : ℝ ↦ e₁ + t ^ 2) '' Ioi 0 = Ioi e₁ := by
    ext x
    refine ⟨fun ⟨t, ht, hx⟩ ↦ ?_, fun hx ↦ ?_⟩
    · rw [← hx, mem_Ioi]
      have : 0 < t ^ 2 := pow_pos ht 2
      linarith
    · have hx : 0 < x - e₁ := sub_pos.2 hx
      exact ⟨√(x - e₁), sqrt_pos.2 hx, by simp only [sq_sqrt hx.le]; ring⟩
  rw [← himage]
  refine lintegral_image_inv_sqrt_eq_agmIntegral (f' := fun t ↦ 2 * t)
    (sqrt_pos.2 (sub_pos.2 h₂)) (sqrt_pos.2 (sub_pos.2 h₃))
    (fun t _ ↦ ?_) (fun s hs t ht hst ↦ ?_) (fun t ht ↦ by positivity [mem_Ioi.1 ht])
    (fun t _ ↦ ?_)
  · simpa using ((hasDerivAt_pow 2 t).const_add e₁).hasDerivWithinAt
  · exact (sq_eq_sq₀ (le_of_lt hs) (le_of_lt ht)).1 (by simpa using hst)
  · rw [sq_sqrt (sub_pos.2 h₂).le, sq_sqrt (sub_pos.2 h₃).le]
    ring

/-- For `0 < q < p`, the map `t ↦ c + p q / (t² + p)` sends `(0, ∞)` onto `(c, c + q)`. -/
private theorem image_add_mul_div_sq_add_Ioi {c p q : ℝ} (hq : 0 < q) (hqp : q < p) :
    (fun t : ℝ ↦ c + p * q / (t ^ 2 + p)) '' Ioi 0 = Ioo c (c + q) := by
  have hp : 0 < p := hq.trans hqp
  ext x
  refine ⟨fun ⟨t, ht, hx⟩ ↦ ?_, fun ⟨hxc, hxq⟩ ↦ ?_⟩
  · have ht2 : 0 < t ^ 2 := pow_pos ht 2
    have hlt : p * q / (t ^ 2 + p) < q := by
      rw [div_lt_iff₀ (by positivity)]
      nlinarith
    rw [← hx]
    exact ⟨by linarith [show 0 < p * q / (t ^ 2 + p) by positivity], by linarith⟩
  · have hx : 0 < x - c := sub_pos.2 hxc
    have hlt : p < p * q / (x - c) := by
      rw [lt_div_iff₀ hx]
      nlinarith
    refine ⟨√(p * q / (x - c) - p), sqrt_pos.2 (by linarith), ?_⟩
    simp only [sq_sqrt (by linarith : 0 ≤ p * q / (x - c) - p), sub_add_cancel]
    field_simp
    ring

/-- **The cubic integral over `(e₃, e₂)` is an AGM integral.** For `e₃ < e₂ < e₁`,
`∫_{(e₃, e₂)} (4 (x - e₁)(x - e₂)(x - e₃))^(-1/2) dx` is the AGM integral of the axes
`√(e₁ - e₂)` and `√(e₁ - e₃)`. -/
theorem lintegral_Ioo_inv_sqrt_cubic_eq_agmIntegral (h₃₂ : e₃ < e₂) (h₂₁ : e₂ < e₁) :
    ∫⁻ x in Ioo e₃ e₂, ENNReal.ofReal (√(4 * (x - e₁) * (x - e₂) * (x - e₃)))⁻¹ =
      ENNReal.ofReal (agmIntegral √(e₁ - e₂) √(e₁ - e₃)) := by
  -- Write `p = e₁ - e₃` and `q = e₂ - e₃`; the substitution is `x = e₃ + p q / (t² + p)`.
  set p := e₁ - e₃
  set q := e₂ - e₃
  have hp : 0 < p := by linarith
  have hq : 0 < q := by linarith
  have hne (u : ℝ) : u ^ 2 + p ≠ 0 := by positivity
  have himage := image_add_mul_div_sq_add_Ioi (c := e₃) hq (by linarith : q < p)
  rw [add_sub_cancel] at himage
  rw [← himage]
  refine lintegral_image_inv_sqrt_eq_agmIntegral
    (f' := fun t ↦ -(2 * t * p * q) / (t ^ 2 + p) ^ 2)
    (sqrt_pos.2 (sub_pos.2 h₂₁)) (sqrt_pos.2 hp)
    (fun t _ ↦ ?_) (fun s hs t ht hst ↦ ?_) (fun t ht ↦ ?_) (fun t _ ↦ ?_)
  · refine HasDerivAt.hasDerivWithinAt ?_
    convert (((hasDerivAt_pow 2 t).add_const p).inv (hne t)).const_mul (p * q) |>.const_add e₃
      using 1
    · ext s
      simp [div_eq_mul_inv]
    · field_simp
      ring
  · have h := (add_right_injective e₃) hst
    simp only [div_eq_div_iff (hne s) (hne t)] at h
    refine (sq_eq_sq₀ (mem_Ioi.1 hs).le (mem_Ioi.1 ht).le).1 ?_
    nlinarith [mul_pos hp hq]
  · have : 0 < 2 * t * p * q / (t ^ 2 + p) ^ 2 := by positivity [mem_Ioi.1 ht]
    rw [neg_div]
    exact neg_ne_zero.2 this.ne'
  · have := hne t
    rw [sq_sqrt (sub_pos.2 h₂₁).le, sq_sqrt hp.le]
    field_simp
    ring

/-- The AGM integral of the axes `√(e₁ - e₂)` and `√(e₁ - e₃)` is `K(k) / √(e₁ - e₃)`, where
`k = √((e₂ - e₃) / (e₁ - e₃))`. -/
private theorem agmIntegral_sqrt_sub_eq_legendreK (h₃₂ : e₃ ≤ e₂) (h₂₁ : e₂ < e₁) :
    agmIntegral √(e₁ - e₂) √(e₁ - e₃) =
      legendreK √((e₂ - e₃) / (e₁ - e₃)) / √(e₁ - e₃) := by
  rw [agmIntegral_eq_legendreK_div (sqrt_pos.2 (sub_pos.2 h₂₁)) (sqrt_le_sqrt (by linarith)),
    div_pow, sq_sqrt (by linarith), sq_sqrt (by linarith)]
  congr 3
  field_simp [show e₁ - e₃ ≠ 0 by linarith]
  ring

/-- **The cubic integral over `(e₁, ∞)`.** For `e₃ ≤ e₂ < e₁`,
`∫_{(e₁, ∞)} (4 (x - e₁)(x - e₂)(x - e₃))^(-1/2) dx = K(k) / √(e₁ - e₃)`, where
`k = √((e₂ - e₃) / (e₁ - e₃))`. -/
theorem lintegral_Ioi_inv_sqrt_cubic_eq_legendreK (h₃₂ : e₃ ≤ e₂) (h₂₁ : e₂ < e₁) :
    ∫⁻ x in Ioi e₁, ENNReal.ofReal (√(4 * (x - e₁) * (x - e₂) * (x - e₃)))⁻¹ =
      ENNReal.ofReal (legendreK √((e₂ - e₃) / (e₁ - e₃)) / √(e₁ - e₃)) := by
  rw [lintegral_Ioi_inv_sqrt_cubic_eq_agmIntegral h₂₁ (h₃₂.trans_lt h₂₁),
    agmIntegral_sqrt_sub_eq_legendreK h₃₂ h₂₁]

/-- **The cubic integral over `(e₃, e₂)`.** For `e₃ < e₂ < e₁`,
`∫_{(e₃, e₂)} (4 (x - e₁)(x - e₂)(x - e₃))^(-1/2) dx = K(k) / √(e₁ - e₃)`, where
`k = √((e₂ - e₃) / (e₁ - e₃))`. -/
theorem lintegral_Ioo_inv_sqrt_cubic_eq_legendreK (h₃₂ : e₃ < e₂) (h₂₁ : e₂ < e₁) :
    ∫⁻ x in Ioo e₃ e₂, ENNReal.ofReal (√(4 * (x - e₁) * (x - e₂) * (x - e₃)))⁻¹ =
      ENNReal.ofReal (legendreK √((e₂ - e₃) / (e₁ - e₃)) / √(e₁ - e₃)) := by
  rw [lintegral_Ioo_inv_sqrt_cubic_eq_agmIntegral h₃₂ h₂₁,
    agmIntegral_sqrt_sub_eq_legendreK h₃₂.le h₂₁]

end TauCeti.Real
