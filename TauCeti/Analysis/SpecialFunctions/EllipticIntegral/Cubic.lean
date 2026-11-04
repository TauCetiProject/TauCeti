/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.EllipticIntegral.Gauss
import TauCeti.Analysis.Calculus.RealCharts

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

* `TauCeti.Real.setOf_cubic_pos`: for `e₃ < e₂ < e₁`, `D` is positive exactly on
  `(e₃, e₂) ∪ (e₁, ∞)`.
* `TauCeti.Real.lintegral_Ioi_inv_sqrt_cubic_eq_agmIntegral` and
  `TauCeti.Real.lintegral_Ioo_inv_sqrt_cubic_eq_agmIntegral`: both integrals equal the AGM
  integral of the axes `√(e₁ - e₂)` and `√(e₁ - e₃)`.
* `TauCeti.Real.lintegral_Ioi_inv_sqrt_cubic_eq_legendreK` and
  `TauCeti.Real.lintegral_Ioo_inv_sqrt_cubic_eq_legendreK`: both integrals equal
  `K(k) / √(e₁ - e₃)`, via `TauCeti.Real.agmIntegral_sqrt_sub_eq_legendreK`.

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

variable {e₁ e₂ e₃ : ℝ}

/-- For `e₃ < e₂ < e₁`, the cubic `4 (x - e₁)(x - e₂)(x - e₃)` is positive exactly on
`(e₃, e₂) ∪ (e₁, ∞)`. -/
theorem setOf_cubic_pos (h₃₂ : e₃ < e₂) (h₂₁ : e₂ < e₁) :
    {x : ℝ | 0 < 4 * (x - e₁) * (x - e₂) * (x - e₃)} = Ioo e₃ e₂ ∪ Ioi e₁ := by
  ext x
  simp only [mem_ofPred_eq, mem_union, mem_Ioo, mem_Ioi]
  constructor
  · intro h
    by_contra hc
    rcases le_or_gt x e₃ with h3 | h3
    · have : 0 < (x - e₁) * (x - e₂) := mul_pos_of_neg_of_neg (by linarith) (by linarith)
      nlinarith
    · have h2 : e₂ ≤ x := le_of_not_gt fun h2 ↦ hc (Or.inl ⟨h3, h2⟩)
      have h1 : x ≤ e₁ := le_of_not_gt fun h1 ↦ hc (Or.inr h1)
      have : 0 ≤ (x - e₂) * (x - e₃) := mul_nonneg (by linarith) (by linarith)
      nlinarith
  · rintro (⟨h3, h2⟩ | h1)
    · have : 0 < (x - e₁) * (x - e₂) := mul_pos_of_neg_of_neg (by linarith) (by linarith)
      nlinarith
    · have : 0 < (x - e₁) * (x - e₂) := mul_pos (by linarith) (by linarith)
      nlinarith

/-- **The cubic integral over `(e₁, ∞)` is an AGM integral.** For `e₂, e₃ < e₁`,
`∫_{(e₁, ∞)} (4 (x - e₁)(x - e₂)(x - e₃))^(-1/2) dx` is the AGM integral of the axes
`√(e₁ - e₂)` and `√(e₁ - e₃)`. -/
theorem lintegral_Ioi_inv_sqrt_cubic_eq_agmIntegral (h₂ : e₂ < e₁) (h₃ : e₃ < e₁) :
    ∫⁻ x in Ioi e₁, ENNReal.ofReal (√(4 * (x - e₁) * (x - e₂) * (x - e₃)))⁻¹ =
      ENNReal.ofReal (agmIntegral √(e₁ - e₂) √(e₁ - e₃)) := by
  have himage : (fun t : ℝ ↦ e₁ + t ^ 2) '' Ioi 0 = Ioi e₁ := by
    have hsq := image_sq_div_const_Ioi one_pos (y := 0) le_rfl
    simp only [div_one, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at hsq
    have h := image_image (e₁ + ·) (· ^ 2) (Ioi (0 : ℝ))
    rwa [hsq, image_const_add_Ioi, add_zero, eq_comm] at h
  rw [← himage]
  refine lintegral_image_inv_sqrt_eq_agmIntegral (f' := fun t ↦ 2 * t)
    (sqrt_pos.2 (sub_pos.2 h₂)) (sqrt_pos.2 (sub_pos.2 h₃))
    (fun t _ ↦ ?_) (fun s hs t ht hst ↦ ?_) (fun t ht ↦ by positivity [mem_Ioi.1 ht])
    (fun t _ ↦ ?_)
  · simpa using ((hasDerivAt_pow 2 t).const_add e₁).hasDerivWithinAt
  · exact (sq_eq_sq₀ (le_of_lt hs) (le_of_lt ht)).1 (by simpa using hst)
  · rw [sq_sqrt (sub_pos.2 h₂).le, sq_sqrt (sub_pos.2 h₃).le]
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
  have himage := image_add_mul_div_sq_add_Ioi (c := e₃) hp hq
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
theorem agmIntegral_sqrt_sub_eq_legendreK (h₃₂ : e₃ ≤ e₂) (h₂₁ : e₂ < e₁) :
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
