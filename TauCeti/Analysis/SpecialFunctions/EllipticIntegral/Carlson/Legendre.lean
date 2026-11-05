/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.EllipticIntegral.Carlson.Basic
public import TauCeti.Analysis.SpecialFunctions.EllipticIntegral.Carlson.RJ
public import TauCeti.Analysis.SpecialFunctions.EllipticIntegral.Legendre
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import TauCeti.Algebra.Order.Group.EvenFunction
import TauCeti.Analysis.SpecialFunctions.Trigonometric.Arcsin
import TauCeti.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Legendre's integrals in Carlson's symmetric form

Every Legendre integral is a combination of Carlson's symmetric integrals (DLMF 19.25.5, 19.25.7,
19.25.14). For `|φ| ≤ π / 2`, write `s = sin φ`, `c = cos² φ` and `Δ = 1 - k² sin² φ`. Then

* `F(φ, k) = s R_F(c, Δ, 1)`;
* `E(φ, k) = s R_F(c, Δ, 1) - (k² / 3) s³ R_D(c, Δ, 1)`;
* `Π(φ, k, α²) = s R_F(c, Δ, 1) + (α² / 3) s³ R_J(c, Δ, 1, 1 - α² s²)`;

and at `φ = π / 2` (DLMF 19.25.1, 19.25.2, and 19.25.7 at `φ = π / 2`)

* `K(k) = R_F(0, 1 - k², 1)`;
* `E(k) = R_F(0, 1 - k², 1) - (k² / 3) R_D(0, 1 - k², 1)`;
* `Π(k, α²) = R_F(0, 1 - k², 1) + (α² / 3) R_J(0, 1 - k², 1, 1 - α²)`.

The Carlson integrals are evaluated at real arguments coerced to `ℂ`, and each identity is an
equation in `ℂ` whose left side is the real Legendre integral; in particular the right side is
real. The incomplete identities hold under `k² sin² φ < 1` (and `α² sin² φ < 1` for the third
kind), which is `k ^ 2 < 1` (and `α2 < 1`) in the complete case.

The dictionary transfers statements about Carlson's symmetric integrals to Legendre's integrals,
and conversely.

## Main results

* `TauCeti.Real.ofReal_legendreF_eq_carlsonRF`,
  `TauCeti.Real.ofReal_legendreE_eq_carlsonRF_sub_carlsonRD`,
  `TauCeti.Real.ofReal_legendrePi_eq_carlsonRF_add_carlsonRJ`: the incomplete integrals;
* `TauCeti.Real.ofReal_legendreK_eq_carlsonRF`,
  `TauCeti.Real.ofReal_legendreEc_eq_carlsonRF_sub_carlsonRD`,
  `TauCeti.Real.ofReal_legendrePic_eq_carlsonRF_add_carlsonRJ`: the complete integrals.

## Implementation notes

The identities follow from the substitution `t = sin² φ / sin² θ - 1`, which maps `θ ∈ (0, φ)`
onto `t ∈ (0, ∞)` and turns the common factor `½ (t + c)^(-1/2) (t + Δ)^(-1/2) (t + 1)^(-1/2) dt`
of the three Carlson integrands into `(1 - k² sin² θ)^(-1/2) dθ / s`; under it,
`(t + 1)⁻¹ = sin² θ / s²` and `(t + 1 - α² s²)⁻¹ = sin² θ / (s² (1 - α² sin² θ))`.

## References

* NIST *Digital Library of Mathematical Functions*, §19.25(i), <https://dlmf.nist.gov/19.25.i>.
* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, Chapter 9.

B. Braams' `lean-codes` (<https://github.com/bjbraams/lean-codes>) proves these identities
(`Carlson.legendreF_eq_of_mul_lt` in `Carlson/Elliptic/Standard.lean`, and its companions in
`Carlson/Elliptic/LegendreStandard.lean` and `Carlson/Elliptic/LegendreThird.lean`) on top of
Carlson's general `R`-function; the statements here follow its form, with real Carlson arguments
coerced to `ℂ` and the hypothesis `k² sin² φ < 1`. The proofs here work directly from the integral
definitions of `TauCeti.Real.legendreF` and `Complex.carlsonRF` and are not ported from it.
-/

public section

namespace TauCeti.Real

open _root_.Real MeasureTheory Set
open Complex (carlsonRF carlsonRD carlsonRJ carlsonRF_def carlsonRD_def carlsonRJ_def ofReal_cpow
  ofReal_neg ofReal_one real_smul)

/-! ### The substitution `t = sin² φ / sin² θ - 1` -/

/-- **The substitution `t = sin² φ / sin² θ - 1`.** For `0 < φ ≤ π / 2` and `k² sin² φ < 1`, it
turns the common factor of Carlson's integrands at `(cos² φ, 1 - k² sin² φ, 1)` into the integrand
of `F(φ, k)` divided by `sin φ / 2`. A further factor `h t` becomes the real `g θ`, where
`h (sin² φ / sin² θ - 1) = g θ`. -/
private theorem integral_carlson_eq_integral_legendre {φ k : ℝ} (hφ0 : 0 < φ) (hφ : φ ≤ π / 2)
    (hk : k ^ 2 * sin φ ^ 2 < 1) {h : ℝ → ℂ} {g : ℝ → ℝ}
    (hg : ∀ θ ∈ Ioo 0 φ, h (sin φ ^ 2 / sin θ ^ 2 - 1) = g θ) :
    ∫ t in Ioi (0 : ℝ), ((t : ℂ) + ((cos φ ^ 2 : ℝ) : ℂ)) ^ (-(1 / 2) : ℂ) *
        ((t : ℂ) + ((1 - k ^ 2 * sin φ ^ 2 : ℝ) : ℂ)) ^ (-(1 / 2) : ℂ) *
        ((t : ℂ) + 1) ^ (-(1 / 2) : ℂ) * h t =
      ((2 / sin φ * ∫ θ in (0 : ℝ)..φ, (1 - k ^ 2 * sin θ ^ 2) ^ (-1 / 2 : ℝ) * g θ : ℝ) : ℂ) := by
  set s := sin φ with hs_def
  have hs : 0 < s := sin_pos_of_pos_of_lt_pi hφ0 (by linarith [pi_pos])
  have hderiv : ∀ θ ∈ Ioo 0 φ, HasDerivWithinAt (fun θ ↦ s ^ 2 / sin θ ^ 2 - 1)
      (-(2 * s ^ 2 * cos θ / sin θ ^ 3)) (Ioo 0 φ) θ := by
    intro θ ⟨hθ0, hθ⟩
    have hu : sin θ ≠ 0 := (sin_pos_of_pos_of_lt_pi hθ0 (by linarith [pi_pos])).ne'
    have h := ((hasDerivAt_const θ (s ^ 2)).div ((Real.hasDerivAt_sin θ).pow 2)
      (pow_ne_zero 2 hu)).sub_const 1
    convert h.hasDerivWithinAt using 1
    simp only [Pi.pow_apply]
    field_simp
    ring
  have hinj : InjOn (fun θ ↦ s ^ 2 / sin θ ^ 2 - 1) (Ioo 0 φ) := by
    intro θ₁ ⟨h₁0, h₁⟩ θ₂ ⟨h₂0, h₂⟩ heq
    have hu₁ : 0 < sin θ₁ := sin_pos_of_pos_of_lt_pi h₁0 (by linarith [pi_pos])
    have hu₂ : 0 < sin θ₂ := sin_pos_of_pos_of_lt_pi h₂0 (by linarith [pi_pos])
    have hsq : sin θ₁ ^ 2 = sin θ₂ ^ 2 := by
      simp only [sub_left_inj] at heq
      field_simp at heq
      nlinarith [heq]
    refine injOn_sin ⟨by linarith [pi_pos], by linarith⟩ ⟨by linarith [pi_pos], by linarith⟩ ?_
    exact (pow_left_inj₀ hu₁.le hu₂.le two_ne_zero).mp hsq
  rw [← image_sin_sq_div_sin_sq_sub_one_Ioo hφ0 hφ, ← hs_def,
    integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hderiv hinj,
    intervalIntegral.integral_of_le hφ0.le, integral_Ioc_eq_integral_Ioo, ← integral_const_mul,
    ← integral_complex_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioo fun θ ⟨hθ0, hθ⟩ ↦ ?_
  have hu : 0 < sin θ := sin_pos_of_pos_of_lt_pi hθ0 (by linarith [pi_pos])
  have hc : 0 < cos θ := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], by linarith⟩
  have hus : sin θ < s := sin_lt_sin_of_lt_of_le_pi_div_two (by linarith [pi_pos]) hφ hθ
  have hku : 0 < 1 - k ^ 2 * sin θ ^ 2 :=
    sub_pos.mpr (mul_sin_sq_lt_one_of_le hk hθ0.le hθ.le hφ)
  -- The three arguments of the square roots are perfect squares up to `1 - k² sin² θ`.
  have hA : s ^ 2 / sin θ ^ 2 - 1 + cos φ ^ 2 = (s * cos θ / sin θ) ^ 2 := by
    rw [cos_sq', ← hs_def, div_pow, mul_pow, cos_sq' θ]
    field_simp
    ring
  have hB : s ^ 2 / sin θ ^ 2 - 1 + (1 - k ^ 2 * s ^ 2) =
      (s / sin θ) ^ 2 * (1 - k ^ 2 * sin θ ^ 2) := by
    field_simp
    ring
  have hC : s ^ 2 / sin θ ^ 2 - 1 + 1 = (s / sin θ) ^ 2 := by ring
  have hpos : 0 < s / sin θ := div_pos hs hu
  -- At real arguments the principal powers are real inverse square roots.
  have ofReal_add_cpow_neg_half {t w : ℝ} (h : 0 < t + w) :
      ((t : ℂ) + (w : ℂ)) ^ (-(1 / 2) : ℂ) = (((√(t + w))⁻¹ : ℝ) : ℂ) := by
    rw [sqrt_eq_rpow, ← rpow_neg h.le, ofReal_cpow h.le]
    push_cast
    rfl
  have hAc := ofReal_add_cpow_neg_half (t := s ^ 2 / sin θ ^ 2 - 1) (w := cos φ ^ 2)
    (by rw [hA]; positivity)
  have hBc := ofReal_add_cpow_neg_half (t := s ^ 2 / sin θ ^ 2 - 1) (w := 1 - k ^ 2 * s ^ 2)
    (by rw [hB]; positivity)
  have hCc := ofReal_add_cpow_neg_half (t := s ^ 2 / sin θ ^ 2 - 1) (w := 1)
    (by rw [hC]; positivity)
  rw [ofReal_one] at hCc
  rw [hA, sqrt_sq (by positivity)] at hAc
  rw [hB, sqrt_mul (sq_nonneg _), sqrt_sq hpos.le] at hBc
  rw [hC, sqrt_sq hpos.le] at hCc
  rw [abs_neg, abs_of_pos (by positivity), real_smul, hAc, hBc, hCc, hg θ ⟨hθ0, hθ⟩,
    legendreF_integrand_eq_inv_sqrt]
  have hsq := sqrt_pos.mpr hku
  norm_cast
  field_simp

/-! ### Carlson's integrals at `(cos² φ, 1 - k² sin² φ, 1)` for `0 < φ ≤ π / 2` -/

private theorem carlsonRF_eq_of_pos {φ k : ℝ} (hφ0 : 0 < φ) (hφ : φ ≤ π / 2)
    (hk : k ^ 2 * sin φ ^ 2 < 1) :
    carlsonRF (cos φ ^ 2 : ℝ) (1 - k ^ 2 * sin φ ^ 2 : ℝ) 1 = (legendreF φ k / sin φ : ℝ) := by
  have h := integral_carlson_eq_integral_legendre (h := fun _ ↦ 1) (g := fun _ ↦ 1) hφ0 hφ hk
    fun _ _ ↦ ofReal_one.symm
  simp only [mul_one] at h
  rw [carlsonRF_def, h, legendreF_def]
  generalize (∫ θ in (0 : ℝ)..φ, (1 - k ^ 2 * sin θ ^ 2) ^ (-1 / 2 : ℝ)) = I
  push_cast
  ring

private theorem carlsonRD_eq_of_pos {φ k : ℝ} (hφ0 : 0 < φ) (hφ : φ ≤ π / 2)
    (hk : k ^ 2 * sin φ ^ 2 < 1) :
    carlsonRD (cos φ ^ 2 : ℝ) (1 - k ^ 2 * sin φ ^ 2 : ℝ) 1 = (3 / sin φ ^ 3 *
      ∫ θ in (0 : ℝ)..φ, (1 - k ^ 2 * sin θ ^ 2) ^ (-1 / 2 : ℝ) * sin θ ^ 2 : ℝ) := by
  -- Under the substitution, `(t + 1)⁻¹ = sin² θ / sin² φ`.
  have h := integral_carlson_eq_integral_legendre (h := fun t ↦ ((t : ℂ) + 1)⁻¹)
    (g := fun θ ↦ sin θ ^ 2 / sin φ ^ 2) hφ0 hφ hk fun θ _ ↦ by
      rw [← ofReal_one, ← Complex.ofReal_add, ← Complex.ofReal_inv, sub_add_cancel, inv_div]
  have hdiv : ∫ θ in (0 : ℝ)..φ, (1 - k ^ 2 * sin θ ^ 2) ^ (-1 / 2 : ℝ) * (sin θ ^ 2 / sin φ ^ 2) =
      (∫ θ in (0 : ℝ)..φ, (1 - k ^ 2 * sin θ ^ 2) ^ (-1 / 2 : ℝ) * sin θ ^ 2) / sin φ ^ 2 := by
    rw [← intervalIntegral.integral_div]
    simp only [mul_div_assoc]
  rw [carlsonRD_def, carlsonRJ_def, h, hdiv]
  generalize (∫ θ in (0 : ℝ)..φ, (1 - k ^ 2 * sin θ ^ 2) ^ (-1 / 2 : ℝ) * sin θ ^ 2) = J
  push_cast
  ring

private theorem carlsonRJ_eq_of_pos {φ k α2 : ℝ} (hφ0 : 0 < φ) (hφ : φ ≤ π / 2)
    (hk : k ^ 2 * sin φ ^ 2 < 1) (hα : α2 * sin φ ^ 2 < 1) :
    carlsonRJ (cos φ ^ 2 : ℝ) (1 - k ^ 2 * sin φ ^ 2 : ℝ) 1 (1 - α2 * sin φ ^ 2 : ℝ) =
      (3 / sin φ ^ 3 * ∫ θ in (0 : ℝ)..φ,
        (1 - k ^ 2 * sin θ ^ 2) ^ (-1 / 2 : ℝ) * (sin θ ^ 2 / (1 - α2 * sin θ ^ 2)) : ℝ) := by
  -- Under the substitution, `(t + 1 - α² sin² φ)⁻¹ = sin² θ / (sin² φ (1 - α² sin² θ))`.
  have h := integral_carlson_eq_integral_legendre
    (h := fun t ↦ ((t : ℂ) + ((1 - α2 * sin φ ^ 2 : ℝ) : ℂ))⁻¹)
    (g := fun θ ↦ sin θ ^ 2 / (1 - α2 * sin θ ^ 2) / sin φ ^ 2) hφ0 hφ hk fun θ ⟨hθ0, hθ⟩ ↦ by
      have hu : sin θ ≠ 0 := (sin_pos_of_pos_of_lt_pi hθ0 (by linarith [pi_pos])).ne'
      have hαu : 1 - α2 * sin θ ^ 2 ≠ 0 :=
        (sub_pos.mpr (mul_sin_sq_lt_one_of_le hα hθ0.le hθ.le hφ)).ne'
      have hsum : sin φ ^ 2 / sin θ ^ 2 - 1 + (1 - α2 * sin φ ^ 2) =
          sin φ ^ 2 * (1 - α2 * sin θ ^ 2) / sin θ ^ 2 := by
        field_simp
        ring
      rw [← Complex.ofReal_add, ← Complex.ofReal_inv, hsum, inv_div]
      congr 1
      field_simp
  have hdiv : ∫ θ in (0 : ℝ)..φ, (1 - k ^ 2 * sin θ ^ 2) ^ (-1 / 2 : ℝ) *
      (sin θ ^ 2 / (1 - α2 * sin θ ^ 2) / sin φ ^ 2) = (∫ θ in (0 : ℝ)..φ,
        (1 - k ^ 2 * sin θ ^ 2) ^ (-1 / 2 : ℝ) * (sin θ ^ 2 / (1 - α2 * sin θ ^ 2))) /
          sin φ ^ 2 := by
    rw [← intervalIntegral.integral_div]
    simp only [mul_div_assoc]
  rw [carlsonRJ_def, h, hdiv]
  generalize (∫ θ in (0 : ℝ)..φ,
    (1 - k ^ 2 * sin θ ^ 2) ^ (-1 / 2 : ℝ) * (sin θ ^ 2 / (1 - α2 * sin θ ^ 2))) = J
  push_cast
  ring

/-! ### The incomplete integrals -/

/-- **Legendre's integral of the first kind in Carlson's form** (DLMF 19.25.5): for
`|φ| ≤ π / 2` and `k² sin² φ < 1`, `F(φ, k) = sin φ · R_F(cos² φ, 1 - k² sin² φ, 1)`. -/
theorem ofReal_legendreF_eq_carlsonRF {φ k : ℝ} (hφ : |φ| ≤ π / 2) (hk : k ^ 2 * sin φ ^ 2 < 1) :
    (legendreF φ k : ℂ) =
      (sin φ : ℝ) * carlsonRF (cos φ ^ 2 : ℝ) (1 - k ^ 2 * sin φ ^ 2 : ℝ) 1 := by
  -- Both sides are odd in `φ`, so it suffices to prove the identity at `|φ| > 0`.
  refine Function.Odd.eq_of_eq_abs (f := fun φ ↦ (legendreF φ k : ℂ))
    (g := fun φ ↦ (sin φ : ℝ) * carlsonRF (cos φ ^ 2 : ℝ) (1 - k ^ 2 * sin φ ^ 2 : ℝ) 1)
    (fun φ ↦ by simp only [legendreF_neg, ofReal_neg])
    (fun φ ↦ by simp only [sin_neg, cos_neg, neg_sq, ofReal_neg, neg_mul]) fun hφ0 ↦ ?_
  have hk' : k ^ 2 * sin |φ| ^ 2 < 1 := by rcases abs_choice φ with h | h <;> simpa [h] using hk
  have hs : sin |φ| ≠ 0 := (sin_pos_of_pos_of_lt_pi hφ0 (by linarith [pi_pos])).ne'
  rw [carlsonRF_eq_of_pos hφ0 hφ hk']
  exact_mod_cast (mul_div_cancel₀ _ hs).symm

/-- **Legendre's integral of the second kind in Carlson's form** (DLMF 19.25.7): for
`|φ| ≤ π / 2` and `k² sin² φ < 1`, with `c = cos² φ` and `Δ = 1 - k² sin² φ`,
`E(φ, k) = sin φ · R_F(c, Δ, 1) - (k² / 3) sin³ φ · R_D(c, Δ, 1)`. -/
theorem ofReal_legendreE_eq_carlsonRF_sub_carlsonRD {φ k : ℝ} (hφ : |φ| ≤ π / 2)
    (hk : k ^ 2 * sin φ ^ 2 < 1) :
    (legendreE φ k : ℂ) =
      (sin φ : ℝ) * carlsonRF (cos φ ^ 2 : ℝ) (1 - k ^ 2 * sin φ ^ 2 : ℝ) 1 -
        (k : ℂ) ^ 2 / 3 * (sin φ : ℝ) ^ 3 *
          carlsonRD (cos φ ^ 2 : ℝ) (1 - k ^ 2 * sin φ ^ 2 : ℝ) 1 := by
  -- Both sides are odd in `φ`, so it suffices to prove the identity at `|φ| > 0`.
  refine Function.Odd.eq_of_eq_abs (f := fun φ ↦ (legendreE φ k : ℂ))
    (g := fun φ ↦ (sin φ : ℝ) * carlsonRF (cos φ ^ 2 : ℝ) (1 - k ^ 2 * sin φ ^ 2 : ℝ) 1 -
      (k : ℂ) ^ 2 / 3 * (sin φ : ℝ) ^ 3 * carlsonRD (cos φ ^ 2 : ℝ) (1 - k ^ 2 * sin φ ^ 2 : ℝ) 1)
    (fun φ ↦ by simp only [legendreE_neg, ofReal_neg])
    (fun φ ↦ by simp only [sin_neg, cos_neg, neg_sq, ofReal_neg]; ring) fun hφ0 ↦ ?_
  have hk' : k ^ 2 * sin |φ| ^ 2 < 1 := by rcases abs_choice φ with h | h <;> simpa [h] using hk
  have hs : sin |φ| ≠ 0 := (sin_pos_of_pos_of_lt_pi hφ0 (by linarith [pi_pos])).ne'
  rw [carlsonRF_eq_of_pos hφ0 hφ hk', carlsonRD_eq_of_pos hφ0 hφ hk',
    legendreE_eq_legendreF_sub (abs_nonneg φ) hφ hk']
  norm_cast
  field_simp

/-- **Legendre's integral of the third kind in Carlson's form** (DLMF 19.25.14): for
`|φ| ≤ π / 2`, `k² sin² φ < 1` and `α² sin² φ < 1`, with `c = cos² φ` and `Δ = 1 - k² sin² φ`,
`Π(φ, k, α²) = sin φ · R_F(c, Δ, 1) + (α² / 3) sin³ φ · R_J(c, Δ, 1, 1 - α² sin² φ)`. -/
theorem ofReal_legendrePi_eq_carlsonRF_add_carlsonRJ {φ k α2 : ℝ} (hφ : |φ| ≤ π / 2)
    (hk : k ^ 2 * sin φ ^ 2 < 1) (hα : α2 * sin φ ^ 2 < 1) :
    (legendrePi φ k α2 : ℂ) =
      (sin φ : ℝ) * carlsonRF (cos φ ^ 2 : ℝ) (1 - k ^ 2 * sin φ ^ 2 : ℝ) 1 +
        (α2 : ℂ) / 3 * (sin φ : ℝ) ^ 3 *
          carlsonRJ (cos φ ^ 2 : ℝ) (1 - k ^ 2 * sin φ ^ 2 : ℝ) 1 (1 - α2 * sin φ ^ 2 : ℝ) := by
  -- Both sides are odd in `φ`, so it suffices to prove the identity at `|φ| > 0`.
  refine Function.Odd.eq_of_eq_abs (f := fun φ ↦ (legendrePi φ k α2 : ℂ))
    (g := fun φ ↦ (sin φ : ℝ) * carlsonRF (cos φ ^ 2 : ℝ) (1 - k ^ 2 * sin φ ^ 2 : ℝ) 1 +
      (α2 : ℂ) / 3 * (sin φ : ℝ) ^ 3 *
        carlsonRJ (cos φ ^ 2 : ℝ) (1 - k ^ 2 * sin φ ^ 2 : ℝ) 1 (1 - α2 * sin φ ^ 2 : ℝ))
    (fun φ ↦ by simp only [legendrePi_neg, ofReal_neg])
    (fun φ ↦ by simp only [sin_neg, cos_neg, neg_sq, ofReal_neg]; ring) fun hφ0 ↦ ?_
  have hk' : k ^ 2 * sin |φ| ^ 2 < 1 := by rcases abs_choice φ with h | h <;> simpa [h] using hk
  have hα' : α2 * sin |φ| ^ 2 < 1 := by rcases abs_choice φ with h | h <;> simpa [h] using hα
  have hs : sin |φ| ≠ 0 := (sin_pos_of_pos_of_lt_pi hφ0 (by linarith [pi_pos])).ne'
  rw [carlsonRF_eq_of_pos hφ0 hφ hk', carlsonRJ_eq_of_pos hφ0 hφ hk' hα',
    legendrePi_eq_legendreF_add (abs_nonneg φ) hφ hk' hα']
  norm_cast
  field_simp

/-! ### The complete integrals -/

/-- **The complete integral of the first kind in Carlson's form** (DLMF 19.25.1): for
`k² < 1`, `K(k) = R_F(0, 1 - k², 1)`. -/
theorem ofReal_legendreK_eq_carlsonRF {k : ℝ} (hk : k ^ 2 < 1) :
    (legendreK k : ℂ) = carlsonRF 0 (1 - k ^ 2 : ℝ) 1 := by
  simpa [legendreK_def] using ofReal_legendreF_eq_carlsonRF (φ := π / 2)
    (by rw [abs_of_pos (by positivity)]) (by simpa using hk)

/-- **The complete integral of the second kind in Carlson's form** (DLMF 19.25.7 at
`φ = π / 2`): for `k² < 1`, `E(k) = R_F(0, 1 - k², 1) - (k² / 3) R_D(0, 1 - k², 1)`. -/
theorem ofReal_legendreEc_eq_carlsonRF_sub_carlsonRD {k : ℝ} (hk : k ^ 2 < 1) :
    (legendreEc k : ℂ) =
      carlsonRF 0 (1 - k ^ 2 : ℝ) 1 - (k : ℂ) ^ 2 / 3 * carlsonRD 0 (1 - k ^ 2 : ℝ) 1 := by
  simpa [legendreEc_def] using ofReal_legendreE_eq_carlsonRF_sub_carlsonRD (φ := π / 2)
    (by rw [abs_of_pos (by positivity)]) (by simpa using hk)

/-- **The complete integral of the third kind in Carlson's form** (DLMF 19.25.2): for `k² < 1`
and `α² < 1`, `Π(k, α²) = R_F(0, 1 - k², 1) + (α² / 3) R_J(0, 1 - k², 1, 1 - α²)`. -/
theorem ofReal_legendrePic_eq_carlsonRF_add_carlsonRJ {k α2 : ℝ} (hk : k ^ 2 < 1)
    (hα : α2 < 1) :
    (legendrePic k α2 : ℂ) = carlsonRF 0 (1 - k ^ 2 : ℝ) 1 +
      (α2 : ℂ) / 3 * carlsonRJ 0 (1 - k ^ 2 : ℝ) 1 (1 - α2 : ℝ) := by
  simpa [legendrePic_def] using ofReal_legendrePi_eq_carlsonRF_add_carlsonRJ (φ := π / 2)
    (by rw [abs_of_pos (by positivity)]) (by simpa using hk) (by simpa using hα)

end TauCeti.Real
