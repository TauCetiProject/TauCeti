/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
public import TauCeti.NumberTheory.LFunctions.Theta.Gaussian
public import TauCeti.NumberTheory.LFunctions.Theta.Surface.Haar
import Mathlib.MeasureTheory.Integral.Pi
import TauCeti.Analysis.MellinTransform
import TauCeti.Analysis.SpecialFunctions.Pow.Complex

/-!
# The gamma integral of the archimedean Gaussian

For a point `x` of the mixed space of a number field `K` with nonzero norm, the archimedean
Gaussian `y ↦ exp (-π ∑_w y_w |x_w|²)`, integrated against `N(y)^(s/2)` and the multiplicative
Haar measure `dy / y` of the positive parameters, is a product of one gamma integral per
infinite place:

`∫ exp (-π ∑_w y_w |x_w|²) N(y)^(s/2) dy / y = Γ_ℝ(s)^r₁ Γ_ℝ(2s)^r₂ |N(x)|^(-s)`

for `0 < Re s` (`TauCeti.LFunctions.integral_archGaussian_mul_archNorm_cpow`), with
`N(y) = ∏_w y_w^(mult w)` and `|N(x)| = ∏_w |x_w|^(mult w)` (Mathlib's `mixedEmbedding.norm`).
At a real place the factor is `∫_0^∞ e^(-π t x²) t^(s/2) dt / t = Γ_ℝ(s) |x|^(-s)`; at a complex
place it is `∫_0^∞ e^(-π t |z|²) t^s dt / t = π^(-s) Γ(s) |z|^(-2s) = Γ_ℝ(2s) |z|^(-2s)`. In
terms of Deligne's `Γ_ℂ(s) = 2 (2π)^(-s) Γ(s)` the complex factor is `2^(s-1) Γ_ℂ(s)`: a complex
coordinate counts once in the Gaussian, in accordance with the Euclidean pairing `mixedInner`, and
`dy / y` is the product over places, so the complex places contribute `2^(r₂(s-1))` against the
gamma factor `Γ_ℝ(s)^r₁ Γ_ℂ(s)^r₂` of the completed Dedekind zeta function.

This is the gamma integral contributed by one unit orbit of lattice points when the theta series
of an ideal lattice is integrated over the cone above a fundamental domain for the units (Hecke's
integral representation of a partial zeta function). The integrand is integrable
(`TauCeti.LFunctions.integrable_archGaussian_mul_archNorm_cpow`), as the interchange of the
lattice sum with the integral requires.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §§4–5.
-/

public section

noncomputable section

open Complex MeasureTheory Set NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open scoped Real

namespace TauCeti.LFunctions

variable {K : Type*} [Field K] [NumberField K]

/-! ### One place -/

/-- The exponent `m s / 2` of the factor at a place of multiplicity `m` has positive real part. -/
private theorem re_natCast_mul_div_two_pos {m : ℕ} (hm : m ≠ 0) {s : ℂ} (hs : 0 < s.re) :
    0 < ((m : ℂ) * s / 2).re := by
  have : ((m : ℂ) * s / 2).re = m * s.re / 2 := by simp
  rw [this]
  exact div_pos (mul_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm)) hs) two_pos

/-- The factor of the archimedean Gaussian at one place is integrable against
`t ^ (m s / 2) dt / t`. -/
private theorem integrable_cpow_mul_exp_neg_multHaar {a : ℝ} (ha : 0 < a) {m : ℕ} (hm : m ≠ 0)
    {s : ℂ} (hs : 0 < s.re) :
    Integrable (fun t : ℝ ↦ (t : ℂ) ^ (m * s / 2) * (Real.exp (-(π * a ^ 2 * t)) : ℂ))
      multHaar := by
  simpa only [smul_eq_mul] using integrable_multHaar_cpow_smul_iff.mpr
    (mellinConvergent_exp_neg_mul (by positivity) (re_natCast_mul_div_two_pos hm hs))

/-- The factor of the archimedean Gaussian at one place, against `t ^ (m s / 2) dt / t`:
`∫_0^∞ e^(-π t a²) t^(m s / 2) dt / t = Γ_ℝ(m s) a^(-m s)`. -/
private theorem integral_cpow_mul_exp_neg_multHaar {a : ℝ} (ha : 0 < a) {m : ℕ} (hm : m ≠ 0)
    {s : ℂ} (hs : 0 < s.re) :
    ∫ t, (t : ℂ) ^ (m * s / 2) * (Real.exp (-(π * a ^ 2 * t)) : ℂ) ∂multHaar =
      Gammaℝ (m * s) * (a : ℂ) ^ (m * -s) := by
  have hc : 0 < π * a ^ 2 := by positivity
  have hpow : ((π * a ^ 2 : ℝ) : ℂ) ^ (-(m * s / 2)) =
      (π : ℂ) ^ (-(m * s) / 2) * (a : ℂ) ^ (m * -s) := by
    rw [ofReal_mul, ofReal_mul_cpow Real.pi_pos.le, ofReal_pow, ofReal_pow_cpow ha.le]
    congr 2 <;> ring
  have h := integral_multHaar_cpow_smul (fun t : ℝ ↦ (Real.exp (-(π * a ^ 2 * t)) : ℂ))
    (m * s / 2)
  simp only [smul_eq_mul, mellin, ofReal_exp, ofReal_neg, ofReal_mul (π * a ^ 2)] at h ⊢
  rw [h, integral_cpow_mul_exp_neg_mul_Ioi (re_natCast_mul_div_two_pos hm hs) hc, one_div,
    inv_cpow_ofReal_nonneg hc.le, ← cpow_neg, hpow, Gammaℝ_def]
  ring

/-! ### The product over the places -/

/-- The coordinates of a point of nonzero norm are positive at every place. -/
private theorem normAtPlace_pos_of_norm_ne_zero {x : mixedSpace K}
    (hx : mixedEmbedding.norm x ≠ 0) (w : InfinitePlace K) : 0 < normAtPlace w x :=
  (normAtPlace_nonneg w x).lt_of_ne' (mixedEmbedding.norm_ne_zero_iff.mp hx w)

/-- A principal power of `∏_w b_w ^ mult w`, for nonnegative `b`, is `∏_w b_w ^ (mult w · z)`. -/
private theorem ofReal_prod_pow_mult_cpow {b : InfinitePlace K → ℝ} (hb : ∀ w, 0 ≤ b w)
    (z : ℂ) : ((∏ w, b w ^ mult w : ℝ) : ℂ) ^ z = ∏ w, (b w : ℂ) ^ (mult w * z) := by
  rw [ofReal_prod_cpow _ fun w _ ↦ pow_nonneg (hb w) _]
  refine Finset.prod_congr rfl fun w _ ↦ ?_
  rw [ofReal_pow, ofReal_pow_cpow (hb w)]

/-- On the positive orthant the integrand splits into one factor per infinite place. -/
private theorem archGaussian_mul_archNorm_cpow_eq_prod {y : realSpace K} (hy : ∀ w, 0 < y w)
    (x : mixedSpace K) (s : ℂ) :
    archGaussian y x * (archNorm y : ℂ) ^ (s / 2) =
      ∏ w, (y w : ℂ) ^ (mult w * s / 2) *
        (Real.exp (-(π * normAtPlace w x ^ 2 * y w)) : ℂ) := by
  rw [Finset.prod_mul_distrib, mul_comm, archGaussian_apply, archNorm_apply,
    ofReal_prod_pow_mult_cpow fun w ↦ (hy w).le, Finset.mul_sum, Real.exp_sum, ofReal_prod]
  simp_rw [mul_div_assoc]
  congr 1
  refine Finset.prod_congr rfl fun w _ ↦ ?_
  ring_nf

/-- The product over the places of `Γ_ℝ(mult w · s)` is `Γ_ℝ(s)^r₁ Γ_ℝ(2s)^r₂`. -/
private theorem prod_Gammaℝ_mult_mul (s : ℂ) :
    ∏ w : InfinitePlace K, Gammaℝ (mult w * s) =
      Gammaℝ s ^ nrRealPlaces K * Gammaℝ (2 * s) ^ nrComplexPlaces K := by
  classical
  rw [prod_eq_prod_mul_prod]
  simp_rw [mult_isReal, mult_isComplex, Finset.prod_const, Finset.card_univ]
  push_cast
  rw [one_mul]

variable {x : mixedSpace K} {s : ℂ}

/-- For `x` of nonzero norm and `0 < Re s`, the archimedean Gaussian against `N(y)^(s/2)` is
integrable for the multiplicative Haar measure `dy / y` of the parameters. -/
theorem integrable_archGaussian_mul_archNorm_cpow (hx : mixedEmbedding.norm x ≠ 0)
    (hs : 0 < s.re) :
    Integrable (fun y ↦ archGaussian y x * (archNorm y : ℂ) ^ (s / 2)) (archHaar K) := by
  have ha := normAtPlace_pos_of_norm_ne_zero hx
  have hint := Integrable.fintype_prod (μ := fun _ : InfinitePlace K ↦ multHaar)
    fun w ↦ integrable_cpow_mul_exp_neg_multHaar (ha w) (mult_ne_zero (w := w)) hs
  rw [← archHaar_def] at hint
  refine hint.congr ?_
  filter_upwards [ae_archHaar_pos] with y hy
  exact (archGaussian_mul_archNorm_cpow_eq_prod hy x s).symm

/-- **The gamma integral of the archimedean Gaussian.** For `x` of nonzero norm and `0 < Re s`,
`∫ exp (-π ∑_w y_w |x_w|²) N(y)^(s/2) dy / y = Γ_ℝ(s)^r₁ Γ_ℝ(2s)^r₂ |N(x)|^(-s)`. The factor
`Γ_ℝ(2s) = π^(-s) Γ(s)` of a complex place is `2^(s-1) Γ_ℂ(s)`. -/
theorem integral_archGaussian_mul_archNorm_cpow (hx : mixedEmbedding.norm x ≠ 0)
    (hs : 0 < s.re) :
    ∫ y, archGaussian y x * (archNorm y : ℂ) ^ (s / 2) ∂archHaar K =
      Gammaℝ s ^ nrRealPlaces K * Gammaℝ (2 * s) ^ nrComplexPlaces K *
        (mixedEmbedding.norm x : ℂ) ^ (-s) := by
  have ha := normAtPlace_pos_of_norm_ne_zero hx
  calc ∫ y, archGaussian y x * (archNorm y : ℂ) ^ (s / 2) ∂archHaar K
      = ∫ y, ∏ w, (y w : ℂ) ^ (mult w * s / 2) *
          (Real.exp (-(π * normAtPlace w x ^ 2 * y w)) : ℂ) ∂archHaar K := by
        refine integral_congr_ae ?_
        filter_upwards [ae_archHaar_pos] with y hy
        exact archGaussian_mul_archNorm_cpow_eq_prod hy x s
    _ = ∏ w, ∫ t, (t : ℂ) ^ (mult w * s / 2) *
          (Real.exp (-(π * normAtPlace w x ^ 2 * t)) : ℂ) ∂multHaar := by
        rw [archHaar_def]
        exact integral_fintype_prod_eq_prod (fun w (t : ℝ) ↦ (t : ℂ) ^ (mult w * s / 2) *
          (Real.exp (-(π * normAtPlace w x ^ 2 * t)) : ℂ))
    _ = ∏ w, Gammaℝ (mult w * s) * (normAtPlace w x : ℂ) ^ (mult w * -s) := by
        exact Finset.prod_congr rfl fun w _ ↦
          integral_cpow_mul_exp_neg_multHaar (ha w) (mult_ne_zero (w := w)) hs
    _ = _ := by
        rw [Finset.prod_mul_distrib, prod_Gammaℝ_mult_mul, mixedEmbedding.norm_apply,
          ofReal_prod_pow_mult_cpow fun w ↦ (ha w).le]

end TauCeti.LFunctions
