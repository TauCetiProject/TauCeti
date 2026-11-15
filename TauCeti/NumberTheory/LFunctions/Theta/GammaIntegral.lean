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
import TauCeti.Analysis.SpecialFunctions.Gamma.Archimedean
import TauCeti.Analysis.SpecialFunctions.Pow.Complex
import TauCeti.NumberTheory.NumberField.CanonicalEmbedding.Basic

/-!
# The gamma integral of the archimedean Gaussian

For a point `x` of the mixed space of a number field `K` with nonzero norm and placewise complex
exponents `z : InfinitePlace K → ℂ` with `∀ w, 0 < (z w).re`, integrating the archimedean Gaussian
`y ↦ exp (-π ∑_w y_w |x_w|²)` against `∏_w y_w^(z_w / 2)` and the multiplicative Haar measure
`dy / y` of the positive parameters splits into one gamma integral per infinite place:

`∫ (∏_w y_w^(z_w / 2)) exp (-π ∑_w y_w |x_w|²) dy / y = (∏_w Γ_ℝ(z_w)) * ∏_w |x_w|^(-z_w)`

(`TauCeti.LFunctions.integrable_prod_cpow_div_two_mul_archGaussian`,
`TauCeti.LFunctions.integral_prod_cpow_div_two_mul_archGaussian`). Decomposing
`∏_w Γ_ℝ(mult w · s + p w)` into Deligne's `Γ_ℝ` and `Γ_ℂ` factors across the real and complex
places (`TauCeti.LFunctions.prod_Gammaℝ_mult_mul_add`) expresses the complex factors using
`Γ_ℝ(2 z) = 2^(z - 1) Γ_ℂ(z)`.

Specializing to `z w = mult w * s` (`0 < Re s`), where `∏_w y_w^(mult w · s / 2) = N(y)^(s / 2)`
with `N(y) = ∏_w y_w^(mult w)` and `|N(x)| = ∏_w |x_w|^(mult w)` (Mathlib's `mixedEmbedding.norm`),
gives the unweighted Dedekind gamma integral:

`∫ exp (-π ∑_w y_w |x_w|²) N(y)^(s/2) dy / y = Γ_ℝ(s)^r₁ Γ_ℝ(2s)^r₂ |N(x)|^(-s)`

(`TauCeti.LFunctions.integrable_archGaussian_mul_archNorm_cpow`,
`TauCeti.LFunctions.integral_archGaussian_mul_archNorm_cpow`). At a real place the factor is
`∫_0^∞ e^(-π t x²) t^(s/2) dt / t = Γ_ℝ(s) |x|^(-s)`; at a complex place it is
`∫_0^∞ e^(-π t |z|²) t^s dt / t = π^(-s) Γ(s) |z|^(-2s) = Γ_ℝ(2s) |z|^(-2s)`, which equals
`2^(s-1) Γ_ℂ(s) |z|^(-2s)`.

This is the gamma integral contributed by one unit orbit of lattice points when the theta series
of an ideal lattice is integrated over the cone above a fundamental domain for the units (Hecke's
integral representation of a partial zeta function or Grossencharacter L-function).

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §§4–5 and §8.
-/

public section

noncomputable section

open Complex MeasureTheory Set NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
  TauCeti.NumberField.mixedEmbedding
open scoped Real

namespace TauCeti.LFunctions

variable {K : Type*} [Field K] [NumberField K]

/-! ### Placewise-exponent gamma integrals and `Γ_ℝ`/`Γ_ℂ` decomposition -/

/-- For `x` of nonzero norm and placewise exponents `z : InfinitePlace K → ℂ` with
`∀ w, 0 < (z w).re`, the product `(∏_w y_w^(z_w / 2)) * archGaussian y x` is integrable against
the multiplicative Haar measure `archHaar K`. -/
theorem integrable_prod_cpow_div_two_mul_archGaussian {x : mixedSpace K}
    (hx : mixedEmbedding.norm x ≠ 0) {z : InfinitePlace K → ℂ} (hz : ∀ w, 0 < (z w).re) :
    Integrable (fun y ↦ (∏ w : InfinitePlace K, (y w : ℂ) ^ (z w / 2)) * archGaussian y x)
      (archHaar K) := by
  have ha := normAtPlace_pos_of_norm_ne_zero hx
  have hint := Integrable.fintype_prod (μ := fun _ : InfinitePlace K ↦ multHaar)
    fun w ↦ integrable_cpow_div_two_mul_exp_neg_multHaar (ha w) (hz w)
  rw [← archHaar_def] at hint
  refine hint.congr (Filter.Eventually.of_forall fun y ↦ ?_)
  dsimp only
  rw [archGaussian_eq_prod, Finset.prod_mul_distrib]

/-- **Placewise-exponent gamma integral of the archimedean Gaussian.** For `x` of nonzero norm and
`z : InfinitePlace K → ℂ` with `∀ w, 0 < (z w).re`,
`∫ (∏_w y_w^(z_w / 2)) exp (-π ∑_w y_w |x_w|²) dy / y = (∏_w Γ_ℝ(z_w)) * ∏_w |x_w|^(-z_w)`. -/
theorem integral_prod_cpow_div_two_mul_archGaussian {x : mixedSpace K}
    (hx : mixedEmbedding.norm x ≠ 0) {z : InfinitePlace K → ℂ} (hz : ∀ w, 0 < (z w).re) :
    ∫ y, (∏ w : InfinitePlace K, (y w : ℂ) ^ (z w / 2)) * archGaussian y x ∂archHaar K =
      (∏ w : InfinitePlace K, Gammaℝ (z w)) *
        ∏ w : InfinitePlace K, (normAtPlace w x : ℂ) ^ (-z w) := by
  have ha := normAtPlace_pos_of_norm_ne_zero hx
  have hprod (y : realSpace K) :
      (∏ w : InfinitePlace K, (y w : ℂ) ^ (z w / 2)) * archGaussian y x =
        ∏ w : InfinitePlace K, (y w : ℂ) ^ (z w / 2) *
          (Real.exp (-(π * normAtPlace w x ^ 2 * y w)) : ℂ) := by
    rw [archGaussian_eq_prod, Finset.prod_mul_distrib]
  simp_rw [hprod]
  rw [archHaar_def,
    integral_fintype_prod_eq_prod (fun (w : InfinitePlace K) (t : ℝ) ↦
      (t : ℂ) ^ (z w / 2) * (Real.exp (-(π * normAtPlace w x ^ 2 * t)) : ℂ)),
    ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun w _ ↦ integral_cpow_div_two_mul_exp_neg_multHaar (ha w) (hz w)

open scoped Classical in
/-- Decomposition of `∏_w Γ_ℝ(mult w · s + p w)` into Deligne's `Γ_ℝ` and `Γ_ℂ` factors across
the real and complex infinite places of `K`, for arbitrary complex shifts
`p : InfinitePlace K → ℂ`. -/
theorem prod_Gammaℝ_mult_mul_add (s : ℂ) (p : InfinitePlace K → ℂ) :
    (∏ w : InfinitePlace K, Gammaℝ ((mult w : ℂ) * s + p w)) =
      ((2 : ℂ) ^ (s - 1)) ^ nrComplexPlaces K *
        (2 : ℂ) ^ ((∑ w : {w : InfinitePlace K // w.IsComplex}, p w.1) / 2) *
        ((∏ w : {w : InfinitePlace K // w.IsReal}, Gammaℝ (s + p w.1)) *
          ∏ w : {w : InfinitePlace K // w.IsComplex}, Gammaℂ (s + p w.1 / 2)) := by
  have hreal :
      (∏ w : {w : InfinitePlace K // w.IsReal}, Gammaℝ ((mult w.1 : ℂ) * s + p w.1)) =
      ∏ w : {w : InfinitePlace K // w.IsReal}, Gammaℝ (s + p w.1) := by
    refine Finset.prod_congr rfl fun w _ ↦ ?_
    rw [mult_isReal w, Nat.cast_one, one_mul]
  have hcomplex :
      (∏ w : {w : InfinitePlace K // w.IsComplex}, Gammaℝ ((mult w.1 : ℂ) * s + p w.1)) =
      ((2 : ℂ) ^ (s - 1)) ^ nrComplexPlaces K *
        (2 : ℂ) ^ ((∑ w : {w : InfinitePlace K // w.IsComplex}, p w.1) / 2) *
        ∏ w : {w : InfinitePlace K // w.IsComplex}, Gammaℂ (s + p w.1 / 2) := by
    have hstep (w : {w : InfinitePlace K // w.IsComplex}) :
        Gammaℝ ((mult w.1 : ℂ) * s + p w.1) =
          (2 : ℂ) ^ (s - 1) * (2 : ℂ) ^ (p w.1 / 2) * Gammaℂ (s + p w.1 / 2) := by
      have harg : (mult w.1 : ℂ) * s + p w.1 = 2 * (s + p w.1 / 2) := by
        rw [mult_isComplex w, Nat.cast_ofNat]
        ring
      have hexp : s + p w.1 / 2 - 1 = (s - 1) + p w.1 / 2 := by ring
      rw [harg, Gammaℝ_two_mul, hexp, cpow_add _ _ two_ne_zero]
    simp_rw [hstep, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      ← TauCeti.cpow_sum two_ne_zero, ← Finset.sum_div]
  rw [prod_eq_prod_mul_prod, hreal, hcomplex]
  ring

/-! ### Unweighted Dedekind specialization -/

/-- On the positive orthant, `archGaussian y x * N(y)^(s/2)` is the placewise power product
at `z w = mult w * s` times `archGaussian y x`. -/
private theorem archGaussian_mul_archNorm_cpow_eq {y : realSpace K} (hy : ∀ w, 0 < y w)
    (x : mixedSpace K) (s : ℂ) :
    archGaussian y x * (archNorm y : ℂ) ^ (s / 2) =
      (∏ w : InfinitePlace K, (y w : ℂ) ^ ((mult w : ℂ) * s / 2)) * archGaussian y x := by
  rw [mul_comm, archNorm_apply, ofReal_prod_pow_cpow _ fun w _ ↦ (hy w).le]
  simp_rw [mul_div_assoc]

/-- The product over the places of `Γ_ℝ(mult w · s)` is `Γ_ℝ(s)^r₁ Γ_ℝ(2s)^r₂`. -/
private theorem prod_Gammaℝ_mult_mul (s : ℂ) :
    ∏ w : InfinitePlace K, Gammaℝ (mult w * s) =
      Gammaℝ s ^ nrRealPlaces K * Gammaℝ (2 * s) ^ nrComplexPlaces K := by
  classical
  rw [prod_eq_prod_mul_prod]
  simp_rw [mult_isReal, mult_isComplex, Finset.prod_const, Finset.card_univ]
  push_cast
  rw [one_mul]

omit [NumberField K] in
private theorem re_mult_mul_pos {s : ℂ} (hs : 0 < s.re) (w : InfinitePlace K) :
    0 < ((mult w : ℂ) * s).re := by
  have hm : (0 : ℝ) < mult w := Nat.cast_pos.mpr (Nat.pos_of_ne_zero mult_ne_zero)
  simpa using mul_pos hm hs

variable {x : mixedSpace K} {s : ℂ}

/-- For `x` of nonzero norm and `0 < Re s`, the archimedean Gaussian against `N(y)^(s/2)` is
integrable for the multiplicative Haar measure `dy / y` of the parameters. -/
theorem integrable_archGaussian_mul_archNorm_cpow (hx : mixedEmbedding.norm x ≠ 0)
    (hs : 0 < s.re) :
    Integrable (fun y ↦ archGaussian y x * (archNorm y : ℂ) ^ (s / 2)) (archHaar K) := by
  refine (integrable_prod_cpow_div_two_mul_archGaussian hx (re_mult_mul_pos hs)).congr ?_
  filter_upwards [ae_archHaar_pos] with y hy
  exact (archGaussian_mul_archNorm_cpow_eq hy x s).symm

/-- **The gamma integral of the archimedean Gaussian.** For `x` of nonzero norm and `0 < Re s`,
`∫ exp (-π ∑_w y_w |x_w|²) N(y)^(s/2) dy / y = Γ_ℝ(s)^r₁ Γ_ℝ(2s)^r₂ |N(x)|^(-s)`. The factor
`Γ_ℝ(2s) = π^(-s) Γ(s)` of a complex place is `2^(s-1) Γ_ℂ(s)`. -/
theorem integral_archGaussian_mul_archNorm_cpow (hx : mixedEmbedding.norm x ≠ 0)
    (hs : 0 < s.re) :
    ∫ y, archGaussian y x * (archNorm y : ℂ) ^ (s / 2) ∂archHaar K =
      Gammaℝ s ^ nrRealPlaces K * Gammaℝ (2 * s) ^ nrComplexPlaces K *
        (mixedEmbedding.norm x : ℂ) ^ (-s) := by
  have ha := normAtPlace_pos_of_norm_ne_zero hx
  have heq : ∫ y, archGaussian y x * (archNorm y : ℂ) ^ (s / 2) ∂archHaar K =
      ∫ y, (∏ w : InfinitePlace K, (y w : ℂ) ^ ((mult w : ℂ) * s / 2)) *
        archGaussian y x ∂archHaar K := by
    refine integral_congr_ae ?_
    filter_upwards [ae_archHaar_pos] with y hy
    exact archGaussian_mul_archNorm_cpow_eq hy x s
  rw [heq, integral_prod_cpow_div_two_mul_archGaussian hx (re_mult_mul_pos hs),
    prod_Gammaℝ_mult_mul, mixedEmbedding.norm_apply,
    ofReal_prod_pow_cpow _ fun w _ ↦ (ha w).le]
  simp_rw [mul_neg]

end TauCeti.LFunctions
