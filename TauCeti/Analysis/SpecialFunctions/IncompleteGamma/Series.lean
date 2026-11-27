/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.IncompleteGamma.Complementary
import Mathlib.Analysis.Analytic.Binomial
import TauCeti.Analysis.SpecialFunctions.IncompleteGamma.SpecialValues
import TauCeti.Analysis.SpecialFunctions.Pow.Complex
import TauCeti.RingTheory.Binomial

/-!
# Series expansions of the complex incomplete Gamma functions

Series expansions of the incomplete Gamma functions from DLMF §8.7(i).

## Main results

* `Complex.hasSum_regularizedGamma`: `P(a, z) = z^a e^{−z} ∑ zᵏ / Γ(a + k + 1)` for every `a`
  and `z` (DLMF 8.7.3, second form, divided by `Γ(a)`);
* `Complex.hasSum_lowerIncompleteGamma`: `γ(a, z) = ∑ (−1)ᵏ z^{a+k} / (k! (a + k))` for
  `a ∉ −ℕ` and every `z`;
* `Complex.hasSum_Gamma_sub_upperIncompleteGamma`,
  `Complex.hasSum_Gamma_sub_upperIncompleteGamma_cexp`: the two series of DLMF 8.7.3 for
  `Γ(a) − Γ(a, z)`, for `a ∉ −ℕ` and `z` in the slit plane;
* `Complex.hasSum_upperIncompleteGamma_sub_upperIncompleteGamma_add`: DLMF 8.7.2 for the upper
  function, `Γ(a, x) − Γ(a, x + y) = e^{−x} x^{a−1} ∑ (1 − a)ₙ / (−x)ⁿ (1 − e^{−y} eₙ(y))`
  for every `a`, real `x` and complex `y` with `|y| < x`;
* `Complex.hasSum_lowerIncompleteGamma_add_sub_lowerIncompleteGamma`: DLMF 8.7.2 for the lower
  function, `γ(a, x + y) − γ(a, x)`, with the same series, for `a ∉ −ℕ`.

Here `eₙ(y) = ∑_{k=0}^n yᵏ / k!` is the truncated exponential series (DLMF 8.4.11) and
`(b)ₙ = (ascPochhammer ℂ n).eval b` is Pochhammer's symbol.

## Implementation notes

The series of DLMF 8.7.3 are those of DLMF 8.7.1 for Tricomi's function `γ*(a, z)`
(`Complex.hasSum_tricomiIncompleteGamma`,
`Complex.hasSum_tricomiIncompleteGamma_of_ne_neg_natCast`), multiplied by `Γ(a) z^a`,
together with the complementary relation DLMF 8.2.3
(`Complex.upperIncompleteGamma_add_lowerIncompleteGamma`).

DLMF 8.7.2 is proved for real `x`, where the segment from `x` to `x + y` lies in the right half
plane. There `Γ(a, x) − Γ(a, x + y)` is the integral of `t^{a−1} e^{−t}` along the segment; the
binomial series of `(1 + t y / x)^{a−1}` (Mathlib's `binomialSeries`) is integrated termwise by
dominated convergence, and `∫₀^y sⁿ e^{−s} ds = n! (1 − e^{−y} eₙ(y))` is `γ(n + 1, y)` by
DLMF 8.2.1 (`Complex.lowerIncompleteGamma_eq_integral`) and DLMF 8.4.7
(`Complex.lowerIncompleteGamma_natCast_add_one`). The upper form holds at every `a`; the lower form
needs `a ∉ −ℕ`, where `γ(a, ·)` takes Mathlib's junk value `0`.

## References

* NIST Digital Library of Mathematical Functions, §8.7, <https://dlmf.nist.gov/8.7>.

Adapted from `incompleteGamma_increment_series`, `upperIncompleteGamma_hasSum_alternating` and
`upperIncompleteGamma_hasSum_exponential` of the lean-DLMF project
(<https://github.com/bjbraams/lean-DLMF>), file `DLMF/IncompleteGamma/SeriesRecurrences.lean`.
There 8.7.2 is stated for complex `x` with the segment from `x` to `x + y` in the slit plane;
here, following DLMF, `x` is real and positive, and the upper form is stated for
every `a`.
-/

public section

noncomputable section

open Finset MeasureTheory Set
open scoped Interval Nat NNReal ENNReal

namespace Complex

/-- **DLMF 8.7.3**, second form, divided by `Γ(a)`: `P(a, z) = z^a e^{−z} ∑ zᵏ / Γ(a + k + 1)`
for every `a` and `z`. -/
theorem hasSum_regularizedGamma (a z : ℂ) :
    HasSum (fun k : ℕ => z ^ a * cexp (-z) * z ^ k / Gamma (a + k + 1))
      (regularizedGamma a z) := by
  rw [regularizedGamma_def]
  exact ((hasSum_tricomiIncompleteGamma a z).mul_left (z ^ a)).congr_fun fun k => by ring

/-- The power series of the lower incomplete Gamma function:
`γ(a, z) = ∑ (−1)ᵏ z^{a+k} / (k! (a + k))` for `a ∉ −ℕ` and every `z`, with the principal power
`z^{a+k}`. -/
theorem hasSum_lowerIncompleteGamma {a : ℂ} (ha : ∀ n : ℕ, a ≠ -n) (z : ℂ) :
    HasSum (fun k : ℕ => (-1) ^ k * z ^ (a + k) / (k ! * (a + k)))
      (lowerIncompleteGamma a z) := by
  rw [lowerIncompleteGamma_def, regularizedGamma_def, ← mul_assoc]
  refine ((hasSum_tricomiIncompleteGamma_of_ne_neg_natCast ha z).mul_left
    (Gamma a * z ^ a)).congr_fun fun k => ?_
  have hΓ : Gamma a ≠ 0 := Gamma_ne_zero ha
  have hak : a + k ≠ 0 := fun h => ha k (by linear_combination h)
  rcases eq_or_ne z 0 with rfl | hz
  · have ha0 : a ≠ 0 := by simpa using ha 0
    simp [zero_cpow hak, zero_cpow ha0]
  · rw [cpow_add _ _ hz, cpow_natCast, neg_pow z]
    field_simp

/-- **DLMF 8.7.3**: `Γ(a, z) = Γ(a) − ∑ (−1)ᵏ z^{a+k} / (k! (a + k))` for `a ∉ −ℕ` and `z` in the
slit plane. -/
theorem hasSum_Gamma_sub_upperIncompleteGamma {a z : ℂ} (ha : ∀ n : ℕ, a ≠ -n)
    (hz : z ∈ slitPlane) :
    HasSum (fun k : ℕ => (-1) ^ k * z ^ (a + k) / (k ! * (a + k)))
      (Gamma a - upperIncompleteGamma a z) := by
  rw [← eq_sub_of_add_eq' (upperIncompleteGamma_add_lowerIncompleteGamma ha hz)]
  exact hasSum_lowerIncompleteGamma ha z

/-- **DLMF 8.7.3**, second form: `Γ(a, z) = Γ(a) (1 − z^a e^{−z} ∑ zᵏ / Γ(a + k + 1))` for
`a ∉ −ℕ` and `z` in the slit plane. -/
theorem hasSum_Gamma_sub_upperIncompleteGamma_cexp {a z : ℂ} (ha : ∀ n : ℕ, a ≠ -n)
    (hz : z ∈ slitPlane) :
    HasSum (fun k : ℕ => Gamma a * z ^ a * cexp (-z) * z ^ k / Gamma (a + k + 1))
      (Gamma a - upperIncompleteGamma a z) := by
  rw [← eq_sub_of_add_eq' (upperIncompleteGamma_add_lowerIncompleteGamma ha hz),
    lowerIncompleteGamma_def]
  exact ((hasSum_regularizedGamma a z).mul_left (Gamma a)).congr_fun fun k => by ring

/-- For `t ∈ [0, 1]`, `‖t y‖ ≤ ‖y‖`. -/
private theorem norm_ofReal_mul_le {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (y : ℂ) :
    ‖(t : ℂ) * y‖ ≤ ‖y‖ := by
  rw [norm_mul, norm_real, Real.norm_of_nonneg ht.1]
  exact mul_le_of_le_one_left (norm_nonneg y) ht.2

/-- For real `x` and `‖y‖ < x`, the segment from `x` to `x + y` lies in the right half plane,
hence in the slit plane. -/
private theorem ofReal_add_mul_mem_slitPlane {x : ℝ} {y : ℂ} (hy : ‖y‖ < x) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : (x : ℂ) + t * y ∈ slitPlane := by
  refine mem_slitPlane_iff.mpr (Or.inl ?_)
  rw [add_re, ofReal_re]
  linarith [(abs_le.mp (abs_re_le_norm ((t : ℂ) * y))).1, norm_ofReal_mul_le ht y]

/-- The binomial series of `(1 + t y / x)^{a−1}` integrates termwise along the segment from `x`
to `x + y`, for real `x` and `|y| < x`. -/
private theorem hasSum_integral_binomialSeries (a : ℂ) {x : ℝ} {y : ℂ} (hy : ‖y‖ < x) :
    HasSum (fun n : ℕ => ∫ t in (0 : ℝ)..1, y * cexp (-((x : ℂ) + t * y)) * (x : ℂ) ^ (a - 1) *
        (Ring.choose (a - 1) n * ((t : ℂ) * y / x) ^ n))
      (∫ t in (0 : ℝ)..1, y * (((x : ℂ) + t * y) ^ (a - 1) * cexp (-((x : ℂ) + t * y)))) := by
  have hx : 0 < x := (norm_nonneg y).trans_lt hy
  -- on the segment, `t y / x` lies in the disc of radius `ρ = |y| / x < 1`
  set ρ : ℝ≥0 := ⟨‖y‖ / x, by positivity⟩
  have hρ1 : (ρ : ℝ) < 1 := (div_lt_one hx).mpr hy
  have hsmall (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : ‖(t : ℂ) * y / x‖ ≤ ρ := by
    rw [norm_div, norm_real, Real.norm_of_nonneg hx.le]
    exact div_le_div_of_nonneg_right (norm_ofReal_mul_le ht y) hx.le
  have hIoc {t : ℝ} (ht : t ∈ Ι (0 : ℝ) 1) : t ∈ Set.Icc (0 : ℝ) 1 :=
    Ioc_subset_Icc_self (by rwa [uIoc_of_le zero_le_one] at ht)
  -- the binomial series of `(1 + t y / x)^{a − 1}` on the segment
  have hpt (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : HasSum (fun n => y * cexp (-((x : ℂ) + t * y)) *
      (x : ℂ) ^ (a - 1) * (Ring.choose (a - 1) n * ((t : ℂ) * y / x) ^ n))
      (y * (((x : ℂ) + t * y) ^ (a - 1) * cexp (-((x : ℂ) + t * y)))) := by
    have hw : (t : ℂ) * y / x ∈ Metric.eball (0 : ℂ) 1 := by
      rw [← ENNReal.ofReal_one, Metric.eball_ofReal]
      simpa using (hsmall t ht).trans_lt hρ1
    have h := (one_add_cpow_hasFPowerSeriesOnBall_zero (a := a - 1)).hasSum hw
    simp only [binomialSeries, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul,
      zero_add] at h
    have hsplit : (x : ℂ) + t * y = x * (1 + t * y / x) := by
      field_simp [ofReal_ne_zero.mpr hx.ne']
    rw [hsplit, TauCeti.ofReal_mul_cpow hx.le, ← hsplit]
    convert h.mul_left (y * cexp (-((x : ℂ) + t * y)) * (x : ℂ) ^ (a - 1)) using 1
    ring
  -- a summable bound, uniform on the segment
  have hsum : Summable fun n : ℕ => ‖(Ring.choose (a - 1) n : ℂ)‖ * (ρ : ℝ) ^ n := by
    have h := (binomialSeries ℂ (a - 1)).summable_norm_mul_pow (r := ρ)
      ((ENNReal.coe_lt_one_iff.mpr (by exact_mod_cast hρ1)).trans_le binomialSeries_radius_ge_one)
    simpa only [binomialSeries, FormalMultilinearSeries.ofScalars_norm] using h
  have hbound (n : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      ‖y * cexp (-((x : ℂ) + t * y)) * (x : ℂ) ^ (a - 1) *
        (Ring.choose (a - 1) n * ((t : ℂ) * y / x) ^ n)‖ ≤
      ‖y‖ * Real.exp ‖y‖ * ‖(x : ℂ) ^ (a - 1)‖ * (‖(Ring.choose (a - 1) n : ℂ)‖ * (ρ : ℝ) ^ n) := by
    have hE : ‖cexp (-((x : ℂ) + t * y))‖ ≤ Real.exp ‖y‖ := by
      rw [norm_exp, Real.exp_le_exp, neg_re, add_re, ofReal_re]
      linarith [(abs_le.mp (abs_re_le_norm ((t : ℂ) * y))).1, norm_ofReal_mul_le ht y]
    have := hsmall t ht
    simp only [norm_mul, norm_pow]
    gcongr
  exact intervalIntegral.hasSum_integral_of_dominated_convergence
    (fun n _ => ‖y‖ * Real.exp ‖y‖ * ‖(x : ℂ) ^ (a - 1)‖ *
      (‖(Ring.choose (a - 1) n : ℂ)‖ * (ρ : ℝ) ^ n))
    (fun n => (by fun_prop : Continuous fun t : ℝ => y * cexp (-((x : ℂ) + t * y)) *
      (x : ℂ) ^ (a - 1) * (Ring.choose (a - 1) n * ((t : ℂ) * y / x) ^ n)).aestronglyMeasurable)
    (fun n => .of_forall fun t ht => hbound n t (hIoc ht))
    (.of_forall fun _ _ => hsum.mul_left _) intervalIntegrable_const
    (.of_forall fun t ht => hpt t (hIoc ht))

/-- The `n`-th term of the binomial series in DLMF 8.7.2, integrated along the segment from `x`
to `x + y`: `∫₀¹ y e^{−(x + t y)} x^{a−1} (a − 1 choose n) (t y / x)ⁿ dt` is
`e^{−x} x^{a−1} (1 − a)ₙ / (−x)ⁿ (1 − e^{−y} eₙ(y))`, for every real `x` (at `x = 0` both
sides use Lean's convention `x / 0 = 0`). -/
private theorem integral_binomialSeries_term (a y : ℂ) (x : ℝ) (n : ℕ) :
    ∫ t in (0 : ℝ)..1, y * cexp (-((x : ℂ) + t * y)) * (x : ℂ) ^ (a - 1) *
        (Ring.choose (a - 1) n * ((t : ℂ) * y / x) ^ n) =
      cexp (-x) * (x : ℂ) ^ (a - 1) * (ascPochhammer ℂ n).eval (1 - a) / (-(x : ℂ)) ^ n *
        (1 - cexp (-y) * ∑ k ∈ range (n + 1), y ^ k / k !) := by
  -- `y^{n+1} ∫₀¹ tⁿ e^{−y t} dt = γ(n + 1, y) = n! (1 − e^{−y} eₙ(y))` (DLMF 8.2.1, 8.4.7)
  have hγ := lowerIncompleteGamma_eq_integral (a := (n : ℂ) + 1)
    (by simp only [add_re, natCast_re, one_re]; positivity) y
  rw [lowerIncompleteGamma_natCast_add_one, add_sub_cancel_right] at hγ
  simp only [cpow_natCast] at hγ
  rw [← Nat.cast_add_one, cpow_natCast] at hγ
  -- `n! (a − 1 choose n) (−1)ⁿ = (1 − a)ₙ`
  have hc : (n ! : ℂ) * Ring.choose (a - 1) n * (-1) ^ n = (ascPochhammer ℂ n).eval (1 - a) := by
    rw [TauCeti.Ring.factorial_mul_choose_mul_neg_one_pow, neg_sub]
  have hF : (fun t : ℝ => y * cexp (-((x : ℂ) + t * y)) * (x : ℂ) ^ (a - 1) *
      (Ring.choose (a - 1) n * ((t : ℂ) * y / x) ^ n)) = fun t : ℝ =>
      cexp (-x) * (x : ℂ) ^ (a - 1) * Ring.choose (a - 1) n / x ^ n *
        (y ^ (n + 1) * ((t : ℂ) ^ n * cexp (-(y * t)))) := by
    funext t
    rw [neg_add, Complex.exp_add, div_pow, mul_pow, mul_comm (t : ℂ) y]
    ring
  rw [hF, intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, ← hγ,
    neg_pow, ← hc]
  field_simp

/-- **DLMF 8.7.2** for the upper function: for every `a`, real `x` and complex `y` with
`|y| < x`,
`Γ(a, x) − Γ(a, x + y) = e^{−x} x^{a−1} ∑ (1 − a)ₙ / (−x)ⁿ (1 − e^{−y} eₙ(y))`, where
`eₙ(y) = ∑_{k=0}^n yᵏ / k!`. -/
theorem hasSum_upperIncompleteGamma_sub_upperIncompleteGamma_add (a : ℂ) {x : ℝ} {y : ℂ}
    (hy : ‖y‖ < x) :
    HasSum (fun n : ℕ => cexp (-x) * (x : ℂ) ^ (a - 1) * (ascPochhammer ℂ n).eval (1 - a) /
        (-(x : ℂ)) ^ n * (1 - cexp (-y) * ∑ k ∈ range (n + 1), y ^ k / k !))
      (upperIncompleteGamma a x - upperIncompleteGamma a (x + y)) := by
  rw [upperIncompleteGamma_sub_upperIncompleteGamma_add_eq_integral a
    fun _ ht => ofReal_add_mul_mem_slitPlane hy ht]
  exact (hasSum_integral_binomialSeries a hy).congr_fun fun n =>
    (integral_binomialSeries_term a y x n).symm

/-- **DLMF 8.7.2** for the lower function: for `a ∉ −ℕ`, real `x` and complex `y` with
`|y| < x`,
`γ(a, x + y) − γ(a, x) = e^{−x} x^{a−1} ∑ (1 − a)ₙ / (−x)ⁿ (1 − e^{−y} eₙ(y))`, where
`eₙ(y) = ∑_{k=0}^n yᵏ / k!`. -/
theorem hasSum_lowerIncompleteGamma_add_sub_lowerIncompleteGamma {a : ℂ}
    (ha : ∀ n : ℕ, a ≠ -n) {x : ℝ} {y : ℂ} (hy : ‖y‖ < x) :
    HasSum (fun n : ℕ => cexp (-x) * (x : ℂ) ^ (a - 1) * (ascPochhammer ℂ n).eval (1 - a) /
        (-(x : ℂ)) ^ n * (1 - cexp (-y) * ∑ k ∈ range (n + 1), y ^ k / k !))
      (lowerIncompleteGamma a (x + y) - lowerIncompleteGamma a x) := by
  have hx : 0 < x := (norm_nonneg y).trans_lt hy
  have hmem : (x : ℂ) + y ∈ slitPlane := by
    simpa using ofReal_add_mul_mem_slitPlane hy (right_mem_Icc.mpr zero_le_one)
  have h1 := upperIncompleteGamma_add_lowerIncompleteGamma ha (ofReal_mem_slitPlane.mpr hx)
  have h2 := upperIncompleteGamma_add_lowerIncompleteGamma ha hmem
  convert hasSum_upperIncompleteGamma_sub_upperIncompleteGamma_add a hy using 1
  linear_combination h2 - h1

end Complex
