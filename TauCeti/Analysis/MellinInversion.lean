/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Analysis.MellinInversion
public import Mathlib.RingTheory.Polynomial.Pochhammer
public import TauCeti.Analysis.Contour.Residue.Basic
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Topology.Algebra.Polynomial
import TauCeti.Analysis.Contour.Residue.Rectangle
import TauCeti.Analysis.Complex.NormSq
import TauCeti.Analysis.MellinTransform
import TauCeti.Analysis.SpecialFunctions.ImproperIntegrals
import TauCeti.Analysis.SpecialFunctions.Pochhammer
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Norm bounds, contour shifts, and the first-order cutoff for Mellin inversion

Mathlib's `mellinInv σ f y` is `(1 / 2π) ∫ y^{-(σ + i t)} • f(σ + i t) dt`. For `y > 0`, the factor
`t ↦ y^{-(σ + i t)}` is continuous of constant norm `y^{-σ}`. Hence the integrand is integrable
whenever `f` is integrable on the vertical line `Re s = σ`, and the norm of `mellinInv σ f y` is at
most `(y^{-σ} / 2π) ∫ ‖f(σ + i t)‖ dt`.

When `f : ℂ → ℂ` is meromorphic in a strip `σ₀ ≤ Re z ≤ σ₁` with finitely many poles `S` inside the
open strip `σ₀ < Re z < σ₁`, integrable on both boundary lines, and decays on horizontal segments at
heights `±T`, applying
`TauCeti.Contour.integral_add_mul_I_sub_integral_add_mul_I_eq_two_pi_mul_sum_residue`
to `z ↦ x^{-z} f(z)` shifts the Mellin inversion contour across `S`:

`mellinInv σ₁ f x = mellinInv σ₀ f x + ∑_{s ∈ S} Res_s (z ↦ x^{-z} f(z))`.

This file also evaluates the Mellin inverse of the first-order Perron kernel `1 / (s(s + 1))`. The
kernel is used for sums smoothed by `1 - n/x`. The migration motivating this computation
is the Prime Number Theorem and more project by Alex Kontorovich, Terence Tao and contributors,
`PrimeNumberTheoremAnd/PerronFormula.lean` (`Perron.formulaLtOne`, `Perron.formulaGtOne`). The proof
here composes Mathlib's interval-power Mellin transforms and Mellin inversion, independently of
that project's contour argument.

The vertical-line bound generalizes the first-order estimates
`Perron.vertIntBound` and `Perron.vertIntBoundLeft` in the same PNT+ development. Its two endpoint
margins preserve unequal coefficients and give Cauchy-integral control of outward real lines.

## Main results

* `Complex.VerticalIntegrable.integrable_cpow_smul`: the integrand of `mellinInv σ f y` is
  integrable for `y > 0` when `VerticalIntegrable f σ`.
* `TauCeti.mellinInv_zero`: `mellinInv σ f 0 = 0`.
* `TauCeti.norm_mellinInv_le`: `‖mellinInv σ f x‖ ≤ (x^{-σ} / 2π) ∫ ‖f(σ + i t)‖ dt` for `x ≥ 0`.
* `TauCeti.mellinInv_sub_mellinInv_eq_sum_residue`: shifting `mellinInv` from `σ₁` to `σ₀` for
  `x ≥ 0` when the horizontal segment integrals tend to `0`.
* `TauCeti.mellinInv_eq_mellinInv_add_sum_residue_of_norm_le`: shifting `mellinInv` for `x ≥ 0`
  under a uniform norm decay bound on horizontal segments.
* `TauCeti.mellinInv_inv_mul_add_one`: its inverse Mellin transform is `max (1 - x) 0` for
  positive `x`, on every line `Re s = c > 0`.
* `TauCeti.integral_cpow_div_mul_add_one`: its integral is `2π * max (1 - 1/x) 0` for
  positive `x` and `c`. At the cutoff `x = 1` this value is zero.
* `TauCeti.mellinInv_isLittleO_nhdsGT_zero`, `TauCeti.mellinInv_isLittleO_atTop`: the
  Riemann–Lebesgue estimates `mellinInv σ G x = o(x^{-σ})` as `x → 0+` (DLMF 2.5.7) and as
  `x → +∞`, both from `TauCeti.mellinInv_isLittleO_of_tendsto_log`. Mathlib writes
  `mellinInv σ G x` as `x^{-σ}` times a Fourier transform of `G` on the line `Re z = σ`,
  evaluated at `log x`, and the Riemann–Lebesgue lemma applies to it.

* `TauCeti.integrable_and_integral_norm_cpow_div_ascPochhammer_le`: absolute convergence and a
  full-line L¹ bound for all-order Perron kernels, with separate first/last-factor margins.

## References

* E. C. Titchmarsh, *The Theory of Functions*, §9.5.
* H. Iwaniec, E. Kowalski, *Analytic Number Theory*, §5.9.

The Riemann–Lebesgue estimates follow the lean-DLMF project
(<https://github.com/bjbraams/lean-DLMF>), file
`DLMF/AsymptoticApproximations/Mellin/Transforms.lean`.
-/

public section

open Real Set MeasureTheory Filter
open scoped Interval Topology
open Complex hiding exp continuous_exp

namespace Complex

/-- If `f` is integrable on the vertical line `Re s = σ`, then so is the integrand
`t ↦ y^{-(σ + i t)} • f(σ + i t)` of the Mellin inversion integral `mellinInv σ f y`, for
`y > 0`. -/
theorem VerticalIntegrable.integrable_cpow_smul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {f : ℂ → E} {σ : ℝ} (hf : VerticalIntegrable f σ) {y : ℝ} (hy : 0 < y) :
    Integrable fun t : ℝ ↦ (y : ℂ) ^ (-(σ + t * I)) • f (σ + t * I) := by
  -- `t ↦ y^{-(σ + i t)}` is continuous of constant norm `y^{-σ}`
  refine hf.bdd_smul (y ^ (-σ)) ?_ (Eventually.of_forall fun t ↦ ?_)
  · exact (Continuous.const_cpow (by fun_prop)
      (Or.inl (ofReal_ne_zero.mpr hy.ne'))).aestronglyMeasurable
  · rw [norm_cpow_eq_rpow_re_of_pos hy]
    simp

end Complex

namespace TauCeti

/-- At `x = 0`, `mellinInv σ f 0 = 0` for every `σ` and `f`, since `0^{-(σ + i y)} = 0` for every
`y ≠ 0`. -/
@[simp]
theorem mellinInv_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (σ : ℝ) (f : ℂ → E) : mellinInv σ f 0 = 0 := by
  have hae : (fun y : ℝ ↦ ((0 : ℝ) : ℂ) ^ (-(σ + y * I)) • f (σ + y * I)) =ᵐ[volume]
      fun _ ↦ (0 : E) := by
    filter_upwards [ae_iff.mpr (by simp : volume {y : ℝ | ¬ y ≠ 0} = 0)] with y hy
    have hne : -(σ + y * I) ≠ 0 := fun h ↦ hy (by simpa using congrArg im h)
    rw [ofReal_zero, zero_cpow hne, zero_smul]
  rw [mellinInv, integral_congr_ae hae, integral_zero, smul_zero]

/-- For `x ≥ 0`, the Mellin inverse on `Re s = σ` satisfies
`‖mellinInv σ f x‖ ≤ (x^{-σ} / 2π) ∫ ‖f(σ + i t)‖ dt`. No integrability assumption on `f` is needed,
as non-integrable integrands have Bochner integral `0`. -/
theorem norm_mellinInv_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (σ : ℝ) (f : ℂ → E) {x : ℝ} (hx : 0 ≤ x) :
    ‖mellinInv σ f x‖ ≤ x ^ (-σ) / (2 * π) * ∫ t : ℝ, ‖f (σ + t * I)‖ := by
  rcases hx.eq_or_lt with rfl | hx
  · rw [mellinInv_zero, norm_zero]
    exact mul_nonneg (div_nonneg (Real.rpow_nonneg le_rfl _) (by positivity))
      (integral_nonneg fun _ ↦ norm_nonneg _)
  rw [mellinInv, norm_smul, Real.norm_of_nonneg (by positivity)]
  have hnorm (t : ℝ) :
      ‖(x : ℂ) ^ (-(σ + t * I)) • f (σ + t * I)‖ = x ^ (-σ) * ‖f (σ + t * I)‖ := by
    rw [norm_smul, norm_cpow_eq_rpow_re_of_pos hx]
    simp
  calc (1 / (2 * π)) * ‖∫ y : ℝ, (x : ℂ) ^ (-(σ + y * I)) • f (σ + y * I)‖
      ≤ (1 / (2 * π)) * ∫ y : ℝ, ‖(x : ℂ) ^ (-(σ + y * I)) • f (σ + y * I)‖ :=
        mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity)
    _ = x ^ (-σ) / (2 * π) * ∫ t : ℝ, ‖f (σ + t * I)‖ := by
        simp_rw [hnorm, integral_const_mul]
        ring

/-- **Shifting a Mellin inversion contour across poles.** Let `σ₀ ≤ σ₁` and `x ≥ 0`. Suppose `f` is
analytic on `σ₀ ≤ Re z ≤ σ₁` away from a finite set `S` contained in `σ₀ < Re z < σ₁`, meromorphic
at each point of `S`, and vertically integrable on `Re z = σ₀` and `Re z = σ₁`. If the horizontal
segment integrals of `z ↦ x^{-z} f(z)` at heights `±T` tend to `0` as `T → +∞`, then
`mellinInv σ₁ f x - mellinInv σ₀ f x` equals the sum of the residues of `z ↦ x^{-z} f(z)` over
`S`. -/
theorem mellinInv_sub_mellinInv_eq_sum_residue
    {f : ℂ → ℂ} {S : Finset ℂ} {σ₀ σ₁ x : ℝ} (hσ : σ₀ ≤ σ₁) (hx : 0 ≤ x)
    (hf : ∀ z : ℂ, z.re ∈ Icc σ₀ σ₁ → z ∉ S → AnalyticAt ℂ f z)
    (hmero : ∀ s ∈ S, MeromorphicAt f s)
    (hS : ∀ s ∈ S, s.re ∈ Ioo σ₀ σ₁)
    (hint₀ : VerticalIntegrable f σ₀) (hint₁ : VerticalIntegrable f σ₁)
    (hbot : Tendsto
      (fun T : ℝ ↦ ∫ u : ℝ in σ₀..σ₁, (x : ℂ) ^ (-((u : ℂ) - T * I)) * f (u - T * I))
      atTop (𝓝 0))
    (htop : Tendsto
      (fun T : ℝ ↦ ∫ u : ℝ in σ₀..σ₁, (x : ℂ) ^ (-((u : ℂ) + T * I)) * f (u + T * I))
      atTop (𝓝 0)) :
    mellinInv σ₁ f x - mellinInv σ₀ f x =
      ∑ s ∈ S, Contour.residue (fun z ↦ (x : ℂ) ^ (-z) * f z) s := by
  rcases hx.eq_or_lt with rfl | hx
  · simp
  have hx_slit : (x : ℂ) ∈ slitPlane := ofReal_mem_slitPlane.mpr hx
  have hcpow (z : ℂ) : AnalyticAt ℂ (fun w : ℂ ↦ (x : ℂ) ^ (-w)) z :=
    analyticAt_const.cpow (by fun_prop) hx_slit
  have hshift := Contour.integral_add_mul_I_sub_integral_add_mul_I_eq_two_pi_mul_sum_residue
    (f := fun z ↦ (x : ℂ) ^ (-z) * f z) hσ
    (fun z hz hzS ↦ (hcpow z).mul (hf z hz hzS))
    (fun s hs ↦ (hcpow s).meromorphicAt.mul (hmero s hs)) hS
    (by simpa only [VerticalIntegrable, smul_eq_mul] using hint₀.integrable_cpow_smul hx)
    (by simpa only [VerticalIntegrable, smul_eq_mul] using hint₁.integrable_cpow_smul hx)
    hbot htop
  rw [mellinInv, mellinInv, ← smul_sub, real_smul]
  simp only [smul_eq_mul, hshift]
  push_cast
  field_simp [pi_ne_zero]

/-- **Shifting a Mellin inversion contour under uniform horizontal decay.** If `‖f(u ± i T)‖ ≤ B T`
on `u ∈ [σ₀, σ₁]` eventually as `T → +∞` with `B T → 0`, then for `x ≥ 0` the horizontal segment
integrals vanish and
`mellinInv σ₁ f x = mellinInv σ₀ f x + ∑ s ∈ S, residue (fun z ↦ x^{-z} f z) s`. -/
theorem mellinInv_eq_mellinInv_add_sum_residue_of_norm_le
    {f : ℂ → ℂ} {S : Finset ℂ} {σ₀ σ₁ x : ℝ} {B : ℝ → ℝ} (hσ : σ₀ ≤ σ₁) (hx : 0 ≤ x)
    (hf : ∀ z : ℂ, z.re ∈ Icc σ₀ σ₁ → z ∉ S → AnalyticAt ℂ f z)
    (hmero : ∀ s ∈ S, MeromorphicAt f s)
    (hS : ∀ s ∈ S, s.re ∈ Ioo σ₀ σ₁)
    (hint₀ : VerticalIntegrable f σ₀) (hint₁ : VerticalIntegrable f σ₁)
    (hB : Tendsto B atTop (𝓝 0))
    (hbound : ∀ᶠ (T : ℝ) in atTop, ∀ u ∈ Icc σ₀ σ₁,
      ‖f ((u : ℂ) + T * I)‖ ≤ B T ∧ ‖f ((u : ℂ) - T * I)‖ ≤ B T) :
    mellinInv σ₁ f x =
      mellinInv σ₀ f x + ∑ s ∈ S, Contour.residue (fun z ↦ (x : ℂ) ^ (-z) * f z) s := by
  set M : ℝ := max (x ^ (-σ₀)) (x ^ (-σ₁))
  have hM0 : 0 ≤ M := le_max_of_le_left (Real.rpow_nonneg hx _)
  have hcpow {z : ℂ} (hre : z.re ∈ Icc σ₀ σ₁) (him : z.im ≠ 0) : ‖(x : ℂ) ^ (-z)‖ ≤ M := by
    rcases hx.eq_or_lt with rfl | hx
    · have hne : -z ≠ 0 := fun h ↦ him (by simpa using congrArg im h)
      simpa [zero_cpow hne] using hM0
    · rw [norm_cpow_eq_rpow_re_of_pos hx, neg_re]
      rcases le_or_gt 1 x with hx1 | hx1
      · exact (Real.rpow_le_rpow_of_exponent_le hx1 (neg_le_neg hre.1)).trans (le_max_left _ _)
      · exact (Real.rpow_le_rpow_of_exponent_ge hx hx1.le (neg_le_neg hre.2)).trans
          (le_max_right _ _)
  have hseg {s : ℝ → ℂ} (hre : ∀ T u : ℝ, ((u : ℂ) + s T).re = u)
      (him : ∀ᶠ T in atTop, ∀ u : ℝ, ((u : ℂ) + s T).im ≠ 0)
      (hg : ∀ᶠ T in atTop, ∀ u ∈ Icc σ₀ σ₁, ‖f ((u : ℂ) + s T)‖ ≤ B T) :
      Tendsto (fun T : ℝ ↦ ∫ u : ℝ in σ₀..σ₁,
        (x : ℂ) ^ (-((u : ℂ) + s T)) * f ((u : ℂ) + s T)) atTop (𝓝 0) :=
    intervalIntegral.tendsto_integral_nhds_zero_of_ae_norm_le (by simpa using hB.const_mul M) <|
      (him.and hg).mono fun T ⟨hTim, hTB⟩ ↦ Eventually.of_forall fun u hu ↦ by
        have hu' : u ∈ Icc σ₀ σ₁ := Ioc_subset_Icc_self (by rwa [uIoc_of_le hσ] at hu)
        rw [norm_mul]
        exact mul_le_mul (hcpow (by simpa [hre T u] using hu') (hTim u)) (hTB u hu')
          (norm_nonneg _) hM0
  rw [← sub_eq_iff_eq_add']
  refine mellinInv_sub_mellinInv_eq_sum_residue hσ hx hf hmero hS hint₀ hint₁ ?_ ?_
  · simpa only [sub_eq_add_neg] using hseg (s := fun T ↦ -(T * I)) (by simp)
      ((eventually_ne_atTop (0 : ℝ)).mono fun T hT u ↦ by simpa using hT)
      (hbound.mono fun T hT u hu ↦ (hT u hu).2)
  · exact hseg (s := fun T ↦ T * I) (by simp)
      ((eventually_ne_atTop (0 : ℝ)).mono fun T hT u ↦ by simpa using hT)
      (hbound.mono fun T hT u hu ↦ (hT u hu).1)

/-- The all-order Perron kernel is integrable and its full-line L¹ norm is bounded by the
mixed square-root majorant determined by its first and last factors.

The positive margins `a` and `b` bound `|c|` and `|c + j|` from below. Every intermediate real
factor has absolute value at least one, so discarding those factors only increases the bound.
The real part `c` may be positive or negative. For `j = 1` the intermediate condition is empty,
and every line away from `0` and `-1` admits such margins. Zero input is included.

Keeping both margins separate preserves unequal majorants; taking their minimum gives a
scaled Cauchy majorant useful when the vertical line moves outwards. -/
theorem integrable_and_integral_norm_cpow_div_ascPochhammer_le
    (j : ℕ) (hj : 1 ≤ j) {x c a b : ℝ} (hx : 0 ≤ x) (ha : 0 < a) (hb : 0 < b)
    (hac : a ≤ |c|) (hbc : b ≤ |c + j|)
    (hmid : ∀ k : ℕ, 0 < k → k < j → 1 ≤ |c + k|) :
    Integrable (fun t : ℝ ↦ (x : ℂ) ^ ((c : ℂ) + t * I) /
      (ascPochhammer ℂ (j + 1)).eval ((c : ℂ) + t * I)) ∧
    (∫ t : ℝ, ‖(x : ℂ) ^ ((c : ℂ) + t * I) /
      (ascPochhammer ℂ (j + 1)).eval ((c : ℂ) + t * I)‖) ≤
      x ^ c * ∫ t : ℝ, 1 /
        (Real.sqrt (a ^ 2 + t ^ 2) * Real.sqrt (b ^ 2 + t ^ 2)) := by
  have hc : c ≠ 0 := abs_pos.mp (ha.trans_le hac)
  have hden (t : ℝ) : Real.sqrt (a ^ 2 + t ^ 2) * Real.sqrt (b ^ 2 + t ^ 2) ≤
      ‖(ascPochhammer ℂ (j + 1)).eval ((c : ℂ) + t * I)‖ :=
    (mul_le_mul (Complex.sqrt_sq_add_sq_le_norm_add_mul_I ha.le hac)
      (Complex.sqrt_sq_add_sq_le_norm_add_mul_I hb.le hbc)
      (Real.sqrt_nonneg _) (norm_nonneg _)).trans
        (norm_endpoints_le_norm_ascPochhammer_eval j hj c t hmid)
  have hne (t : ℝ) : (ascPochhammer ℂ (j + 1)).eval ((c : ℂ) + t * I) ≠ 0 := by
    apply norm_pos_iff.mp
    exact lt_of_lt_of_le (by positivity) (hden t)
  rcases hx.eq_or_lt with rfl | hx
  · have hz (t : ℝ) : (c : ℂ) + t * I ≠ 0 := by
      intro h
      exact hc (by simpa using congrArg Complex.re h)
    simp only [Complex.ofReal_zero, Complex.zero_cpow (hz _), zero_div, norm_zero,
      integral_zero, Real.zero_rpow hc, zero_mul]
    exact ⟨integrable_zero ℝ ℂ volume, le_rfl⟩
  have hmajor := (integrable_one_div_sqrt_mul_sqrt ha hb).const_mul (x ^ c)
  have hcont : Continuous (fun t : ℝ ↦ (x : ℂ) ^ ((c : ℂ) + t * I) /
      (ascPochhammer ℂ (j + 1)).eval ((c : ℂ) + t * I)) :=
    (Continuous.const_cpow (by fun_prop) (Or.inl (ofReal_ne_zero.mpr hx.ne'))).div
      ((Polynomial.continuous _).comp (by fun_prop)) hne
  have hpoint (t : ℝ) : ‖(x : ℂ) ^ ((c : ℂ) + t * I) /
      (ascPochhammer ℂ (j + 1)).eval ((c : ℂ) + t * I)‖ ≤
      x ^ c * (1 / (Real.sqrt (a ^ 2 + t ^ 2) * Real.sqrt (b ^ 2 + t ^ 2))) := by
    rw [norm_div, norm_cpow_eq_rpow_re_of_pos hx]
    simp only [add_re, ofReal_re, re_ofReal_mul, I_re, mul_zero, add_zero]
    rw [mul_one_div]
    exact div_le_div_of_nonneg_left (Real.rpow_nonneg hx.le _) (by positivity) (hden t)
  have hint := hmajor.mono' hcont.aestronglyMeasurable (Eventually.of_forall hpoint)
  refine ⟨hint, ?_⟩
  simpa only [integral_const_mul] using
    integral_mono hint.norm hmajor hpoint

/-- The inverse Mellin transform of `1 / (s(s+1))` is the continuous first-order cutoff. -/
theorem mellinInv_inv_mul_add_one {c x : ℝ} (hc : 0 < c) (hx : 0 < x) :
    mellinInv c (fun s : ℂ ↦ (s * (s + 1))⁻¹) x = (max (1 - x) 0 : ℝ) := by
  have hm (t : ℝ) : mellin (fun u : ℝ ↦ ((max (1 - u) 0 : ℝ) : ℂ)) ((c : ℂ) + t * I) =
      ((((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1))⁻¹) :=
    (hasMellin_max_one_sub_zero (by simpa using hc)).2
  have hv : VerticalIntegrable (mellin (fun u : ℝ ↦ ((max (1 - u) 0 : ℝ) : ℂ))) c := by
    have hint := integrable_and_integral_norm_cpow_div_ascPochhammer_le 1 (by decide)
      (x := 1) (by norm_num) hc (by linarith : 0 < c + 1)
      (le_abs_self c) (by simpa only [Nat.cast_one] using le_abs_self (c + 1))
      (by intro k hk hk1; omega)
    simpa [VerticalIntegrable, hm, ascPochhammer_succ_eval, ascPochhammer_zero, one_div]
      using hint.1
  have h := mellinInv_mellin_eq c (fun u : ℝ ↦ ((max (1 - u) 0 : ℝ) : ℂ)) hx
    (hasMellin_max_one_sub_zero (by simpa using hc)).1 hv (by fun_prop)
  rw [mellinInv] at h ⊢
  simpa only [hm] using h

private lemma riesz_integrand_eq {x : ℝ} (hx : 0 ≤ x) (s : ℂ) :
    ((x⁻¹ : ℝ) : ℂ) ^ (-s) • (s * (s + 1))⁻¹ = (x : ℂ) ^ s / (s * (s + 1)) := by
  rw [Complex.ofReal_inv, Complex.inv_cpow_ofReal_nonneg hx, Complex.cpow_neg, inv_inv,
    smul_eq_mul, ← div_eq_mul_inv]

/-- The integral of `x^s / (s(s+1))` on a positive vertical line is the continuous cutoff
weight times `2π`. In particular, its value at `x = 1` is zero. -/
theorem integral_cpow_div_mul_add_one {c x : ℝ} (hc : 0 < c) (hx : 0 < x) :
    (∫ t : ℝ, (x : ℂ) ^ ((c : ℂ) + t * I) /
      (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1))) =
      ((2 * π : ℝ) : ℂ) * (max (1 - x⁻¹) 0 : ℝ) := by
  have h := mellinInv_inv_mul_add_one hc (inv_pos.mpr hx)
  simp only [mellinInv, riesz_integrand_eq hx.le] at h
  have hπ : ((2 * π : ℝ) : ℂ) ≠ 0 := by exact_mod_cast mul_ne_zero two_ne_zero pi_ne_zero
  apply (inv_mul_eq_iff_eq_mul₀ hπ).mp
  simpa only [Complex.real_smul, one_div, Complex.ofReal_inv] using h

section RiemannLebesgue

open Asymptotics
open scoped FourierTransform

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- **The Riemann–Lebesgue estimate for Mellin inversion.** Along any filter on which `x > 0`
eventually and `log x` leaves every compact set, `mellinInv σ G x = o(x^{-σ})`. No hypothesis on
`G` is needed: if `G` is not integrable on the line `Re z = σ`, then `mellinInv σ G x = 0` for
every `x > 0`, so the estimate holds trivially. -/
theorem mellinInv_isLittleO_of_tendsto_log (G : ℂ → E) (σ : ℝ) {l : Filter ℝ}
    (hpos : ∀ᶠ x in l, 0 < x) (hlog : Tendsto Real.log l (cocompact ℝ)) :
    (fun x => mellinInv σ G x) =o[l] fun x => x ^ (-σ) := by
  set g : ℝ → E := fun y => G (σ + 2 * π * y * I)
  have hu : Tendsto (fun x => 𝓕 g (Real.log x)) l (𝓝 0) :=
    (Real.zero_at_infty_fourier g).comp hlog
  have heq : (fun x => mellinInv σ G x) =ᶠ[l]
      fun x => ((x ^ (-σ) : ℝ) : ℂ) • 𝓕 g (Real.log x) := by
    filter_upwards [hpos] with x hx
    rw [mellinInv_eq_fourierInv σ G hx, Real.fourierInv_eq_fourier_neg, neg_neg, ofReal_cpow hx.le,
      ofReal_neg]
  have h : (fun x => mellinInv σ G x) =o[l] fun x => ((x ^ (-σ) : ℝ) : ℂ) := by
    refine IsLittleO.congr' ?_ heq.symm EventuallyEq.rfl
    simpa using (isBigO_refl (fun x : ℝ => ((x ^ (-σ) : ℝ) : ℂ)) l).smul_isLittleO
      ((isLittleO_one_iff ℂ).2 hu)
  refine isLittleO_norm_right.mp ?_
  simpa only [norm_real] using isLittleO_norm_right.mpr h

/-- DLMF 2.5.7: `mellinInv σ G x = o(x^{-σ})` as `x → 0+`. -/
theorem mellinInv_isLittleO_nhdsGT_zero (G : ℂ → E) (σ : ℝ) :
    (fun x => mellinInv σ G x) =o[𝓝[>] 0] fun x => x ^ (-σ) :=
  mellinInv_isLittleO_of_tendsto_log G σ self_mem_nhdsWithin
    (Real.tendsto_log_nhdsGT_zero.mono_right atBot_le_cocompact)

/-- `mellinInv σ G x = o(x^{-σ})` as `x → +∞`, the estimate after a shift of the line of Mellin
inversion to the right. -/
theorem mellinInv_isLittleO_atTop (G : ℂ → E) (σ : ℝ) :
    (fun x => mellinInv σ G x) =o[atTop] fun x => x ^ (-σ) :=
  mellinInv_isLittleO_of_tendsto_log G σ (eventually_gt_atTop 0)
    (Real.tendsto_log_atTop.mono_right atTop_le_cocompact)

end RiemannLebesgue

end TauCeti
