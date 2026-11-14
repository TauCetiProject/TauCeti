/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.NumberTheory.Harmonic.ZetaAsymp
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LSeries.Linearity
import TauCeti.Algebra.BigOperators.Intervals
import TauCeti.NumberTheory.LSeries.Convergence
import TauCeti.NumberTheory.LSeries.SumCoeff

/-!
# The Riemann zeta function at real arguments and on the right half-plane

For a real `s > 1`, Mathlib's `riemannZeta s` is the sum of the complex Dirichlet series
`∑ 1 / n ^ s`. This file records the corresponding statements for the real series: the real
`p`-series `∑ (n + 1) ^ (-s)` sums to the real part of `riemannZeta s`. Together with Mathlib's
`riemannZeta_re_pos_of_one_lt` and `riemannZeta_im_eq_zero_of_one_lt`, this identifies the
real normalizing constant of a `p`-series, as needed for the Zipf law on the positive integers.

The file also proves that `riemannZeta` is measurable, so that families of laws normalized by its
real values are measurable in their parameter.

On the critical strip the series diverges, and the sign of `ζ(σ)` for real `0 < σ < 1` comes from
the alternating series `η(s) = ∑ (-1) ^ (n + 1) n⁻ˢ = (1 - 2 ^ (1 - s)) ζ(s)`. Its partial sums
are `0` or `1`, so partial summation continues it to `Re s > 0` as
`s ∫_1^∞ A(t) t^(-s-1) dt` with `0 ≤ A(t) ≤ 1` and `A = 1` on `[1, 2)`. For real `0 < σ < 1`
this integral is positive while `1 - 2 ^ (1 - σ)` is negative, so `ζ(σ) < 0`. This is the sign
of the zeta factor in the products of L-functions with nonnegative coefficients used in
Siegel's theorem on real zeros.

Euler–Maclaurin summation on `1` gives the first-order integral representation
`riemannZeta₀ s = 1 - s ∫_1^∞ {t} t^(-s-1) dt` on `Re s > 0`, where `riemannZeta₀` is the entire
completion of `ζ(s) - (s - 1)⁻¹`. Since `0 ≤ {t} < 1`, this bounds `‖riemannZeta₀ s‖` by
`1 + ‖s‖ / Re s` and `‖ζ(s)‖` by `‖s - 1‖⁻¹ + 1 + ‖s‖ / Re s` on the whole right half-plane
(including at `s = 1` under Mathlib's junk-value convention).

## Main results

* `TauCeti.hasSum_nat_add_one_rpow_neg_riemannZeta_re`: `∑ (n + 1) ^ (-s) = Re ζ(s)` for `s > 1`;
* `TauCeti.hasSum_nat_rpow_neg_riemannZeta_re`: the same series indexed from `n = 0` with the
  vanishing term `0 ^ (-s)`;
* `TauCeti.measurable_riemannZeta`: the Riemann zeta function is measurable.
* `TauCeti.LSeries_neg_one_pow_add_one_eq_mul_riemannZeta`: the alternating series
  `∑ (-1) ^ (n + 1) n⁻ˢ` is `(1 - 2 ^ (1 - s)) ζ(s)` for `Re s > 1`.
* `TauCeti.one_sub_two_cpow_mul_riemannZeta_eq_mul_integral`: the partial-summation integral of
  the alternating series represents `(1 - 2 ^ (1 - s)) ζ(s)` on `Re s > 0`, `s ≠ 1`.
* `TauCeti.riemannZeta_lt_zero`: `ζ(σ)` is a negative real number for real `0 < σ < 1`.
* `TauCeti.riemannZeta₀_eq_one_sub_mul_integral`: `riemannZeta₀ s = 1 - s ∫_1^∞ {t} t^(-s-1) dt`
  on `Re s > 0`.
* `TauCeti.norm_riemannZeta₀_le` and `TauCeti.norm_riemannZeta_le`: explicit vertical linear
  growth bounds on `Re s > 0`.

## References

* H. Davenport, *Multiplicative Number Theory*, the chapter on Siegel's theorem.
-/

public section

open Complex Filter Finset
open scoped Topology ComplexOrder

namespace TauCeti

/-- For real `s > 1`, the real series `∑ (n + 1) ^ (-s)` sums to the real part of `riemannZeta s`.
-/
theorem hasSum_nat_add_one_rpow_neg_riemannZeta_re {s : ℝ} (hs : 1 < s) :
    HasSum (fun n : ℕ => ((n : ℝ) + 1) ^ (-s)) (riemannZeta s).re := by
  have hsum : Summable fun n : ℕ => ((n : ℝ) + 1) ^ (-s) := by
    simpa using (summable_nat_add_iff 1).2 (Real.summable_nat_rpow.2 (by linarith : -s < -1))
  have hζ : riemannZeta s = ((∑' n : ℕ, ((n : ℝ) + 1) ^ (-s) : ℝ) : ℂ) := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by simpa using hs), ofReal_tsum]
    congr 1 with n
    rw [ofReal_cpow (by positivity), one_div, ← cpow_neg]
    norm_cast
  rw [hζ, ofReal_re]
  exact hsum.hasSum

/-- For real `s > 1`, the real series `∑ n ^ (-s)` over all natural numbers sums to the real part of
`riemannZeta s`; its `n = 0` term is `0 ^ (-s) = 0`. -/
theorem hasSum_nat_rpow_neg_riemannZeta_re {s : ℝ} (hs : 1 < s) :
    HasSum (fun n : ℕ => (n : ℝ) ^ (-s)) (riemannZeta s).re := by
  rw [← hasSum_nat_add_iff' 1]
  simpa [Real.zero_rpow (by linarith : -s ≠ 0)] using
    hasSum_nat_add_one_rpow_neg_riemannZeta_re hs

/-- The Riemann zeta function is measurable: it is continuous away from its pole at `1`. -/
@[fun_prop]
theorem measurable_riemannZeta : Measurable riemannZeta :=
  measurable_of_continuousOn_compl_singleton 1 differentiableOn_riemannZeta.continuousOn

/-- **The alternating zeta series.** On `Re s > 1`, the Dirichlet series
`η(s) = ∑ (-1) ^ (n + 1) n⁻ˢ` equals `(1 - 2 ^ (1 - s)) ζ(s)`. Writing
`(-1) ^ (n + 1) = 2 χ₀(n) - 1` with `χ₀` the principal character modulo `2` gives
`η(s) = 2 (1 - 2⁻ˢ) ζ(s) - ζ(s)`. -/
theorem LSeries_neg_one_pow_add_one_eq_mul_riemannZeta {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n ↦ (-1 : ℂ) ^ (n + 1)) s = (1 - 2 ^ (1 - s)) * riemannZeta s := by
  set χ : DirichletCharacter ℂ 2 := 1
  have hχ : (fun n : ℕ ↦ (-1 : ℂ) ^ (n + 1)) = (2 : ℂ) • (fun n : ℕ ↦ χ n) - 1 := by
    funext n
    rcases Nat.even_or_odd n with h | h
    · have : ¬ IsUnit (n : ZMod 2) := by
        rw [ZMod.natCast_eq_zero_iff_even.mpr h]; exact not_isUnit_zero
      simp [MulChar.map_nonunit χ this, h.add_one.neg_one_pow]
    · rw [Pi.sub_apply, Pi.smul_apply, ZMod.natCast_eq_one_iff_odd.mpr h]
      simp [pow_succ, h.neg_one_pow]; norm_num
  have hL : LSeries ((2 : ℂ) • (fun n : ℕ ↦ χ n) - 1) s = 2 * χ.LFunction s - riemannZeta s := by
    rw [LSeries_sub ((χ.LSeriesSummable_of_one_lt_re hs).smul 2) (LSeriesSummable_one_iff.mpr hs),
      LSeries_smul, LSeries_one_eq_riemannZeta hs, χ.LFunction_eq_LSeries hs]
  have hχζ : χ.LFunction s = (1 - 2 ^ (-s)) * riemannZeta s := by
    simpa [χ, Nat.prime_two.primeFactors] using
      DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta (N := 2) (fun h ↦ by simp [h] at hs)
  have h2 : (2 : ℂ) ^ (1 - s) = 2 * 2 ^ (-s) := by
    rw [sub_eq_add_neg, cpow_add _ _ two_ne_zero, cpow_one]
  rw [hχ, hL, hχζ, h2]
  ring

/-- **Continuation of the alternating zeta series.** On `Re s > 0`, `s ≠ 1`, the function
`(1 - 2 ^ (1 - s)) ζ(s)` is the partial-summation integral `s ∫_1^∞ A(t) t^(-s-1) dt` of the
coefficients `(-1) ^ (k + 1)`, whose partial sums `A(t) = ∑_{1 ≤ k ≤ t} (-1) ^ (k + 1)` are `0` or
`1`. At `s = 1` the left side is `0` while the integral is positive. -/
theorem one_sub_two_cpow_mul_riemannZeta_eq_mul_integral {s : ℂ} (hs : 0 < s.re) (hs₁ : s ≠ 1) :
    (1 - 2 ^ (1 - s)) * riemannZeta s =
      s * ∫ t in Set.Ioi (1 : ℝ), (∑ k ∈ Icc 1 ⌊t⌋₊, (-1 : ℂ) ^ (k + 1)) *
        (t : ℂ) ^ (-(s + 1)) := by
  set G : ℂ → ℂ := fun z ↦ z * ∫ t in Set.Ioi (1 : ℝ),
    (∑ k ∈ Icc 1 ⌊t⌋₊, (-1 : ℂ) ^ (k + 1)) * (t : ℂ) ^ (-(z + 1))
  have hO : (fun n : ℕ ↦ ∑ k ∈ Icc 1 n, (-1 : ℂ) ^ (k + 1)) =O[atTop]
      fun n ↦ (n : ℝ) ^ (0 : ℝ) :=
    Asymptotics.isBigO_iff.mpr ⟨1, Eventually.of_forall fun n ↦ by
      simpa using LSeries.norm_sum_Icc_neg_one_pow_add_one_le (R := ℂ) n⟩
  have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const continuous_re
  have hG : AnalyticOnNhd ℂ (fun z ↦ (z - 1) * G z) {z : ℂ | 0 < z.re} :=
    ((differentiableOn_id.sub_const 1).mul
      (TauCeti.LSeries.differentiableOn_mul_integral_of_isBigO _ hO)).analyticOnNhd hopen
  have hZ : AnalyticOnNhd ℂ (fun z ↦ (1 - 2 ^ (1 - z)) * riemannZeta₁ z) {z : ℂ | 0 < z.re} :=
    (DifferentiableOn.mul (by fun_prop) differentiable_riemannZeta₁.differentiableOn).analyticOnNhd
      hopen
  have heq : (fun z ↦ (z - 1) * G z) =ᶠ[𝓝 2] fun z ↦ (1 - 2 ^ (1 - z)) * riemannZeta₁ z := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
      (by norm_num : (2 : ℂ) ∈ {z : ℂ | 1 < z.re})] with z hz
    have hz₁ : z - 1 ≠ 0 := sub_ne_zero.mpr fun h ↦ by simp [h] at hz
    simp only [G]
    rw [← LSeries_eq_mul_integral _ le_rfl (zero_lt_one.trans hz)
      (LSeriesSummable_of_bounded_of_one_lt_re (m := 1) (fun n _ ↦ by simp) hz) hO,
      LSeries_neg_one_pow_add_one_eq_mul_riemannZeta hz,
      riemannZeta_eq_inv_sub_mul (sub_ne_zero.mp hz₁)]
    field_simp
  have h := hG.eqOn_of_preconnected_of_eventuallyEq hZ (convex_halfSpace_re_gt 0).isPreconnected
    (by norm_num : (2 : ℂ) ∈ {z : ℂ | 0 < z.re}) heq hs
  simp only [G] at h
  rw [riemannZeta_eq_inv_sub_mul hs₁]
  field_simp [sub_ne_zero.mpr hs₁]
  linear_combination -h

/-- The Riemann zeta function is a negative real number at every real point `0 < σ < 1`. -/
theorem riemannZeta_lt_zero {σ : ℝ} (h₀ : 0 < σ) (h₁ : σ < 1) : riemannZeta σ < 0 := by
  set F : ℝ → ℂ := fun t ↦ (∑ k ∈ Icc 1 ⌊t⌋₊, (-1 : ℂ) ^ (k + 1)) * (t : ℂ) ^ (-((σ : ℂ) + 1))
  set g : ℝ → ℝ := fun t ↦ if Even ⌊t⌋₊ then 0 else t ^ (-(σ + 1))
  have hFg : Set.EqOn F (fun t ↦ (g t : ℂ)) (Set.Ioi 1) := fun t ht ↦ by
    simp only [F, g, sum_Icc_neg_one_pow_add_one]
    split_ifs
    · simp
    · rw [one_mul, ofReal_cpow (zero_le_one.trans ht.le), ofReal_neg, ofReal_add, ofReal_one]
  have hFint : MeasureTheory.IntegrableOn F (Set.Ioi 1) :=
    TauCeti.LSeries.integrableOn_sum_mul_cpow_of_isBigO _ (r := 0)
      (Asymptotics.isBigO_iff.mpr ⟨1, Eventually.of_forall fun n ↦ by
        simpa using LSeries.norm_sum_Icc_neg_one_pow_add_one_le (R := ℂ) n⟩) (by simpa using h₀)
  have hgint : MeasureTheory.IntegrableOn g (Set.Ioi 1) := by
    simpa using (hFint.congr_fun hFg measurableSet_Ioi).re
  have hg₀ (t : ℝ) (ht : 0 ≤ t) : 0 ≤ g t := by
    simp only [g]; split_ifs <;> positivity
  have hg : 0 < ∫ t in Set.Ioi (1 : ℝ), g t := by
    have hpos : 0 < ∫ t in (1 : ℝ)..2, g t := by
      refine intervalIntegral.intervalIntegral_pos_of_pos_on ?_ (fun t ht ↦ ?_) one_lt_two
      · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le one_le_two).mpr
          (hgint.mono_set Set.Ioc_subset_Ioi_self)
      · have : ⌊t⌋₊ = 1 := Nat.floor_eq_iff (by linarith [ht.1]) |>.mpr ⟨by simpa using ht.1.le,
          by norm_num; exact ht.2⟩
        simp only [g, this, Nat.not_even_one, ite_false]
        exact Real.rpow_pos_of_pos (by linarith [ht.1]) _
    rw [intervalIntegral.integral_of_le one_le_two] at hpos
    exact hpos.trans_le (MeasureTheory.setIntegral_mono_set hgint
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi fun t ht ↦ hg₀ t (by
        simp only [Set.mem_Ioi] at ht; linarith)) Set.Ioc_subset_Ioi_self.eventuallySubset)
  have hrep := one_sub_two_cpow_mul_riemannZeta_eq_mul_integral (s := σ) (by simpa using h₀)
    (by exact_mod_cast h₁.ne)
  have h2 : (2 : ℂ) ^ (1 - (σ : ℂ)) = ((2 : ℝ) ^ (1 - σ) : ℝ) := by
    rw [ofReal_cpow zero_le_two, ofReal_ofNat, ofReal_sub, ofReal_one]
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hFg, integral_complex_ofReal,
    h2] at hrep
  have hc : 1 - (2 : ℝ) ^ (1 - σ) < 0 := sub_neg.mpr (Real.one_lt_rpow one_lt_two (by linarith))
  have hz : riemannZeta σ = ((σ * ∫ t in Set.Ioi (1 : ℝ), g t) / (1 - 2 ^ (1 - σ)) : ℝ) := by
    have hc' : (1 : ℂ) - ((2 : ℝ) ^ (1 - σ) : ℝ) ≠ 0 := by exact_mod_cast hc.ne
    push_cast
    rw [eq_div_iff hc', ← hrep]
    ring
  rw [hz]
  exact_mod_cast div_neg_of_pos_of_neg (mul_pos h₀ hg) hc

private theorem integrableOn_fract_mul_cpow {s : ℂ} (hs : 0 < s.re) :
    MeasureTheory.IntegrableOn
      (fun t : ℝ ↦ ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))) (Set.Ioi 1) := by
  refine (integrableOn_Ioi_rpow_of_lt (by linarith : -(s.re + 1) < -1) zero_lt_one).mono'
    (((continuous_ofReal.measurable.comp measurable_fract).aestronglyMeasurable.restrict).mul
      ((ContinuousOn.aestronglyMeasurable
        (fun t (ht : t ∈ Set.Ioi (1 : ℝ)) ↦ (continuousAt_ofReal_cpow_const _ _
          (Or.inr (zero_lt_one.trans ht).ne')).continuousWithinAt) measurableSet_Ioi))) ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 < t := zero_lt_one.trans ht
  rw [norm_mul, norm_real, Real.norm_of_nonneg (Int.fract_nonneg t),
    norm_cpow_eq_rpow_re_of_pos ht0]
  simp only [neg_re, add_re, one_re]
  exact mul_le_of_le_one_left (Real.rpow_nonneg ht0.le _) (Int.fract_lt_one t).le

private theorem differentiableOn_integral_fract_mul_cpow :
    DifferentiableOn ℂ
      (fun s : ℂ ↦ ∫ t in Set.Ioi (1 : ℝ), ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)))
      {s : ℂ | 0 < s.re} := by
  set F : ℝ → ℂ := (Set.Ici (1 : ℝ)).indicator fun t ↦ ((Int.fract t : ℝ) : ℂ)
  have hmeas : MeasureTheory.AEStronglyMeasurable F MeasureTheory.volume :=
    ((continuous_ofReal.measurable.comp measurable_fract).indicator
      measurableSet_Ici).aestronglyMeasurable
  have hb (t : ℝ) : ‖F t‖ ≤ 1 := by
    by_cases ht : t ∈ Set.Ici (1 : ℝ) <;>
      simp [F, ht, abs_of_nonneg (Int.fract_nonneg t), (Int.fract_lt_one t).le]
  have hloc : MeasureTheory.LocallyIntegrableOn F (Set.Ioi 0) :=
    ((MeasureTheory.memLp_top_of_bound hmeas 1 (Eventually.of_forall hb)).locallyIntegrable
      le_top).locallyIntegrableOn _
  have hO_top : F =O[atTop] fun t : ℝ ↦ t ^ (-(0 : ℝ)) :=
    Asymptotics.isBigO_iff.mpr ⟨1, Eventually.of_forall fun t ↦ by simpa using hb t⟩
  have hO_zero (c : ℝ) : F =O[𝓝[>] 0] fun t : ℝ ↦ t ^ c := by
    refine Asymptotics.isBigO_iff.mpr ⟨0, ?_⟩
    filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with t ht
    simp [F, Set.indicator_of_notMem (show t ∉ Set.Ici (1 : ℝ) by simp [ht.2.not_ge])]
  have hmellin (s : ℂ) :
      ∫ t in Set.Ioi (1 : ℝ), ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)) = mellin F (-s) := by
    have hEq : Set.EqOn (fun t : ℝ ↦ (t : ℂ) ^ (-s - 1) • F t)
        ((Set.Ici (1 : ℝ)).indicator fun t ↦ ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)))
        (Set.Ioi 0) := fun t _ ↦ by
      by_cases h1 : t ∈ Set.Ici (1 : ℝ)
      · simp only [F, Set.indicator_of_mem h1, smul_eq_mul, mul_comm,
          show -(s + 1) = -s - 1 by ring]
      · simp [F, Set.indicator_of_notMem h1]
    rw [mellin, MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hEq,
      MeasureTheory.setIntegral_indicator measurableSet_Ici,
      Set.inter_eq_right.mpr (Set.Ici_subset_Ioi.mpr zero_lt_one),
      MeasureTheory.integral_Ici_eq_integral_Ioi]
  intro s hs
  simp_rw [hmellin]
  exact ((mellin_differentiableAt_of_isBigO_rpow (a := 0) hloc hO_top
    (by simpa using hs) (hO_zero _)
    (sub_one_lt (-s).re)).comp s differentiableAt_id.neg).differentiableWithinAt

/-- **First-order Euler–Maclaurin continuation of `ζ(s) - (s - 1)⁻¹`.** On the half-plane
`Re s > 0`, the entire function `riemannZeta₀` equals `1 - s ∫_1^∞ {t} t^(-s-1) dt`. -/
theorem riemannZeta₀_eq_one_sub_mul_integral {s : ℂ} (hs : 0 < s.re) :
    riemannZeta₀ s =
      1 - s * ∫ t in Set.Ioi (1 : ℝ), ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
  set G : ℂ → ℂ := fun z ↦
    1 - z * ∫ t in Set.Ioi (1 : ℝ), ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(z + 1))
  have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const continuous_re
  have hG : AnalyticOnNhd ℂ G {z : ℂ | 0 < z.re} :=
    (differentiableOn_const 1 |>.sub
      (differentiableOn_id.mul differentiableOn_integral_fract_mul_cpow)).analyticOnNhd hopen
  have heq : riemannZeta₀ =ᶠ[𝓝 (2 : ℂ)] G := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
      (by norm_num : (2 : ℂ) ∈ {z : ℂ | 1 < z.re})] with z hz
    have hz1 : z ≠ 1 := fun h ↦ by simp [h] at hz
    have hO1 : (fun n : ℕ ↦ ∑ k ∈ Icc 1 n, (1 : ℕ → ℂ) k) =O[atTop]
        fun n ↦ (n : ℝ) ^ (1 : ℝ) := by
      refine Asymptotics.isBigO_iff.mpr ⟨1, Eventually.of_forall fun n ↦ ?_⟩
      simp
    have hstep (t : ℝ) (ht : t ∈ Set.Ioi (1 : ℝ)) :
        (∑ k ∈ Icc 1 ⌊t⌋₊, (1 : ℕ → ℂ) k) * (t : ℂ) ^ (-(z + 1)) =
          (t : ℂ) ^ (-z) - ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(z + 1)) := by
      have ht0 : 0 < t := zero_lt_one.trans ht
      have hfl : ⌊t⌋ = (⌊t⌋₊ : ℤ) := Int.floor_eq_iff.mpr
        ⟨by exact_mod_cast Nat.floor_le ht0.le, by exact_mod_cast Nat.lt_floor_add_one t⟩
      have hfr : (⌊t⌋₊ : ℂ) = (t : ℂ) - ((Int.fract t : ℝ) : ℂ) := by
        have : (⌊t⌋₊ : ℝ) = t - Int.fract t := by rw [Int.fract, hfl, Int.cast_natCast]; ring
        exact_mod_cast this
      have htc : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht0.ne'
      simp only [Pi.one_apply, sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_one,
        hfr, sub_mul]
      rw [neg_add', cpow_sub _ _ htc, cpow_one, mul_div_cancel₀ _ htc]
    have hI : ∫ t in Set.Ioi (1 : ℝ), (∑ k ∈ Icc 1 ⌊t⌋₊, (1 : ℕ → ℂ) k) * (t : ℂ) ^ (-(z + 1)) =
        (z - 1)⁻¹ - ∫ t in Set.Ioi (1 : ℝ), ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(z + 1)) := by
      rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hstep,
        MeasureTheory.integral_sub (integrableOn_Ioi_cpow_of_lt (by simpa using hz) zero_lt_one)
          (integrableOn_fract_mul_cpow (zero_lt_one.trans hz)),
        integral_Ioi_cpow_of_lt (by simpa using hz) zero_lt_one]
      simp only [ofReal_one, one_cpow]
      rw [show -z + 1 = -(z - 1) by ring, neg_div_neg_eq, one_div]
    have hL := LSeries_eq_mul_integral (1 : ℕ → ℂ) zero_le_one hz
      (LSeriesSummable_one_iff.mpr hz) hO1
    rw [LSeries_one_eq_riemannZeta hz, riemannZeta_eq_inv_sub_add hz1, hI] at hL
    have hz1' : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
    field_simp at hL
    exact mul_left_cancel₀ hz1' (by simp only [G]; linear_combination hL)
  exact (differentiable_riemannZeta₀.differentiableOn.analyticOnNhd
    hopen).eqOn_of_preconnected_of_eventuallyEq hG (convex_halfSpace_re_gt 0).isPreconnected
      (by norm_num : (2 : ℂ) ∈ {z : ℂ | 0 < z.re}) heq hs

/-- On the right half-plane `Re s > 0`, `‖riemannZeta₀ s‖ ≤ 1 + ‖s‖ / Re s`. -/
theorem norm_riemannZeta₀_le {s : ℂ} (hs : 0 < s.re) :
    ‖riemannZeta₀ s‖ ≤ 1 + ‖s‖ / s.re := by
  rw [riemannZeta₀_eq_one_sub_mul_integral hs]
  have hint :
      ‖∫ t in Set.Ioi (1 : ℝ), ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))‖ ≤ 1 / s.re := by
    calc
      _ ≤ ∫ t in Set.Ioi (1 : ℝ), t ^ (-(s.re + 1)) := by
        refine MeasureTheory.norm_integral_le_of_norm_le
          (integrableOn_Ioi_rpow_of_lt (by linarith : -(s.re + 1) < -1) zero_lt_one) ?_
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
        have ht0 : 0 < t := zero_lt_one.trans ht
        rw [norm_mul, norm_real, Real.norm_of_nonneg (Int.fract_nonneg t),
          norm_cpow_eq_rpow_re_of_pos ht0]
        simp only [neg_re, add_re, one_re]
        exact mul_le_of_le_one_left (Real.rpow_nonneg ht0.le _) (Int.fract_lt_one t).le
      _ = 1 / s.re := by
        rw [integral_Ioi_rpow_of_lt (by linarith) zero_lt_one, Real.one_rpow]
        ring
  calc
    ‖1 - s * ∫ t in Set.Ioi (1 : ℝ), ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))‖
      ≤ ‖(1 : ℂ)‖ +
          ‖s * ∫ t in Set.Ioi (1 : ℝ), ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))‖ :=
        norm_sub_le _ _
    _ = 1 + ‖s‖ * ‖∫ t in Set.Ioi (1 : ℝ), ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))‖ := by
        rw [norm_one, norm_mul]
    _ ≤ 1 + ‖s‖ * (1 / s.re) := by gcongr
    _ = 1 + ‖s‖ / s.re := by ring

/-- On the right half-plane `Re s > 0`, `‖riemannZeta s‖ ≤ ‖s - 1‖⁻¹ + 1 + ‖s‖ / Re s`. At `s = 1`
the pole term `‖s - 1‖⁻¹` vanishes and Mathlib's value `(γ - log (4π)) / 2` has norm `< 2`. -/
theorem norm_riemannZeta_le {s : ℂ} (hs : 0 < s.re) :
    ‖riemannZeta s‖ ≤ ‖s - 1‖⁻¹ + 1 + ‖s‖ / s.re := by
  rcases eq_or_ne s 1 with rfl | hs1
  · have h : riemannZeta 1 = (((Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) / 2 : ℝ) :
        ℂ) := by
      rw [riemannZeta_one, ofReal_div, ofReal_sub,
        ofReal_log (by positivity : (0 : ℝ) ≤ 4 * Real.pi)]
      norm_cast
    have hlog_pos : 0 < Real.log (4 * Real.pi) :=
      Real.log_pos (by linarith [Real.two_le_pi])
    have hlog_le : Real.log (4 * Real.pi) ≤ 4 := by
      rw [Real.log_le_iff_le_exp (by positivity)]
      have hexp : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      have h16 : (16 : ℝ) ≤ Real.exp 4 := by
        calc (16 : ℝ) = 2 ^ 4 := by norm_num
          _ ≤ (Real.exp 1) ^ 4 := pow_le_pow_left₀ zero_le_two hexp 4
          _ = Real.exp 4 := by rw [← Real.exp_nat_mul]; norm_num
      linarith [Real.pi_le_four]
    rw [h, norm_real, Real.norm_eq_abs]
    simp only [sub_self, norm_zero, inv_zero, zero_add, norm_one, one_re, div_one]
    rw [abs_le]
    constructor <;> linarith [Real.one_half_lt_eulerMascheroniConstant,
      Real.eulerMascheroniConstant_lt_two_thirds]
  · rw [riemannZeta_eq_inv_sub_add hs1]
    calc
      ‖(s - 1)⁻¹ + riemannZeta₀ s‖ ≤ ‖(s - 1)⁻¹‖ + ‖riemannZeta₀ s‖ := norm_add_le _ _
      _ ≤ ‖s - 1‖⁻¹ + (1 + ‖s‖ / s.re) := by rw [norm_inv]; gcongr; exact norm_riemannZeta₀_le hs
      _ = ‖s - 1‖⁻¹ + 1 + ‖s‖ / s.re := by ring

end TauCeti
