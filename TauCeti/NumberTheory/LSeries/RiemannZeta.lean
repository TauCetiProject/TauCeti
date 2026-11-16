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
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LSeries.Linearity
import TauCeti.Algebra.BigOperators.Intervals
import TauCeti.Analysis.MellinTransform.UpperTail
import TauCeti.NumberTheory.LSeries.Convergence
import TauCeti.NumberTheory.LSeries.SumCoeff

/-!
# The Riemann zeta function at real arguments and on the open right half-plane

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

Splitting `⌊t⌋₊ = t - Int.fract t` on `(1, ∞)` similarly continues the regularized function
`riemannZeta₀ s = ζ(s) - (s - 1)⁻¹` to the whole open right half-plane `Re s > 0` (including
`s = 1`) as `1 - s ∫_1^∞ {t} t^{-(s + 1)} dt`, yielding explicit right-half-plane growth bounds
`‖riemannZeta₀ s‖ ≤ 1 + ‖s‖ / Re s` and `‖ζ(s)‖ ≤ ‖s‖ / ‖s - 1‖ + ‖s‖ / Re s` without spurious
denominators on `Re s = 1`.

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
* `TauCeti.riemannZeta₀_eq_one_sub_mul_integral` and `TauCeti.riemannZeta_eq_div_sub_mul_integral`:
  fractional-part continuation of `riemannZeta₀` and `riemannZeta` on `Re s > 0`.
* `TauCeti.norm_riemannZeta₀_le_one_add_div` and `TauCeti.norm_riemannZeta_le_div_add_div`:
  explicit right-half-plane growth bounds on `Re s > 0`.

## References

* H. Davenport, *Multiplicative Number Theory*, Chapters 12 and 21.
* E. C. Titchmarsh, *The Theory of the Riemann Zeta-Function*, §2.1 (2.1.4).
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

section FractionalPartGrowth

open MeasureTheory Asymptotics

/-- **Fractional-part representation of `riemannZeta₀`.** On the open right half-plane `Re s > 0`
(including `s = 1`), the regularized zeta function `riemannZeta₀ s` equals
`1 - s ∫_1^∞ {t} t^{-(s + 1)} dt`. -/
theorem riemannZeta₀_eq_one_sub_mul_integral {s : ℂ} (hs : 0 < s.re) :
    riemannZeta₀ s =
      1 - s * ∫ t in Set.Ioi (1 : ℝ), (↑(Int.fract t) : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
  have hfract_O : (fun t : ℝ ↦ (↑(Int.fract t) : ℂ)) =O[atTop] fun t ↦ t ^ (0 : ℝ) := by
    refine isBigO_iff.mpr ⟨1, Eventually.of_forall fun t ↦ ?_⟩
    simpa [abs_of_nonneg (Int.fract_nonneg t)] using (Int.fract_lt_one t).le
  set G : ℂ → ℂ := fun z ↦
    1 - z * ∫ t in Set.Ioi (1 : ℝ), (↑(Int.fract t) : ℂ) * (t : ℂ) ^ (-(z + 1))
  have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const continuous_re
  have hG : AnalyticOnNhd ℂ G {z : ℂ | 0 < z.re} :=
    ((differentiableOn_const 1).sub
      (differentiableOn_id.mul
        (differentiableOn_integral_mul_cpow_of_isBigO hfract_O))).analyticOnNhd hopen
  have hZ : AnalyticOnNhd ℂ riemannZeta₀ {z : ℂ | 0 < z.re} :=
    differentiable_riemannZeta₀.differentiableOn.analyticOnNhd hopen
  -- On `Re z > 1`, split `⌊t⌋₊ = t - {t}` in the partial-summation integral of `ζ(z)`.
  have heq : riemannZeta₀ =ᶠ[𝓝 (2 : ℂ)] G := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
      (by norm_num : (2 : ℂ) ∈ {z : ℂ | 1 < z.re})] with z hz
    have hz0 : 0 < z.re := zero_lt_one.trans hz
    have hz1 : z ≠ 1 := fun h ↦ by simp [h] at hz
    have hO1 : (fun n : ℕ ↦ ∑ k ∈ Icc 1 n, (1 : ℕ → ℂ) k) =O[atTop]
        fun n ↦ (n : ℝ) ^ (1 : ℝ) := by
      refine isBigO_iff.mpr ⟨1, Eventually.of_forall fun n ↦ ?_⟩
      simp
    have hzeta := LSeries_eq_mul_integral (1 : ℕ → ℂ) zero_le_one hz
      (LSeriesSummable_one_iff.mpr hz) hO1
    rw [LSeries_one_eq_riemannZeta hz, riemannZeta_eq_inv_sub_add hz1] at hzeta
    have hint1 : IntegrableOn (fun t : ℝ ↦ (t : ℂ) ^ (-z)) (Set.Ioi 1) :=
      integrableOn_Ioi_cpow_of_lt (by simpa using hz) zero_lt_one
    have hfract_loc : LocallyIntegrableOn (fun t : ℝ ↦ (↑(Int.fract t) : ℂ)) (Set.Ici 1) := by
      refine ((locallyIntegrable_const (1 : ℝ)).mono
        (Complex.measurable_ofReal.comp measurable_fract).aestronglyMeasurable
        (Eventually.of_forall fun t ↦ ?_)).locallyIntegrableOn _
      simpa [abs_of_nonneg (Int.fract_nonneg t)] using (Int.fract_lt_one t).le
    have hint2 : IntegrableOn
        (fun t : ℝ ↦ (↑(Int.fract t) : ℂ) * (t : ℂ) ^ (-(z + 1))) (Set.Ioi 1) :=
      integrableOn_mul_cpow_of_isBigO hfract_loc hfract_O hz0
    have hcongr : Set.EqOn
        (fun t : ℝ ↦ (∑ k ∈ Icc 1 ⌊t⌋₊, (1 : ℕ → ℂ) k) * (t : ℂ) ^ (-(z + 1)))
        (fun t : ℝ ↦ (t : ℂ) ^ (-z) - (↑(Int.fract t) : ℂ) * (t : ℂ) ^ (-(z + 1)))
        (Set.Ioi 1) := by
      intro t ht
      have ht0 : 0 < t := zero_lt_one.trans ht
      have hfl : (∑ k ∈ Icc 1 ⌊t⌋₊, (1 : ℕ → ℂ) k) = (t : ℂ) - (↑(Int.fract t) : ℂ) := by
        have hnat : (⌊t⌋₊ : ℝ) = t - Int.fract t := by
          rw [natCast_floor_eq_intCast_floor ht0.le, Int.self_sub_fract]
        simp only [Pi.one_apply, sum_const, Nat.card_Icc, add_tsub_cancel_right, nsmul_eq_mul,
          mul_one]
        exact_mod_cast hnat
      dsimp only
      rw [hfl, sub_mul]
      congr 1
      have hpow : (t : ℂ) * (t : ℂ) ^ (-(z + 1)) = (t : ℂ) ^ (1 + -(z + 1)) := by
        rw [cpow_add _ _ (ofReal_ne_zero.mpr ht0.ne'), cpow_one]
      rw [hpow]
      congr 1
      ring
    have hmain : ∫ t : ℝ in Set.Ioi 1, (t : ℂ) ^ (-z) = 1 / (z - 1) := by
      rw [integral_Ioi_cpow_of_lt (by simpa using hz) zero_lt_one, ofReal_one, one_cpow]
      have hzn : -z + 1 ≠ 0 := by
        intro h
        exact hz1 (by linear_combination -h)
      field_simp [sub_ne_zero.mpr hz1, hzn]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioi hcongr, integral_sub hint1 hint2, hmain] at hzeta
    simp only [G]
    have hsub : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
    have hkey : (z - 1)⁻¹ + riemannZeta₀ z = (z - 1)⁻¹ +
        (1 - z * ∫ t in Set.Ioi (1 : ℝ), (↑(Int.fract t) : ℂ) * (t : ℂ) ^ (-(z + 1))) := by
      calc
        (z - 1)⁻¹ + riemannZeta₀ z =
            z * (1 / (z - 1) - ∫ t in Set.Ioi (1 : ℝ),
              (↑(Int.fract t) : ℂ) * (t : ℂ) ^ (-(z + 1))) := hzeta
        _ = (z - 1)⁻¹ +
            (1 - z * ∫ t in Set.Ioi (1 : ℝ), (↑(Int.fract t) : ℂ) * (t : ℂ) ^ (-(z + 1))) := by
          field_simp [hsub]
          ring
    exact add_left_cancel hkey
  exact hZ.eqOn_of_preconnected_of_eventuallyEq hG (convex_halfSpace_re_gt 0).isPreconnected
    (by norm_num : (2 : ℂ) ∈ {z : ℂ | 0 < z.re}) heq hs

/-- **Fractional-part continuation of `riemannZeta`.** For `Re s > 0` and `s ≠ 1`,
`ζ(s) = s / (s - 1) - s ∫_1^∞ {t} t^{-(s + 1)} dt`. -/
theorem riemannZeta_eq_div_sub_mul_integral {s : ℂ} (hs : 0 < s.re) (hs₁ : s ≠ 1) :
    riemannZeta s =
      s / (s - 1) - s * ∫ t in Set.Ioi (1 : ℝ), (↑(Int.fract t) : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
  rw [riemannZeta_eq_inv_sub_add hs₁, riemannZeta₀_eq_one_sub_mul_integral hs]
  field_simp [sub_ne_zero.mpr hs₁]
  ring

/-- On the open right half-plane `Re s > 0`, `‖riemannZeta₀ s‖ ≤ 1 + ‖s‖ / Re s`. -/
theorem norm_riemannZeta₀_le_one_add_div {s : ℂ} (hs : 0 < s.re) :
    ‖riemannZeta₀ s‖ ≤ 1 + ‖s‖ / s.re := by
  have hb : ‖∫ t in Set.Ioi (1 : ℝ), (↑(Int.fract t) : ℂ) * (t : ℂ) ^ (-(s + 1))‖ ≤ 1 / s.re :=
    norm_integral_mul_cpow_le_of_bound (fun t _ ↦ by
      rw [Complex.norm_real, Real.norm_of_nonneg (Int.fract_nonneg t)]
      exact (Int.fract_lt_one t).le) hs
  rw [riemannZeta₀_eq_one_sub_mul_integral hs]
  calc
    ‖1 - s * ∫ t in Set.Ioi (1 : ℝ), (↑(Int.fract t) : ℂ) * (t : ℂ) ^ (-(s + 1))‖ ≤
        ‖(1 : ℂ)‖ +
          ‖s‖ * ‖∫ t in Set.Ioi (1 : ℝ), (↑(Int.fract t) : ℂ) * (t : ℂ) ^ (-(s + 1))‖ := by
      rw [← norm_mul]
      exact norm_sub_le _ _
    _ ≤ 1 + ‖s‖ * (1 / s.re) := by
      rw [norm_one]
      gcongr
    _ = 1 + ‖s‖ / s.re := by ring

/-- **Explicit right-half-plane growth bound for `riemannZeta`.** For `Re s > 0` and `s ≠ 1`,
`‖ζ(s)‖ ≤ ‖s‖ / ‖s - 1‖ + ‖s‖ / Re s`. -/
theorem norm_riemannZeta_le_div_add_div {s : ℂ} (hs : 0 < s.re) (hs₁ : s ≠ 1) :
    ‖riemannZeta s‖ ≤ ‖s‖ / ‖s - 1‖ + ‖s‖ / s.re := by
  have hb : ‖∫ t in Set.Ioi (1 : ℝ), (↑(Int.fract t) : ℂ) * (t : ℂ) ^ (-(s + 1))‖ ≤ 1 / s.re :=
    norm_integral_mul_cpow_le_of_bound (fun t _ ↦ by
      rw [Complex.norm_real, Real.norm_of_nonneg (Int.fract_nonneg t)]
      exact (Int.fract_lt_one t).le) hs
  rw [riemannZeta_eq_div_sub_mul_integral hs hs₁]
  calc
    ‖s / (s - 1) - s * ∫ t in Set.Ioi (1 : ℝ), (↑(Int.fract t) : ℂ) * (t : ℂ) ^ (-(s + 1))‖ ≤
        ‖s / (s - 1)‖ +
          ‖s‖ * ‖∫ t in Set.Ioi (1 : ℝ), (↑(Int.fract t) : ℂ) * (t : ℂ) ^ (-(s + 1))‖ := by
      rw [← norm_mul]
      exact norm_sub_le _ _
    _ ≤ ‖s‖ / ‖s - 1‖ + ‖s‖ * (1 / s.re) := by
      rw [norm_div]
      gcongr
    _ = ‖s‖ / ‖s - 1‖ + ‖s‖ / s.re := by ring

end FractionalPartGrowth

end TauCeti
