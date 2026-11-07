/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LSeries.Linearity
import TauCeti.NumberTheory.LSeries.SumCoeff

/-!
# The Riemann zeta function at real arguments

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

## Main results

* `TauCeti.hasSum_nat_add_one_rpow_neg_riemannZeta_re`: `∑ (n + 1) ^ (-s) = Re ζ(s)` for `s > 1`;
* `TauCeti.hasSum_nat_rpow_neg_riemannZeta_re`: the same series indexed from `n = 0` with the
  vanishing term `0 ^ (-s)`;
* `TauCeti.measurable_riemannZeta`: the Riemann zeta function is measurable.
* `TauCeti.one_sub_two_cpow_mul_riemannZeta_eq_mul_integral`: the partial-summation integral of
  the alternating series represents `(1 - 2 ^ (1 - s)) ζ(s)` on `Re s > 0`, `s ≠ 1`.
* `TauCeti.riemannZeta_lt_zero`: `ζ(σ)` is a negative real number for real `0 < σ < 1`.

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

/-- On `Re s > 1`, writing `(-1) ^ (n + 1) = 2 χ₀(n) - 1` with `χ₀` the principal character
modulo `2` gives `η(s) = 2 (1 - 2⁻ˢ) ζ(s) - ζ(s) = (1 - 2 ^ (1 - s)) ζ(s)`. -/
private theorem LSeries_neg_one_pow {s : ℂ} (hs : 1 < s.re) :
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
  have hA (n : ℕ) : ∑ k ∈ Icc 1 n, (-1 : ℂ) ^ (k + 1) = if Even n then 0 else 1 := by
    rw [← Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range, add_tsub_cancel_right,
      ← neg_one_geom_sum]
    simp [pow_add]
  have hA₁ (n : ℕ) : ‖∑ k ∈ Icc 1 n, (-1 : ℂ) ^ (k + 1)‖ ≤ 1 := by
    rw [hA]; split_ifs <;> simp
  have hO : (fun n : ℕ ↦ ∑ k ∈ Icc 1 n, (-1 : ℂ) ^ (k + 1)) =O[atTop]
      fun n ↦ (n : ℝ) ^ (0 : ℝ) :=
    Asymptotics.isBigO_iff.mpr ⟨1, Eventually.of_forall fun n ↦ by
      simpa using hA₁ n⟩
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
      LSeries_neg_one_pow hz, riemannZeta_eq_inv_sub_mul (sub_ne_zero.mp hz₁)]
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
  have hA (n : ℕ) : ∑ k ∈ Icc 1 n, (-1 : ℂ) ^ (k + 1) = if Even n then 0 else 1 := by
    rw [← Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range, add_tsub_cancel_right,
      ← neg_one_geom_sum]
    simp [pow_add]
  have hA₁ (n : ℕ) : ‖∑ k ∈ Icc 1 n, (-1 : ℂ) ^ (k + 1)‖ ≤ 1 := by
    rw [hA]; split_ifs <;> simp
  have hFg : Set.EqOn F (fun t ↦ (g t : ℂ)) (Set.Ioi 1) := fun t ht ↦ by
    simp only [F, g, hA]
    split_ifs
    · simp
    · rw [one_mul, ofReal_cpow (zero_le_one.trans ht.le), ofReal_neg, ofReal_add, ofReal_one]
  have hFint : MeasureTheory.IntegrableOn F (Set.Ioi 1) :=
    TauCeti.LSeries.integrableOn_sum_mul_cpow_of_bound _ hA₁
      (by simpa using h₀)
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
        simp only [Set.mem_Ioi] at ht; linarith)) Set.Ioc_subset_Ioi_self.eventuallyLE)
  have hrep := one_sub_two_cpow_mul_riemannZeta_eq_mul_integral (s := σ) (by simpa using h₀)
    (by exact_mod_cast h₁.ne)
  have h2 : (2 : ℂ) ^ (1 - (σ : ℂ)) = ((2 : ℝ) ^ (1 - σ) : ℝ) := by
    rw [ofReal_cpow zero_le_two]
    push_cast
    rfl
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

end TauCeti
