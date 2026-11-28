/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DirichletCharacter.LFunction.Basic
public import TauCeti.NumberTheory.LSeries.SumCoeff
public import TauCeti.NumberTheory.DirichletCharacter.PartialSum
import Mathlib.Analysis.Complex.Convex
import TauCeti.NumberTheory.DirichletCharacter.LFunction.Entire
import TauCeti.NumberTheory.LSeries.Moebius
import TauCeti.NumberTheory.LSeries.RiemannZeta.Basic
import TauCeti.NumberTheory.LSeries.RiemannZeta.Bounds
import TauCeti.NumberTheory.PrimeFactors.Bounds

/-!
# Bounds for Dirichlet L-functions and their Dirichlet series

Cancellation over a full period bounds the partial sums of a nonprincipal character of level
`N` by `N`, so they are `O(1)` (`DirichletCharacter.isBigO_sum_Icc_one`). Partial summation then
represents its continued L-function on `Re(s) > 0` by an
absolutely convergent integral and gives `‖L(s, χ)‖ ≤ N ‖s‖ / Re(s)`. In particular this is a
linear growth bound on each vertical line in the right half-plane, with explicit dependence
on the level. For a primitive character the level is its conductor.

At `s = 1` the same integral is `∫_{t > 1} S(t) / t²`, where `S(t)` is the sum of `χ k` over
`1 ≤ k ≤ t`. Using `‖S(t)‖ ≤ t` on `(1, N]` and `‖S(t)‖ ≤ N` beyond gives
`‖L(1, χ)‖ ≤ 1 + log N`, and hence `‖L(1, χ)‖ ≤ (1 + t⁻¹) N ^ t` for every `t > 0`. No
primitivity is assumed, so these bounds also hold for imprimitive characters such as the product
of two characters taken at the least common multiple of their levels. Combining the nonprincipal
bound with the fractional-part bound on `riemannZeta` and the Euler-factor bound on
`N.primeFactors` also yields
`‖L(s, χ)‖ ≤ N (‖s - 1‖⁻¹ + 1 + ‖s‖ / Re(s))` on `Re(s) > 0` (away from `s = 1` when `χ = 1`) for
every character `χ` of level `N`, principal or nonprincipal.

The bounds on `Re(s) > 0` above are for the native analytic continuation, not the Dirichlet
series (which need not converge absolutely in this half-plane). No zero-free hypothesis is
required. With the principal pole removed, the Möbius series gives a level-independent lower
bound on `Re s > 1`.

On `Re(s) ≥ 1 + 1 / A`, where the Dirichlet series converges absolutely, comparison with
`ζ(Re s) < 1 + 1 / (Re s - 1)` gives `‖L(s, χ)‖ ≤ 1 + A`
(`DirichletCharacter.norm_LSeries_le_one_add`).

## Provenance

`DirichletCharacter.norm_LSeries_le_one_add` is adapted from `New.norm_LSeries_char_le` in grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC), file
`src/Lib/Analytic/PrimeNumberTheorem/LFunctionGrowth.lean`.

## References

* H. Davenport, *Multiplicative Number Theory*, the partial-summation construction and bounds
  for Dirichlet L-functions, and the chapter on Siegel's theorem for the bound at `s = 1`.
-/

public section

open Finset Filter MeasureTheory Complex Asymptotics
open scoped Topology

namespace DirichletCharacter

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)

/-- Partial summation represents the continued L-function of a nonprincipal character on the
whole half-plane `Re(s) > 0`. -/
theorem LFunction_eq_mul_integral (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    χ.LFunction s =
      s * ∫ t in Set.Ioi (1 : ℝ), (∑ k ∈ Icc 1 ⌊t⌋₊, χ k) * (t : ℂ) ^ (-(s + 1)) := by
  have hO : (fun n : ℕ ↦ ∑ k ∈ Icc 1 n, χ k) =O[atTop] fun n ↦ (n : ℝ) ^ (0 : ℝ) := by
    simpa only [Real.rpow_zero] using χ.isBigO_sum_Icc_one hχ
  have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const continuous_re
  have hF := TauCeti.LSeries.differentiableOn_mul_integral_of_isBigO _ hO
  have heq : χ.LFunction =ᶠ[𝓝 (2 : ℂ)]
      fun z ↦ z * ∫ t in Set.Ioi (1 : ℝ), (∑ k ∈ Icc 1 ⌊t⌋₊, χ k) *
        (t : ℂ) ^ (-(z + 1)) := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
      (by norm_num : (2 : ℂ) ∈ {z : ℂ | 1 < z.re})] with z hz
    rw [LFunction_eq_LSeries χ hz]
    exact LSeries_eq_mul_integral _ le_rfl (lt_trans zero_lt_one hz)
      (χ.LSeriesSummable_of_one_lt_re hz) hO
  have hL := (differentiable_LFunction hχ).differentiableOn.analyticOnNhd hopen
  exact (hL.eqOn_of_preconnected_of_eventuallyEq
    (hF.analyticOnNhd hopen) (convex_halfSpace_re_gt 0).isPreconnected
    (by norm_num : (2 : ℂ) ∈ {z : ℂ | 0 < z.re}) heq) hs

/-- On the right half-plane, the continued L-function of a nonprincipal character satisfies
`‖L(s, χ)‖ ≤ N ‖s‖ / Re(s)`. For a primitive character, `N` is the conductor. -/
theorem norm_LFunction_le_level_mul_norm_div_re (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    ‖χ.LFunction s‖ ≤ (N : ℝ) * ‖s‖ / s.re := by
  rw [χ.LFunction_eq_mul_integral hχ hs]
  exact TauCeti.LSeries.norm_mul_integral_le_of_bound _ (χ.norm_sum_Icc_le_level hχ) hs

/-- **A logarithmic bound for `L(1, χ)`.** The continued L-function of a nonprincipal character
of level `N` satisfies `‖L(1, χ)‖ ≤ 1 + log N`. Primitivity is not assumed; for a primitive
character, `N` is the conductor. -/
theorem norm_LFunction_one_le_one_add_log (hχ : χ ≠ 1) :
    ‖χ.LFunction 1‖ ≤ 1 + Real.log N := by
  set f : ℝ → ℂ := fun t ↦ (∑ k ∈ Icc 1 ⌊t⌋₊, χ k) * (t : ℂ) ^ (-((1 : ℂ) + 1)) with hf
  have hN : (1 : ℝ) ≤ N := Nat.one_le_cast.mpr NeZero.one_le
  have hnorm {t : ℝ} (ht : 0 < t) : ‖f t‖ = ‖∑ k ∈ Icc 1 ⌊t⌋₊, χ k‖ * t ^ (-2 : ℝ) := by
    rw [hf, norm_mul, norm_cpow_eq_rpow_re_of_pos ht]
    norm_num
  have hO : (fun n : ℕ ↦ ∑ k ∈ Icc 1 n, χ k) =O[atTop] fun n ↦ (n : ℝ) ^ (0 : ℝ) := by
    simpa only [Real.rpow_zero] using χ.isBigO_sum_Icc_one hχ
  have hint : IntegrableOn (fun t ↦ ‖f t‖) (Set.Ioi 1) :=
    (TauCeti.LSeries.integrableOn_sum_mul_cpow_of_isBigO _ hO (s := 1) (by simp)).norm
  -- Split the integral at `N`: bound the partial sums by `t` below `N` and by `N` above it.
  have hlow : ∫ t in Set.Ioc 1 (N : ℝ), ‖f t‖ ≤ Real.log N := by
    have hinv : IntegrableOn (fun t : ℝ ↦ t⁻¹) (Set.Ioc 1 N) :=
      (continuousOn_inv₀.mono fun t (ht : t ∈ Set.Icc 1 (N : ℝ)) ↦
        (zero_lt_one.trans_le ht.1).ne').integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
    calc
      _ ≤ ∫ t in Set.Ioc 1 (N : ℝ), t⁻¹ := by
        refine setIntegral_mono_on (hint.mono_set Set.Ioc_subset_Ioi_self) hinv measurableSet_Ioc
          fun t ht ↦ ?_
        have ht0 : 0 < t := zero_lt_one.trans ht.1
        -- Termwise, the partial sum up to `t` has norm at most `⌊t⌋₊ ≤ t`.
        have hsum : ‖∑ k ∈ Icc 1 ⌊t⌋₊, χ k‖ ≤ t :=
          calc
            _ ≤ ∑ _k ∈ Icc 1 ⌊t⌋₊, (1 : ℝ) :=
              (norm_sum_le _ _).trans (sum_le_sum fun k _ ↦ χ.norm_le_one k)
            _ ≤ t := by simpa using Nat.floor_le ht0.le
        rw [hnorm ht0]
        calc
          _ ≤ t * t ^ (-2 : ℝ) :=
            mul_le_mul_of_nonneg_right hsum (Real.rpow_nonneg ht0.le _)
          _ = t⁻¹ := by
            rw [Real.rpow_neg ht0.le, Real.rpow_two]
            field_simp
      _ = Real.log N := by
        rw [← intervalIntegral.integral_of_le hN, integral_inv_of_pos one_pos (by linarith),
          div_one]
  have hhigh : ∫ t in Set.Ioi (N : ℝ), ‖f t‖ ≤ 1 := by
    have hN0 : (0 : ℝ) < N := zero_lt_one.trans_le hN
    calc
      _ ≤ ∫ t in Set.Ioi (N : ℝ), (N : ℝ) * t ^ (-2 : ℝ) := by
        refine setIntegral_mono_on (hint.mono_set (Set.Ioi_subset_Ioi hN))
          ((integrableOn_Ioi_rpow_of_lt (by norm_num) hN0).const_mul _) measurableSet_Ioi
          fun t ht ↦ ?_
        have ht0 : 0 < t := hN0.trans ht
        rw [hnorm ht0]
        exact mul_le_mul_of_nonneg_right (χ.norm_sum_Icc_le_level hχ _)
          (Real.rpow_nonneg ht0.le _)
      _ = 1 := by
        rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hN0]
        norm_num [Real.rpow_neg_one, hN0.ne']
  rw [χ.LFunction_eq_mul_integral hχ (by simp), one_mul]
  calc
    _ ≤ ∫ t in Set.Ioi 1, ‖f t‖ := norm_integral_le_integral_norm _
    _ = (∫ t in Set.Ioc 1 (N : ℝ), ‖f t‖) + ∫ t in Set.Ioi (N : ℝ), ‖f t‖ := by
      rw [← setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
        (hint.mono_set Set.Ioc_subset_Ioi_self) (hint.mono_set (Set.Ioi_subset_Ioi hN)),
        Set.Ioc_union_Ioi_eq_Ioi hN]
    _ ≤ 1 + Real.log N := by linarith

/-- **A power bound for `L(1, χ)`.** For every `t > 0`, the continued L-function of a nonprincipal
character of level `N` satisfies `‖L(1, χ)‖ ≤ (1 + t⁻¹) N ^ t`. This is the logarithmic bound
`norm_LFunction_one_le_one_add_log` with `log N ≤ N ^ t / t`. -/
theorem norm_LFunction_one_le_mul_rpow (hχ : χ ≠ 1) {t : ℝ} (ht : 0 < t) :
    ‖χ.LFunction 1‖ ≤ (1 + t⁻¹) * (N : ℝ) ^ t := by
  have hlog := Real.log_le_rpow_div (Nat.cast_nonneg N) ht
  have h1 : 1 ≤ (N : ℝ) ^ t := Real.one_le_rpow (Nat.one_le_cast.mpr NeZero.one_le) ht.le
  calc ‖χ.LFunction 1‖ ≤ 1 + Real.log N := χ.norm_LFunction_one_le_one_add_log hχ
    _ ≤ (N : ℝ) ^ t + (N : ℝ) ^ t / t := by linarith
    _ = (1 + t⁻¹) * (N : ℝ) ^ t := by ring

/-- On `Re(s) > 0` (away from `s = 1` when `χ = 1`), the continued L-function of any Dirichlet
character of level `N` — principal or nonprincipal — satisfies
`‖L(s, χ)‖ ≤ N (‖s - 1‖⁻¹ + 1 + ‖s‖ / Re(s))`. -/
theorem norm_LFunction_le {s : ℂ} (hs : 0 < s.re) (h1 : s ≠ 1 ∨ χ ≠ 1) :
    ‖χ.LFunction s‖ ≤ (N : ℝ) * (‖s - 1‖⁻¹ + 1 + ‖s‖ / s.re) := by
  by_cases hχ : χ = 1
  · subst hχ
    have hs_ne : s ≠ 1 := h1.resolve_right (not_not.mpr rfl)
    rw [← LFunctionTrivChar, LFunctionTrivChar_eq_mul_riemannZeta hs_ne, norm_mul]
    exact mul_le_mul (TauCeti.norm_prod_primeFactors_one_sub_cpow_neg_le hs.le)
      (TauCeti.norm_riemannZeta_le_of_re_pos hs) (norm_nonneg _) (Nat.cast_nonneg N)
  · calc ‖χ.LFunction s‖ ≤ (N : ℝ) * ‖s‖ / s.re :=
          χ.norm_LFunction_le_level_mul_norm_div_re hχ hs
      _ = (N : ℝ) * (‖s‖ / s.re) := mul_div_assoc _ _ _
      _ ≤ (N : ℝ) * (‖s - 1‖⁻¹ + 1 + ‖s‖ / s.re) :=
          mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (by positivity)) (Nat.cast_nonneg N)

/-- On `Re s > 1`, the norm of the pole-removed L-function is bounded below by
`min 1 ‖s - 1‖ / (1 + (Re s - 1)⁻¹)`, independently of the level. -/
theorem min_one_norm_sub_one_div_le_norm_entireLFunction {s : ℂ} (hs : 1 < s.re) :
    min 1 ‖s - 1‖ / (1 + (s.re - 1)⁻¹) ≤ ‖χ.entireLFunction s‖ := by
  have hζ := TauCeti.norm_riemannZeta_lt_one_add_one_div_sub_one (s := (s.re : ℂ))
    (by simpa using hs)
  have hL : 1 / (1 + (s.re - 1)⁻¹) ≤ ‖χ.LFunction s‖ := by
    refine le_trans ?_ (χ.norm_riemannZeta_two_mul_re_div_le_norm_LFunction hs)
    rw [norm_div]
    have hden : 0 < ‖riemannZeta s.re‖ :=
      norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_lt_re (by simpa using hs))
    have hnum := (TauCeti.one_lt_riemannZeta_re (by linarith : 1 < 2 * s.re)).le.trans
      (re_le_norm (riemannZeta ((2 * s.re : ℝ) : ℂ)))
    push_cast at hnum
    exact div_le_div₀ (norm_nonneg _) hnum hden (by simpa [one_div] using hζ.le)
  rw [div_eq_mul_one_div]
  have hnonneg : (0 : ℝ) ≤ 1 / (1 + (s.re - 1)⁻¹) := by positivity
  by_cases hχ : χ = 1
  · subst χ
    have hs₁ : s ≠ 1 := ne_of_apply_ne re (by simpa using hs.ne')
    rw [entireLFunction_one_apply hs₁, norm_mul]
    exact mul_le_mul (min_le_right _ _) hL hnonneg (norm_nonneg _)
  · rw [entireLFunction_of_ne_one hχ]
    exact (mul_le_mul_of_nonneg_right (min_le_left _ _) hnonneg).trans (by simpa using hL)

omit [NeZero N] in
/-- If `Re s ≥ 1 + 1 / A` with `A > 0`, then the Dirichlet series of `χ` has
`‖L(s, χ)‖ ≤ 1 + A`. -/
theorem norm_LSeries_le_one_add {s : ℂ} {A : ℝ} (hA : 0 < A) (hs : 1 + 1 / A ≤ s.re) :
    ‖LSeries (fun n ↦ χ n) s‖ ≤ 1 + A := by
  -- The series is dominated termwise by `ζ(Re s) < 1 + 1 / (Re s - 1)`.
  have hs_one : 1 < s.re := by linarith [one_div_pos.2 hA]
  have h_summable : Summable fun n : ℕ ↦ 1 / (n : ℝ) ^ s.re :=
    Real.summable_one_div_nat_rpow.2 hs_one
  have term_le (n : ℕ) : ‖LSeries.term (χ ·) s n‖ ≤ 1 / (n : ℝ) ^ s.re := by
    rw [LSeries.norm_term_eq]
    split_ifs
    · positivity
    · exact div_le_div_of_nonneg_right (χ.norm_le_one _) (by positivity)
  calc ‖LSeries (fun n ↦ χ n) s‖
    _ ≤ ∑' n : ℕ, 1 / (n : ℝ) ^ s.re := tsum_of_norm_bounded h_summable.hasSum term_le
    _ = ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ s.re := by
      rw [h_summable.tsum_eq_zero_add]
      simp [Real.zero_rpow (one_pos.trans hs_one).ne']
    _ = ∑' n : ℕ, ((n : ℝ) + 1) ^ (-s.re) :=
      tsum_congr fun n ↦ by rw [Real.rpow_neg (by positivity), one_div]
    _ = (riemannZeta s.re).re := (TauCeti.hasSum_nat_add_one_rpow_neg_riemannZeta_re hs_one).tsum_eq
    _ ≤ 1 + 1 / (s.re - 1) :=
      (TauCeti.riemannZeta_re_lt_one_add_one_div_sub_one (by linarith) hs_one.ne').le
    _ ≤ 1 + A := by linarith [(one_div_le hA (sub_pos.2 hs_one)).1 (by linarith)]

end DirichletCharacter
