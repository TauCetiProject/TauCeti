/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DirichletCharacter.LFunction.Entire
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import TauCeti.NumberTheory.DirichletCharacter.LFunction.FiniteFamily.Quadratic
import TauCeti.NumberTheory.DirichletCharacter.LFunction.LogDeriv.ZeroFreeRegion

/-!
# Uniform disk bounds for levels with fixed prime support

For levels supported on a fixed finite set of primes, the regularized L-functions of the
characters whose square is principal have a common positive lower bound near `1`. This makes
the zero-free region and logarithmic-derivative bound uniform on a disk of radius `1 / X`
when the level is at most a fixed power of `X`.

The disk estimate follows the scale choice of `New.eventually_norm_logDeriv_entireL_le_near_one`
in [`grh/src/Lib/Analytic/Primes.lean` of lsernau/grh-lean][short-proof]. Instead of descending
quadratic characters to a fixed level, we use the lower bound for fixed prime support.

[short-proof]: https://github.com/lsernau/grh-lean/blob/72fead1/grh/src/Lib/Analytic/Primes.lean
-/

public section

open Filter Metric Real
open scoped Topology

namespace TauCeti.DirichletCharacter

/-- For large `X`, uniformly in all levels at most `X ^ A` supported on `S`, the pole-removed
L-functions are nonzero on the disk `‖s - 1‖ ≤ 1 / X`, and their logarithmic derivatives have
norm at most `X` there. The threshold depends only on `S` and `A`. -/
theorem eventually_entireLFunction_ne_zero_and_norm_logDeriv_le_of_primeFactors_subset
    (S : Finset ℕ) (A : ℕ) :
    ∀ᶠ X : ℝ in atTop, ∀ {q : ℕ} [NeZero q], q.primeFactors ⊆ S → (q : ℝ) ≤ X ^ A →
      ∀ (χ : DirichletCharacter ℂ q) (s : ℂ), ‖s - 1‖ ≤ X⁻¹ →
        χ.entireLFunction s ≠ 0 ∧ ‖logDeriv χ.entireLFunction s‖ ≤ X := by
  obtain ⟨c, hc, hnear⟩ :=
    exists_pos_eventually_le_norm_regularizedLFunction_of_primeFactors_subset_of_sq_eq_one S
  let l (X : ℝ) := ((A : ℝ) + 1) * log X
  have hl : Tendsto l atTop atTop := tendsto_log_atTop.const_mul_atTop (by positivity)
  have hrad : Tendsto (fun X ↦ 1 / l X) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hl
  have hsmall : ∀ᶠ X : ℝ in atTop, 2 * l X ^ 25 ≤ X := by
    have h := ((isLittleO_pow_log_id_atTop (n := 25)).const_mul_left
      (2 * ((A : ℝ) + 1) ^ 25)).eventuallyLE
    filter_upwards [h, eventually_ge_atTop (0 : ℝ)] with X hpow hX
    refine (Real.le_norm_self _).trans ?_
    simpa only [l, mul_pow, mul_assoc, id_eq, Real.norm_of_nonneg hX] using hpow
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    hl.eventually (eventually_ge_atTop (max (10 ^ 10) c⁻¹)),
    hrad.eventually (eventually_closedBall_subset hnear), hsmall] with X hX hL hball hpow
  intro q _ hS hq χ s hs
  have hL₀ : 10 ^ 10 ≤ l X := (le_max_left _ _).trans hL
  have hLpos : 0 < l X := (by norm_num : (0 : ℝ) < 10 ^ 10).trans_le hL₀
  have hcL : 1 / l X ≤ c := by
    rw [one_div, inv_le_comm₀ hLpos hc]
    exact (le_max_right _ _).trans hL
  have hqL : (q : ℝ) ≤ exp (l X) := by
    have hX₀ : 0 < X := zero_lt_one.trans_le hX
    have he : exp (l X) = X ^ A * X := by
      simp only [l, add_mul, one_mul, exp_add]
      rw [← log_pow, exp_log (pow_pos hX₀ _), exp_log hX₀]
    rw [he]
    exact hq.trans (le_mul_of_one_le_right (by positivity) hX)
  have hre : 1 - 1 / l X ^ 25 ≤ s.re := by
    have hr := one_div_le_one_div_of_le (pow_pos hLpos 25) (by linarith : l X ^ 25 ≤ X)
    -- The real displacement is controlled by the complex displacement from `1`.
    have hdiff := (Complex.abs_re_le_norm (s - 1)).trans
      (hs.trans (by simpa only [one_div] using hr))
    rw [Complex.sub_re, Complex.one_re] at hdiff
    simp only [one_div]
    linarith only [neg_le_of_abs_le hdiff]
  have hn : ‖s‖ ≤ exp (l X) := by
    have hi : X⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hX
    have ht : ‖s‖ ≤ ‖s - 1‖ + 1 := by simpa only [norm_one] using norm_le_norm_sub_add s 1
    linarith [add_one_le_exp (l X)]
  obtain ⟨h₀, h₁⟩ := χ.entireLFunction_ne_zero_and_norm_logDeriv_le hL₀ hqL (fun hχ z hz ↦
    hcL.trans (hball (mem_closedBall_iff_norm.mpr hz) q hS χ hχ)) hre hn
  exact ⟨h₀, h₁.trans hpow⟩

end TauCeti.DirichletCharacter
