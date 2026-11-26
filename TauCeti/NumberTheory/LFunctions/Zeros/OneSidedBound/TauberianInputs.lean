/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.Remainder
import TauCeti.Analysis.Calculus.LogDeriv
import TauCeti.Analysis.Convex.Lipschitz
import TauCeti.NumberTheory.DirichletCharacter.LFunction.LogDeriv.ZeroFreeRegion

/-!
# Tauberian estimates for the signed prime remainder

The signed prime remainder `R_q` is Lipschitz in the logarithmic variable, and the
pole-subtracted factor `s ↦ G_q(s) / s` of its Laplace transform is holomorphic in a common
zero-free region for the two families of Dirichlet characters, with a bound polynomial in the
logarithmic scale. These two estimates are used to obtain rapid decay in `log y`.

## References

* The estimates serve the Tauberian application `New.eventually_abs_primeRemainder_le` in
  `grh/src/New/Reduction/Zeros/PrimeNumberTheorem.lean` of the shorter GRH formalization
  (<https://github.com/lsernau/grh-lean>, commit `72fead102f663d5c7a407964a13dc0cf9d977207`).
-/

public section

open DirichletCharacter Filter Set Topology

namespace TauCeti.OneSidedBound

variable (d q : ℕ) [Fact d.Prime] [NeZero q]

/-- The signed remainder `u ↦ R_q(exp u)` is `26`-Lipschitz on the whole real line. -/
theorem lipschitzWith_primeRemainder_exp :
    LipschitzWith 26 (fun u : ℝ ↦ primeRemainder d q (Real.exp u)) := by
  have hOrdered (x y : ℝ) (hxy : x ≤ y) (hclose : y - x ≤ 1) :
      |primeRemainder d q (Real.exp y) - primeRemainder d q (Real.exp x)| ≤ 26 * (y - x) := by
    have h := abs_primeRemainder_sub_le d q (Real.exp_pos x) (Real.exp_le_exp.mpr hxy)
    have he : (Real.exp y - Real.exp x) / Real.exp x = Real.exp (y - x) - 1 := by
      rw [sub_div, div_self (Real.exp_ne_zero _), ← Real.exp_sub]
    rw [mul_div_assoc, he] at h
    have hsmall := Real.abs_exp_sub_one_le (x := y - x)
      (by rwa [abs_of_nonneg (sub_nonneg.mpr hxy)])
    rw [abs_of_nonneg (sub_nonneg.mpr hxy)] at hsmall
    linarith [le_abs_self (Real.exp (y - x) - 1)]
  apply lipschitzOnWith_univ.mp
  refine convex_univ.lipschitzOnWith_of_locally_dist_le fun x _ ↦ ?_
  rw [nhdsWithin_univ]
  filter_upwards [Metric.ball_mem_nhds x zero_lt_one] with y hy
  rw [Metric.mem_ball, Real.dist_eq] at hy
  simp only [Real.dist_eq, NNReal.coe_ofNat]
  rcases le_total x y with hxy | hyx
  · rw [abs_of_nonneg (sub_nonneg.mpr hxy)] at hy ⊢
    exact hOrdered x y hxy hy.le
  · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hyx)] at hy
    simpa only [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hyx)] using hOrdered y x hyx hy.le

private theorem norm_logDerivMean_le [NeZero (q * d)] {s : ℂ} {B : ℝ}
    (hχ : ∀ χ : DirichletCharacter ℂ q, ‖logDeriv χ.entireLFunction s‖ ≤ B)
    (htw : ∀ χ : DirichletCharacter ℂ q,
      ‖logDeriv (quadraticTwist d χ).entireLFunction s‖ ≤ B) :
    ‖logDerivMean d q s‖ ≤ 2 * B + 1 := by
  classical
  have hφ : (1 : ℝ) ≤ q.totient := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hcard : Fintype.card (DirichletCharacter ℂ q) = q.totient := by
    rw [← Nat.card_eq_fintype_card, card_eq_totient_of_hasEnoughRootsOfUnity]
  let f : DirichletCharacter ℂ q → ℂ := fun χ ↦
    logDeriv (quadraticTwist d χ).entireLFunction s - logDeriv χ.entireLFunction s
  have hsum : ‖∑ χ, f χ‖ ≤ (q.totient : ℝ) * (2 * B) := by
    simpa only [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul, two_mul] using
      norm_sum_le_of_le (s := Finset.univ) (f := f)
        (fun χ _ ↦ (norm_sub_le _ _).trans (add_le_add (htw χ) (hχ χ)))
  rw [logDerivMean_def, norm_div, Complex.norm_natCast, div_le_iff₀ (by linarith)]
  calc
    ‖(∑ χ, f χ) - 1‖ ≤ ‖∑ χ, f χ‖ + 1 := by simpa only [norm_one] using norm_sub_le _ (1 : ℂ)
    _ ≤ (q.totient : ℝ) * (2 * B) + 1 := add_le_add_left hsum 1
    _ ≤ (2 * B + 1) * (q.totient : ℝ) := by linarith

/-- On `Re s ≥ 1 - l⁻²⁶`, `‖s‖ ≤ exp l` for all sufficiently large `l`, the factor `G_q(s) / s`
is analytic and has norm at most `l²⁶`. The threshold may depend on the fixed levels `q` and
`qd`. No coprimality or parity assumption on the twisting prime is needed for this estimate. -/
theorem eventually_analyticAt_and_norm_logDerivMean_div_le :
    ∀ᶠ l : ℝ in atTop, ∀ s : ℂ, 1 - 1 / l ^ 26 ≤ s.re → ‖s‖ ≤ Real.exp l →
      AnalyticAt ℂ (fun z ↦ logDerivMean d q z / z) s ∧ ‖logDerivMean d q s / s‖ ≤ l ^ 26 := by
  classical
  let : NeZero (q * d) := ⟨Nat.mul_ne_zero (NeZero.ne q) (Fact.out : d.Prime).ne_zero⟩
  have hregion (N : ℕ) [NeZero N] : ∀ᶠ l : ℝ in atTop, ∀ χ : DirichletCharacter ℂ N,
      ∀ s : ℂ, 1 - 1 / l ^ 25 ≤ s.re → ‖s‖ ≤ Real.exp l →
        χ.entireLFunction s ≠ 0 ∧ ‖logDeriv χ.entireLFunction s‖ ≤ 2 * l ^ 25 :=
    eventually_all.mpr fun χ ↦ χ.eventually_entireLFunction_ne_zero_and_norm_logDeriv_le
  filter_upwards [hregion q, hregion (q * d), eventually_ge_atTop (10 : ℝ)] with l hq hd hl s hs hn
  have hl₁ : 1 ≤ l := by linarith
  have hpow : l ^ 25 ≤ l ^ 26 := pow_le_pow_right₀ hl₁ (by decide)
  have hη : 1 / l ^ 26 ≤ 1 / l ^ 25 := one_div_le_one_div_of_le (by positivity) hpow
  have hre : 1 - 1 / l ^ 25 ≤ s.re := by linarith
  have htwo : 2 ≤ l ^ 25 := (by linarith : 2 ≤ l).trans (le_self_pow₀ hl₁ (by decide))
  have hhalf : 1 / 2 ≤ ‖s‖ := by
    have hsmall := one_div_le_one_div_of_le two_pos htwo
    linarith [Complex.re_le_norm s]
  have hs₀ : s ≠ 0 := norm_pos_iff.mp (by linarith)
  have hχ (χ : DirichletCharacter ℂ q) := hq χ s hre hn
  have htw (χ : DirichletCharacter ℂ q) := hd (quadraticTwist d χ) s hre hn
  constructor
  · have hsum : AnalyticAt ℂ (fun z ↦ ∑ χ : DirichletCharacter ℂ q,
        (logDeriv (quadraticTwist d χ).entireLFunction z - logDeriv χ.entireLFunction z)) s := by
      refine Finset.analyticAt_fun_sum _ fun χ _ ↦ ?_
      exact (((quadraticTwist d χ).analyticAt_entireLFunction s).logDeriv (htw χ).1).fun_sub
        ((χ.analyticAt_entireLFunction s).logDeriv (hχ χ).1)
    simp only [logDerivMean_def]
    exact (hsum.fun_sub analyticAt_const).div_const.div analyticAt_id hs₀
  · rw [norm_div]
    calc
      _ ≤ (2 * (2 * l ^ 25) + 1) / (1 / 2) := by
        gcongr
        exact norm_logDerivMean_le d q (fun χ ↦ (hχ χ).2) (fun χ ↦ (htw χ).2)
      _ ≤ 10 * l ^ 25 := by linarith
      _ ≤ l ^ 26 := by
        rw [pow_succ l 25, mul_comm (l ^ 25)]
        exact mul_le_mul_of_nonneg_right hl (by positivity)

end TauCeti.OneSidedBound
