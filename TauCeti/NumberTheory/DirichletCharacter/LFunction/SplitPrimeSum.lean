/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Chebyshev.WeightedPrimeMellin
public import TauCeti.NumberTheory.DirichletCharacter.Bounds
public import TauCeti.NumberTheory.DirichletCharacter.LFunction.LogDeriv.Basic
public import TauCeti.NumberTheory.LSeries.RiemannZeta.LogDeriv.NearOne

/-!
# Split primes and the Landau combination `-ζ′/ζ - L′/L`

Let `χ` be a Dirichlet character of positive level. For real `σ > 1`, the combination
`-ζ′/ζ(σ) - re L′/L(σ, χ)` is the sum of the series `∑ Λ(n) (1 + re χ(n)) / n ^ σ`, whose terms
are nonnegative because `‖χ(n)‖ ≤ 1`. Keeping only the primes `p ≤ X` and comparing `p ^ σ` with
`p X ^ (σ - 1)` (`TauCeti.weightedPrimeSum_le_rpow_mul_sum`) bounds the weighted prime sum
`∑_{p ≤ X} (1 + re χ(p)) log p / p` by `X ^ (σ - 1)` times the combination. At the primes with
`χ(p) = 1` the weight is `2`, so

`∑_{p ≤ X, χ(p) = 1} log p / p ≤ (X ^ (σ - 1) / 2) (-ζ′/ζ(σ) - re L′/L(σ, χ))`.

At Landau's point `σ = 1 + 1 / log X` the factor `X ^ (σ - 1)` is `e`. The pole of `-ζ′/ζ` at
`1` (`TauCeti.exists_norm_neg_logDeriv_riemannZeta_one_add_sub_inv_le`) then gives one absolute
constant `C` with

`∑_{p ≤ X, χ(p) = 1} log p / p ≤ (e / 2) (log X + C - re L′/L(1 + 1 / log X, χ))`

for every `X ≥ e`, every positive level and every character of that level. Neither primitivity,
nor reality, nor nontriviality of `χ` is needed.

This is the prime side of Landau's deduction that a real zero `β` of `L(s, χ)` close to `1` leaves
few primes with `χ(p) = 1`: an upper bound `-re L′/L(σ, χ) ≤ A - 1 / (σ - β)` turns the last
display into a bound for the sum over those primes.

## Main results

* `DirichletCharacter.hasSum_vonMangoldt_mul_one_add_re_div_rpow`: for real `σ > 1`,
  `∑ Λ(n) (1 + re χ(n)) / n ^ σ = -re ζ′/ζ(σ) - re L′/L(σ, χ)`.
* `DirichletCharacter.sum_vonMangoldt_mul_one_add_re_div_rpow_le`: every finite partial sum of
  that nonnegative series is at most `-re ζ′/ζ(σ) - re L′/L(σ, χ)`.
* `DirichletCharacter.weightedPrimeSum_one_add_re_le`: the weighted prime sum with weights
  `1 + re χ(p)` is at most `X ^ (σ - 1) (-re ζ′/ζ(σ) - re L′/L(σ, χ))`.
* `DirichletCharacter.sum_primesLE_filter_eq_one_log_div_le`: the split-prime bound at any
  `σ > 1`.
* `DirichletCharacter.sum_primesLE_filter_eq_one_log_div_le_exp_one`: the split-prime bound at
  `σ = 1 + 1 / log X`, with the factor `e / 2`.
* `DirichletCharacter.exists_sum_primesLE_filter_eq_one_log_div_le`: the uniform form with the
  pole of `-ζ′/ζ` made explicit.

## References

* H. Davenport, *Multiplicative Number Theory*, 3rd ed., Springer GTM 74 (2000), Chapter 14,
  for the nonnegativity of such combinations of logarithmic derivatives at real `σ > 1`.
* OpenAI, *Uniform exclusion of Landau–Siegel zeros*, OpenAI mathematics release of
  1 October 2026, §2, Lemma 2, for the split-prime deduction at `σ = 1 + 1 / log X`.
-/

public section

open ArithmeticFunction LSeries

open scoped LSeries.notation

namespace DirichletCharacter

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {σ : ℝ}

/-- **The Landau combination as a positive series.** For real `σ > 1`,
`-re ζ′/ζ(σ) - re L′/L(σ, χ)` is the sum of `∑ Λ(n) (1 + re χ(n)) / n ^ σ`, a series of
nonnegative terms. -/
theorem hasSum_vonMangoldt_mul_one_add_re_div_rpow (hσ : 1 < σ) :
    HasSum (fun n : ℕ ↦ Λ n * (1 + (χ n).re) / (n : ℝ) ^ σ)
      (-(logDeriv riemannZeta σ).re - (logDeriv (LFunction χ) σ).re) := by
  have hs : 1 < (σ : ℂ).re := by simpa
  have h := Complex.hasSum_re
    ((LSeriesSummable_vonMangoldt hs).hasSum.add (LSeriesSummable_twist_vonMangoldt χ hs).hasSum)
  rw [logDeriv_apply riemannZeta, ← neg_neg (deriv riemannZeta _ / _), ← neg_div,
    ← LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs, χ.logDeriv_LFunction_eq_neg_LSeries hs]
  convert h using 1
  · funext n
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    rw [term_of_ne_zero hn, term_of_ne_zero hn, ← add_div, ← Complex.ofReal_natCast n,
      ← Complex.ofReal_cpow n.cast_nonneg, Complex.div_ofReal_re]
    simp only [Pi.mul_apply, Complex.add_re, Complex.ofReal_re, Complex.re_mul_ofReal]
    ring
  · simp only [Complex.neg_re, neg_neg, sub_neg_eq_add, Complex.add_re, LSeries]

/-- Every finite partial sum of the positive series `∑ Λ(n) (1 + re χ(n)) / n ^ σ` is at most
`-re ζ′/ζ(σ) - re L′/L(σ, χ)`, for real `σ > 1`. -/
theorem sum_vonMangoldt_mul_one_add_re_div_rpow_le (hσ : 1 < σ) (s : Finset ℕ) :
    ∑ n ∈ s, Λ n * (1 + (χ n).re) / (n : ℝ) ^ σ ≤
      -(logDeriv riemannZeta σ).re - (logDeriv (LFunction χ) σ).re :=
  sum_le_hasSum s (fun n _ ↦ div_nonneg (mul_nonneg vonMangoldt_nonneg (χ.one_add_re_nonneg n))
    (Real.rpow_nonneg n.cast_nonneg σ))
    (χ.hasSum_vonMangoldt_mul_one_add_re_div_rpow hσ)

/-- **Weighted primes and the Landau combination.** For real `σ > 1` and `X ≥ 0`, the weighted
prime sum `∑_{p ≤ X} (1 + re χ(p)) log p / p` is at most
`X ^ (σ - 1) (-re ζ′/ζ(σ) - re L′/L(σ, χ))`. -/
theorem weightedPrimeSum_one_add_re_le (hσ : 1 < σ) {X : ℝ} (hX : 0 ≤ X) :
    TauCeti.weightedPrimeSum (fun p ↦ 1 + (χ p).re) X ≤
      X ^ (σ - 1) * (-(logDeriv riemannZeta σ).re - (logDeriv (LFunction χ) σ).re) := by
  calc TauCeti.weightedPrimeSum (fun p ↦ 1 + (χ p).re) X
      ≤ X ^ (σ - 1) * ∑ p ∈ Nat.primesLE ⌊X⌋₊, Real.log p * (1 + (χ p).re) / (p : ℝ) ^ σ :=
        TauCeti.weightedPrimeSum_le_rpow_mul_sum (fun p _ ↦ χ.one_add_re_nonneg p) hσ.le X
    _ = X ^ (σ - 1) * ∑ p ∈ Nat.primesLE ⌊X⌋₊, Λ p * (1 + (χ p).re) / (p : ℝ) ^ σ := by
        congr 1
        exact Finset.sum_congr rfl fun p hp ↦ by
          rw [vonMangoldt_apply_prime (Nat.prime_of_mem_primesLE hp)]
    _ ≤ X ^ (σ - 1) * (-(logDeriv riemannZeta σ).re - (logDeriv (LFunction χ) σ).re) :=
        mul_le_mul_of_nonneg_left (χ.sum_vonMangoldt_mul_one_add_re_div_rpow_le hσ _)
          (Real.rpow_nonneg hX _)

/-- **Split primes and the Landau combination.** For real `σ > 1` and `X ≥ 0`, the primes
`p ≤ X` with `χ(p) = 1` satisfy
`∑ log p / p ≤ (X ^ (σ - 1) / 2) (-re ζ′/ζ(σ) - re L′/L(σ, χ))`. -/
theorem sum_primesLE_filter_eq_one_log_div_le (hσ : 1 < σ) {X : ℝ} (hX : 0 ≤ X) :
    ∑ p ∈ (Nat.primesLE ⌊X⌋₊).filter (fun p : ℕ ↦ χ (p : ZMod N) = 1), Real.log p / p ≤
      X ^ (σ - 1) / 2 * (-(logDeriv riemannZeta σ).re - (logDeriv (LFunction χ) σ).re) := by
  set S := (Nat.primesLE ⌊X⌋₊).filter fun p : ℕ ↦ χ (p : ZMod N) = 1
  -- the weight `1 + re χ(p)` is `2` on `S` and nonnegative at every prime
  have hle : 2 * ∑ p ∈ S, Real.log p / p ≤ TauCeti.weightedPrimeSum (fun p ↦ 1 + (χ p).re) X := by
    rw [TauCeti.weightedPrimeSum_def, Finset.mul_sum]
    calc ∑ p ∈ S, 2 * (Real.log p / p) = ∑ p ∈ S, (Real.log p / p) • (1 + (χ p).re) := by
          refine Finset.sum_congr rfl fun p hp ↦ ?_
          rw [(Finset.mem_filter.mp hp).2, Complex.one_re, smul_eq_mul]
          ring
      _ ≤ ∑ p ∈ Nat.primesLE ⌊X⌋₊, (Real.log p / p) • (1 + (χ p).re) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun p _ _ ↦
            smul_nonneg (div_nonneg (Real.log_natCast_nonneg p) p.cast_nonneg)
              (χ.one_add_re_nonneg p)
  linarith [χ.weightedPrimeSum_one_add_re_le hσ hX]

/-- **Split primes at Landau's point.** For `X > 1` and `σ = 1 + 1 / log X`, the primes `p ≤ X`
with `χ(p) = 1` satisfy `∑ log p / p ≤ (e / 2) (-re ζ′/ζ(σ) - re L′/L(σ, χ))`. -/
theorem sum_primesLE_filter_eq_one_log_div_le_exp_one {X : ℝ} (hX : 1 < X) :
    ∑ p ∈ (Nat.primesLE ⌊X⌋₊).filter (fun p : ℕ ↦ χ (p : ZMod N) = 1), Real.log p / p ≤
      Real.exp 1 / 2 * (-(logDeriv riemannZeta ((1 + (Real.log X)⁻¹ : ℝ) : ℂ)).re -
        (logDeriv (LFunction χ) ((1 + (Real.log X)⁻¹ : ℝ) : ℂ)).re) := by
  have hlog : 0 < Real.log X := Real.log_pos hX
  have h := χ.sum_primesLE_filter_eq_one_log_div_le (lt_add_of_pos_right 1 (inv_pos.mpr hlog))
    (zero_le_one.trans hX.le)
  rwa [add_sub_cancel_left, Real.rpow_def_of_pos (zero_lt_one.trans hX),
    mul_inv_cancel₀ hlog.ne'] at h

/-- **Split primes and the pole of `-ζ′/ζ`.** One absolute constant `C` satisfies, for every
positive level `N`, every Dirichlet character `χ` of level `N` and every `X ≥ e`,
`∑_{p ≤ X, χ(p) = 1} log p / p ≤ (e / 2) (log X + C - re L′/L(1 + 1 / log X, χ))`. -/
theorem exists_sum_primesLE_filter_eq_one_log_div_le :
    ∃ C : ℝ, ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (X : ℝ), Real.exp 1 ≤ X →
      ∑ p ∈ (Nat.primesLE ⌊X⌋₊).filter (fun p : ℕ ↦ χ (p : ZMod N) = 1), Real.log p / p ≤
        Real.exp 1 / 2 *
          (Real.log X + C - (logDeriv (LFunction χ) ((1 + (Real.log X)⁻¹ : ℝ) : ℂ)).re) := by
  obtain ⟨C, -, hC⟩ := TauCeti.exists_neg_re_logDeriv_riemannZeta_one_add_le
  refine ⟨C, fun N _ χ X hX ↦ ?_⟩
  have hX1 : 1 < X := (Real.one_lt_exp_iff.mpr one_pos).trans_le hX
  have hlog : 1 ≤ Real.log X := by simpa using Real.log_le_log (Real.exp_pos 1) hX
  have hlog0 : 0 < Real.log X := one_pos.trans_le hlog
  -- the pole of `-ζ′/ζ` at `1` bounds `-re ζ′/ζ(1 + 1 / log X)` by `log X + C`
  have hζ : -(logDeriv riemannZeta ((1 + (Real.log X)⁻¹ : ℝ) : ℂ)).re ≤ Real.log X + C := by
    simpa only [one_div, inv_inv, Complex.ofReal_add, Complex.ofReal_one] using
      hC (Real.log X)⁻¹ (inv_pos.mpr hlog0) (inv_le_one_of_one_le₀ hlog)
  exact (χ.sum_primesLE_filter_eq_one_log_div_le_exp_one hX1).trans
    (mul_le_mul_of_nonneg_left (by linarith) (by positivity))

end DirichletCharacter
