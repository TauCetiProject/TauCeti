/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.Dirichlet
import TauCeti.NumberTheory.LSeries.Twist

/-!
# L-series of power and divisor-sum arithmetic functions

For every `k : ℕ`, twisting the constant sequence `1` by `n ^ k` shifts its `LSeries` by `-k`
(`TauCeti.LSeries.term_mul_natCast_cpow_neg`), so `ArithmeticFunction.pow k` has abscissa of
absolute convergence `k + 1` and L-series `ζ(s - k)` on `Re s > k + 1`. Since
`σ_k = ζ * pow k` as a Dirichlet convolution (`ArithmeticFunction.zeta_mul_pow_eq_sigma`) and
`n ^ k ≤ σ_k(n)` for `n ≥ 1`, the divisor-sum function `σ_k` likewise converges absolutely if and
only if `Re s > k + 1`, has abscissa of absolute convergence `k + 1`, and satisfies
`L(σ_k, s) = ζ(s) ζ(s - k)` on `Re s > k + 1`.

## Main results

* `ArithmeticFunction.LSeriesSummable_pow_iff`, `ArithmeticFunction.abscissaOfAbsConv_pow`,
  `ArithmeticFunction.LSeries_pow_eq_riemannZeta`: convergence half-plane, abscissa `k + 1`, and
  identity `L(pow k, s) = ζ(s - k)` on `Re s > k + 1`.
* `ArithmeticFunction.LSeriesSummable_sigma_iff`, `ArithmeticFunction.abscissaOfAbsConv_sigma`,
  `ArithmeticFunction.LSeries_sigma`: convergence half-plane, abscissa `k + 1`, and factorization
  `L(σ_k, s) = ζ(s) ζ(s - k)` on `Re s > k + 1`.

## References

* F. Diamond and J. Shurman, *A First Course in Modular Forms*, §5.9.
* J.-P. Serre, *A Course in Arithmetic*, Chapter VI, §3.
* The convergence-half-plane and abscissa lemmas follow the pattern of
  `Mathlib/NumberTheory/LSeries/Dirichlet.lean`.
-/

public section

open LSeries
open scoped ArithmeticFunction.zeta ArithmeticFunction.sigma LSeries.notation

namespace ArithmeticFunction

/-- The `n`-th Dirichlet term of `ArithmeticFunction.pow k` at `s` is the `n`-th term of `1` at
`s - k`. -/
theorem term_pow_eq (k : ℕ) (s : ℂ) (n : ℕ) :
    LSeries.term ↗(pow k) s n = LSeries.term 1 (s - k) n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · have hpow : ((pow k n : ℕ) : ℂ) = (1 : ℕ → ℂ) n * (n : ℂ) ^ (-(-(k : ℂ))) := by
      simp [pow_apply, hn, neg_neg]
    simpa only [LSeries.term_of_ne_zero hn, natCoe_apply, hpow, sub_eq_add_neg] using
      TauCeti.LSeries.term_mul_natCast_cpow_neg 1 (-(k : ℂ)) s n

/-- The L-series of `ArithmeticFunction.pow k` at `s` equals the L-series of `1` at `s - k`. -/
theorem LSeries_pow_eq_LSeries_one_sub (k : ℕ) (s : ℂ) :
    L ↗(pow k) s = L 1 (s - k) :=
  tsum_congr (term_pow_eq k s)

/-- The L-series of `ArithmeticFunction.pow k` converges absolutely at `s` if and only if
`k + 1 < s.re`. -/
theorem LSeriesSummable_pow_iff {k : ℕ} {s : ℂ} :
    LSeriesSummable ↗(pow k) s ↔ (k : ℝ) + 1 < s.re := by
  have h : LSeriesSummable ↗(pow k) s ↔ LSeriesSummable 1 (s - k) := by
    simp only [LSeriesSummable, funext (term_pow_eq k s)]
  rw [h, LSeriesSummable_one_iff, Complex.sub_re, Complex.natCast_re]
  exact ⟨fun hs ↦ by linarith, fun hs ↦ by linarith⟩

/-- The abscissa of absolute convergence of `ArithmeticFunction.pow k` is `k + 1`. -/
theorem abscissaOfAbsConv_pow (k : ℕ) :
    abscissaOfAbsConv ↗(pow k) = ((k : ℝ) + 1 : ℝ) := by
  have hset : {x : ℝ | LSeriesSummable ↗(pow k) x} = Set.Ioi ((k : ℝ) + 1) := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_Ioi, LSeriesSummable_pow_iff, Complex.ofReal_re]
  rw [abscissaOfAbsConv, hset, EReal.image_coe_Ioi]
  exact csInf_Ioo <| EReal.coe_lt_top ((k : ℝ) + 1)

/-- On `Re s > k + 1`, the L-series of `ArithmeticFunction.pow k` equals `ζ(s - k)`. -/
theorem LSeries_pow_eq_riemannZeta {k : ℕ} {s : ℂ} (hs : (k : ℝ) + 1 < s.re) :
    L ↗(pow k) s = riemannZeta (s - k) := by
  rw [LSeries_pow_eq_LSeries_one_sub]
  refine LSeries_one_eq_riemannZeta ?_
  rw [Complex.sub_re, Complex.natCast_re]
  linarith

/-- The L-series of the divisor-sum function `σ_k` converges absolutely at `s` if and only if
`k + 1 < s.re`. -/
theorem LSeriesSummable_sigma_iff {k : ℕ} {s : ℂ} :
    LSeriesSummable ↗(σ k) s ↔ (k : ℝ) + 1 < s.re := by
  constructor
  · intro h
    refine LSeriesSummable_pow_iff.mp (.of_norm <| h.norm.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
      fun n ↦ LSeries.norm_term_le s ?_)
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · simp only [Complex.norm_natCast]
      have hle : pow k n ≤ σ k n := by
        simpa [pow_apply, hn, sigma_apply] using
          Finset.single_le_sum (f := fun d ↦ d ^ k) (fun _ _ ↦ Nat.zero_le _)
            (Nat.mem_divisors_self n hn)
      exact_mod_cast hle
  · intro hs
    have hs1 : 1 < s.re := by linarith [Nat.cast_nonneg (α := ℝ) k]
    have hconv : (↗(σ k) : ℕ → ℂ) = ↗ζ ⍟ ↗(pow k) := by
      simp_rw [← zeta_mul_pow_eq_sigma, ← natCoe_apply, natCoe_mul, coe_mul]
    rw [hconv]
    exact (LSeriesSummable_zeta_iff.mpr hs1).convolution (LSeriesSummable_pow_iff.mpr hs)

/-- The abscissa of absolute convergence of the divisor-sum function `σ_k` is `k + 1`. -/
theorem abscissaOfAbsConv_sigma (k : ℕ) :
    abscissaOfAbsConv ↗(σ k) = ((k : ℝ) + 1 : ℝ) := by
  have hset : {x : ℝ | LSeriesSummable ↗(σ k) x} = Set.Ioi ((k : ℝ) + 1) := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_Ioi, LSeriesSummable_sigma_iff, Complex.ofReal_re]
  rw [abscissaOfAbsConv, hset, EReal.image_coe_Ioi]
  exact csInf_Ioo <| EReal.coe_lt_top ((k : ℝ) + 1)

/-- **The L-series of `σ_k`**: on the half-plane `Re s > k + 1`,
`L(σ_k, s) = ζ(s) ζ(s - k)`. -/
theorem LSeries_sigma {k : ℕ} {s : ℂ} (hs : (k : ℝ) + 1 < s.re) :
    L ↗(σ k) s = riemannZeta s * riemannZeta (s - k) := by
  have hs1 : 1 < s.re := by linarith [Nat.cast_nonneg (α := ℝ) k]
  have hconv : (↗(σ k) : ℕ → ℂ) = ↗ζ ⍟ ↗(pow k) := by
    simp_rw [← zeta_mul_pow_eq_sigma, ← natCoe_apply, natCoe_mul, coe_mul]
  rw [hconv, LSeries_convolution' (LSeriesSummable_zeta_iff.mpr hs1)
    (LSeriesSummable_pow_iff.mpr hs), LSeries_zeta_eq_riemannZeta hs1,
    LSeries_pow_eq_riemannZeta hs]

end ArithmeticFunction
