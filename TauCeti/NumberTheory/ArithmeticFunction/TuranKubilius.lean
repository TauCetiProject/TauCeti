/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import TauCeti.NumberTheory.ArithmeticFunction.Additive
import TauCeti.Algebra.BigOperators.Finset.SquaredDeviation
import TauCeti.Algebra.BigOperators.Ring.Finset
import TauCeti.Analysis.SpecialFunctions.Log.Bounds
import TauCeti.Analysis.SpecificLimits.ReciprocalSeries
import TauCeti.Data.Nat.Factorization.ValuationCount
import TauCeti.Data.Nat.Log
import TauCeti.Data.Nat.Prime.Basic
import TauCeti.NumberTheory.Chebyshev.Mertens
import TauCeti.NumberTheory.SumPrimePow

/-!
# The Turán–Kubilius inequality

For any real-valued additive arithmetic function `f : ArithmeticFunction ℝ` and any natural number
`N`, set

* `A = ∑_{p ≤ N} ∑_{1 ≤ k ≤ log_p N} f(p ^ k) / p ^ k`,
* `B = ∑_{p ≤ N} ∑_{1 ≤ k ≤ log_p N} f(p ^ k) ^ 2 / p ^ k`.

The **Turán–Kubilius inequality** bounds the sum of squared deviations of `f` from `A` on
`{1, …, N}` by a universal constant multiple of `N * B`:

`∑ n ∈ Icc 1 N, (f n - A) ^ 2 ≤ 30 * N * B`.

To avoid invoking Mertens' second theorem while keeping an explicit small constant, the proof splits
the prime-power pairs `(p, k)` at `M = Nat.sqrt N`:

* **Small prime powers** (`p ^ k ≤ M`): exact prime-valuation indicators `1_{n.factorization p = k}`
  are centered at their asymptotic density `α(p, k) = 1 / p ^ k - 1 / p ^ (k + 1)`. Inclusion–
  exclusion over multiples of `p ^ k` and `p ^ (k + 1)` controls single-prime counts to within `1`
  and coprime pair counts (`p ≠ q`) to within `2`, giving pairwise correlation at most `3`. By
  Cauchy–Schwarz and `∑_{q ≤ M} q ≤ M ^ 2 ≤ N`, the centered small part has sum of squares at most
  `4 * N * B_S`, and shifting from `α(p, k)` to `1 / p ^ k` costs at most a convergent higher-power
  geometric tail, yielding `≤ 10 * N * B_S`.
* **Large prime powers** (`M < p ^ k ≤ N`): since `(M + 1) ^ 2 > N`, at most one large prime power
  can occur in the canonical factorization of any `n ∈ Icc 1 N`. Hence
  `∑_{n ≤ N} f_L(n) ^ 2 ≤ N * B_L`, and `Finset.sum_sub_sq_le_sum_sq_add_div` plus Cauchy–Schwarz
  reduce `∑_{n ≤ N} (f_L(n) - A_L) ^ 2` to bounding `∑_{(p, k) ∈ L} 1 / p ^ k`: exponents `k ≥ 2`
  contribute at most `1` by `Nat.sum_primesLE_sum_Icc_two_inv_pow_le_one`, while primes
  `M + 1 ≤ p ≤ N` contribute at most `11` by `Chebyshev.sum_primesLE_filter_ge_inv_le`.

Combining the two parts via `(u + v) ^ 2 ≤ 2 * u ^ 2 + 2 * v ^ 2` gives constant `26 ≤ 30` for all
`N : ℕ` (including `N = 0, 1`, with no `2 ≤ N` side-condition). For strongly additive functions
(`f (p ^ k) = f p` for `k ≥ 1`), stripping the convergent `k ≥ 2` geometric tails yields the
distinct-prime form over `Nat.primesLE N`, which specializes at `ω = cardDistinctFactors` to
Turán's original 1934 variance bound.

## Main results

* `ArithmeticFunction.IsAdditive.sum_Icc_sub_sum_primesLE_Icc_log_sq_le`,
  `ArithmeticFunction.IsAdditive.sum_Icc_sub_sq_le`: **the Turán–Kubilius inequality** with
  constant `30`, in both `Icc 1 (p.log N)` and `if p ^ k ≤ N` cutoff forms, for all `N : ℕ`.
* `ArithmeticFunction.IsStronglyAdditive.sum_primesLE_Icc_log_sq_le`,
  `ArithmeticFunction.IsStronglyAdditive.sum_primesLE_Icc_log_sub_sum_primesLE`,
  `ArithmeticFunction.IsStronglyAdditive.sum_primesLE_Icc_log_sub_sum_primesLE_sq_le`: comparison
  between full prime-power sums and distinct-prime sums for strongly additive functions.
* `ArithmeticFunction.IsStronglyAdditive.sum_Icc_sub_sq_le`: distinct-prime Turán–Kubilius bound
  for strongly additive functions.
* `ArithmeticFunction.sum_Icc_cardDistinctFactors_sub_sq_le`: Turán's inequality (1934) for `ω(n)`.

## References

* C. Elsholtz and T. Tao, *Counting the number of solutions to the Erdős–Straus equation on unit
  fractions*, Appendix A, Lemmas A.2–A.3.
* J. Kubilius, *Probabilistic Methods in the Theory of Numbers*, Chapter III.
* P. Turán, *On a theorem of Hardy and Ramanujan*, J. London Math. Soc. **9** (1934), 274–276.
-/

public section

open Finset

namespace ArithmeticFunction

/-! ### Centered single-prime valuation parts -/

section ValuationCounts

/-- Asymptotic density `1 / p ^ k - 1 / p ^ (k + 1)` of `{n : v_p(n) = k}`. -/
private noncomputable def valDensity (p k : ℕ) : ℝ :=
  1 / (p : ℝ) ^ k - 1 / (p : ℝ) ^ (k + 1)

private lemma valDensity_eq (p k : ℕ) :
    valDensity p k = 1 / (p : ℝ) ^ k - 1 / (p : ℝ) ^ (k + 1) := rfl

/-- Centered prime-power valuation sum at a single prime `p` up to cutoff `M`. -/
private noncomputable def centeredPrimePart (M : ℕ) (f : ArithmeticFunction ℝ) (p n : ℕ) : ℝ :=
  ∑ k ∈ Icc 1 (p.log M),
    f (p ^ k) * ((if n.factorization p = k then (1 : ℝ) else 0) - valDensity p k)

private lemma centeredPrimePart_apply (M : ℕ) (f : ArithmeticFunction ℝ) (p n : ℕ) :
    centeredPrimePart M f p n = ∑ k ∈ Icc 1 (p.log M),
      f (p ^ k) * ((if n.factorization p = k then (1 : ℝ) else 0) - valDensity p k) := rfl

/-- Single-prime diagonal sum of squares for a centered prime-power linear combination. -/
private lemma sum_centered_single_prime_sq_le (N M : ℕ) (f : ArithmeticFunction ℝ)
    {p : ℕ} (hp : p.Prime) :
    ∑ n ∈ Icc 1 N, centeredPrimePart M f p n ^ 2 ≤
      (N : ℝ) * (∑ k ∈ Icc 1 (p.log M), f (p ^ k) ^ 2 / (p : ℝ) ^ k) +
        (∑ k ∈ Icc 1 (p.log M), |f (p ^ k)|) ^ 2 := by
  set K := Icc 1 (p.log M)
  set g : ℕ → ℝ := fun n ↦ ∑ k ∈ K, if n.factorization p = k then f (p ^ k) else 0
  set μ : ℝ := ∑ k ∈ K, f (p ^ k) * valDensity p k
  have hY : ∀ n, centeredPrimePart M f p n = g n - μ := fun n ↦ by
    rw [centeredPrimePart_apply]
    simp only [K, g, μ, mul_sub, sum_sub_distrib, mul_ite, mul_one, mul_zero]
  have hg2_le : ∑ n ∈ Icc 1 N, g n ^ 2 ≤ (N : ℝ) * ∑ k ∈ K, f (p ^ k) ^ 2 / (p : ℝ) ^ k := by
    have hgsq : ∀ n, g n ^ 2 = ∑ k ∈ K, if n.factorization p = k then f (p ^ k) ^ 2 else 0 :=
      fun n ↦ K.sum_ite_pow_of_subsingleton (n.factorization p = ·) (fun k ↦ f (p ^ k)) two_ne_zero
        fun _ _ _ _ h1 h2 ↦ h1.symm.trans h2
    simp_rw [hgsq]
    rw [sum_comm, mul_sum]
    refine sum_le_sum fun k _ ↦ ?_
    calc (∑ n ∈ Icc 1 N, if n.factorization p = k then f (p ^ k) ^ 2 else 0)
        = f (p ^ k) ^ 2 * ∑ n ∈ Icc 1 N, (if n.factorization p = k then (1 : ℝ) else 0) := by
          simp only [mul_sum, mul_boole]
      _ ≤ f (p ^ k) ^ 2 * ((N : ℝ) / (p : ℝ) ^ k) :=
          mul_le_mul_of_nonneg_left (Nat.sum_Icc_ite_factorization_le N p k) (sq_nonneg _)
      _ = (N : ℝ) * (f (p ^ k) ^ 2 / (p : ℝ) ^ k) := by ring
  set δ : ℝ := (∑ n ∈ Icc 1 N, g n) - (N : ℝ) * μ
  have hδ_abs : |δ| ≤ ∑ k ∈ K, |f (p ^ k)| := by
    have hδ_eq : δ = ∑ k ∈ K, f (p ^ k) *
        ((∑ n ∈ Icc 1 N, (if n.factorization p = k then (1 : ℝ) else 0)) -
          (N : ℝ) * valDensity p k) := by
      simp only [δ, g, μ, mul_sum]
      rw [sum_comm, ← sum_sub_distrib]
      refine sum_congr rfl fun k _ ↦ ?_
      rw [mul_sub, mul_sum]
      simp only [mul_boole]
      ring
    rw [hδ_eq]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k _ ↦ ?_)
    rw [abs_mul, valDensity_eq]
    exact mul_le_of_le_one_right (abs_nonneg _)
      (Nat.abs_sum_Icc_ite_factorization_sub_lt_one N hp k).le
  have hvar : ∑ n ∈ Icc 1 N, centeredPrimePart M f p n ^ 2 ≤
      (∑ n ∈ Icc 1 N, g n ^ 2) + δ ^ 2 / (N : ℝ) := by
    simpa [hY, δ] using (Icc 1 N).sum_sub_sq_le_sum_sq_add_div g μ
  have hδ_div : δ ^ 2 / (N : ℝ) ≤ (∑ k ∈ K, |f (p ^ k)|) ^ 2 := by
    rcases eq_or_ne N 0 with rfl | hN0
    · simp [sq_nonneg]
    · exact (div_le_self (sq_nonneg δ) (mod_cast Nat.pos_of_ne_zero hN0)).trans
        ((sq_abs δ).symm ▸ pow_le_pow_left₀ (abs_nonneg δ) hδ_abs 2)
  exact hvar.trans (add_le_add hg2_le hδ_div)

end ValuationCounts

/-! ### Small and large prime-power variance bounds -/

section SplitBounds

/-- Small-prime-power part `f_S(n)` up to cutoff `M`. -/
private def smallPart (M : ℕ) (f : ArithmeticFunction ℝ) (n : ℕ) : ℝ :=
  ∑ p ∈ Nat.primesLE M, ∑ k ∈ Icc 1 (p.log M),
    if n.factorization p = k then f (p ^ k) else 0

private lemma smallPart_apply (M : ℕ) (f : ArithmeticFunction ℝ) (n : ℕ) :
    smallPart M f n = ∑ p ∈ Nat.primesLE M, ∑ k ∈ Icc 1 (p.log M),
      if n.factorization p = k then f (p ^ k) else 0 := rfl

/-- Prime-power expectation proxy `∑_{p ≤ M} ∑_{1 ≤ k ≤ log_p M} f(p ^ k) / p ^ k`. -/
private noncomputable def smallMean (M : ℕ) (f : ArithmeticFunction ℝ) : ℝ :=
  ∑ p ∈ Nat.primesLE M, ∑ k ∈ Icc 1 (p.log M), f (p ^ k) / (p : ℝ) ^ k

private lemma smallMean_eq (M : ℕ) (f : ArithmeticFunction ℝ) :
    smallMean M f = ∑ p ∈ Nat.primesLE M, ∑ k ∈ Icc 1 (p.log M), f (p ^ k) / (p : ℝ) ^ k := rfl

/-- Prime-power variance proxy `∑_{p ≤ M} ∑_{1 ≤ k ≤ log_p M} f(p ^ k) ^ 2 / p ^ k`. -/
private noncomputable def smallVar (M : ℕ) (f : ArithmeticFunction ℝ) : ℝ :=
  ∑ p ∈ Nat.primesLE M, ∑ k ∈ Icc 1 (p.log M), f (p ^ k) ^ 2 / (p : ℝ) ^ k

private lemma smallVar_eq (M : ℕ) (f : ArithmeticFunction ℝ) :
    smallVar M f = ∑ p ∈ Nat.primesLE M, ∑ k ∈ Icc 1 (p.log M),
      f (p ^ k) ^ 2 / (p : ℝ) ^ k := rfl

/-- Distinct-prime off-diagonal correlation bound for centered small-prime-power sums. -/
private lemma sum_small_centered_mul_le (N M : ℕ) (f : ArithmeticFunction ℝ)
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    ∑ n ∈ Icc 1 N, centeredPrimePart M f p n * centeredPrimePart M f q n ≤
      3 * ((∑ k ∈ Icc 1 (p.log M), |f (p ^ k)|) * ∑ l ∈ Icc 1 (q.log M), |f (q ^ l)|) := by
  have hexp : ∑ n ∈ Icc 1 N, centeredPrimePart M f p n * centeredPrimePart M f q n =
      ∑ k ∈ Icc 1 (p.log M), ∑ l ∈ Icc 1 (q.log M), f (p ^ k) * f (q ^ l) *
        ∑ n ∈ Icc 1 N, ((if n.factorization p = k then (1 : ℝ) else 0) - valDensity p k) *
          ((if n.factorization q = l then (1 : ℝ) else 0) - valDensity q l) := by
    trans ∑ n ∈ Icc 1 N, ∑ k ∈ Icc 1 (p.log M), ∑ l ∈ Icc 1 (q.log M),
        f (p ^ k) * f (q ^ l) *
          (((if n.factorization p = k then (1 : ℝ) else 0) - valDensity p k) *
            ((if n.factorization q = l then (1 : ℝ) else 0) - valDensity q l))
    · refine sum_congr rfl fun n _ ↦ ?_
      rw [centeredPrimePart_apply, centeredPrimePart_apply, sum_mul_sum]
      exact sum_congr rfl fun _ _ ↦ sum_congr rfl fun _ _ ↦ by ring
    · rw [sum_comm]
      refine sum_congr rfl fun k _ ↦ ?_
      rw [sum_comm]
      exact sum_congr rfl fun l _ ↦ (mul_sum _ _ _).symm
  rw [hexp]
  calc _ ≤ ∑ k ∈ Icc 1 (p.log M), ∑ l ∈ Icc 1 (q.log M), |f (p ^ k)| * |f (q ^ l)| * 3 := by
        refine sum_le_sum fun k _ ↦ sum_le_sum fun l _ ↦ ?_
        set Ckl := ∑ n ∈ Icc 1 N,
          ((if n.factorization p = k then (1 : ℝ) else 0) - valDensity p k) *
            ((if n.factorization q = l then (1 : ℝ) else 0) - valDensity q l)
        have hcorr : |Ckl| ≤ 3 := by
          simp only [Ckl, valDensity_eq]
          exact (Nat.abs_sum_Icc_ite_factorization_sub_mul_sub_lt_three N hp hq hpq k l).le
        calc f (p ^ k) * f (q ^ l) * Ckl
            ≤ |f (p ^ k) * f (q ^ l) * Ckl| := le_abs_self _
          _ = |f (p ^ k)| * |f (q ^ l)| * |Ckl| := by rw [abs_mul, abs_mul]
          _ ≤ |f (p ^ k)| * |f (q ^ l)| * 3 := mul_le_mul_of_nonneg_left hcorr (by positivity)
    _ = 3 * ((∑ k ∈ Icc 1 (p.log M), |f (p ^ k)|) * ∑ l ∈ Icc 1 (q.log M), |f (q ^ l)|) := by
        rw [sum_mul_sum, mul_sum]
        refine sum_congr rfl fun _ _ ↦ ?_
        rw [mul_sum]
        exact sum_congr rfl fun _ _ ↦ by ring

/-- Cauchy–Schwarz bound `(∑_{p^k ≤ √N} |f(p^k)|) ^ 2 ≤ N * B_S` via `∑_{q ≤ √N} q ≤ N`. -/
private lemma sum_primesLE_abs_pow_sq_le (N : ℕ) (f : ArithmeticFunction ℝ) :
    (∑ p ∈ Nat.primesLE N.sqrt, ∑ k ∈ Icc 1 (p.log N.sqrt), |f (p ^ k)|) ^ 2 ≤
      (N : ℝ) * smallVar N.sqrt f := by
  set M := N.sqrt
  have hW_reg : (∑ p ∈ Nat.primesLE M, ∑ k ∈ Icc 1 (p.log M), |f (p ^ k)|) =
      ∑ q ∈ Icc 1 M, (if IsPrimePow q then |f q| else 0) := by
    symm
    refine (Nat.sum_Icc_eq_sum_primesLE_sum_Icc_log (fun _ hn ↦ ite_eq_right hn) M).trans ?_
    exact sum_congr rfl fun p hp ↦ sum_congr rfl fun k hk ↦ ite_eq_left
      ((Nat.prime_of_mem_primesLE hp).isPrimePow.pow (by have := (mem_Icc.mp hk).1; lia))
  have hB_reg : smallVar M f =
      ∑ q ∈ Icc 1 M, (if IsPrimePow q then f q ^ 2 / (q : ℝ) else 0) := by
    rw [smallVar_eq]
    symm
    refine (Nat.sum_Icc_eq_sum_primesLE_sum_Icc_log (fun _ hn ↦ ite_eq_right hn) M).trans ?_
    refine sum_congr rfl fun p hp ↦ sum_congr rfl fun k hk ↦ ?_
    rw [ite_eq_left ((Nat.prime_of_mem_primesLE hp).isPrimePow.pow
      (by have := (mem_Icc.mp hk).1; lia)), Nat.cast_pow]
  rw [hW_reg, hB_reg, mul_comm]
  refine (sum_sq_le_sum_mul_sum_of_sq_le_mul (Icc 1 M)
    (f := fun q ↦ if IsPrimePow q then f q ^ 2 / (q : ℝ) else 0) (g := fun q ↦ (q : ℝ))
    (fun _ _ ↦ by split_ifs <;> positivity) (fun _ _ ↦ by positivity) fun q hq ↦ ?_).trans ?_
  · split_ifs
    · have hq0 : (q : ℝ) ≠ 0 := mod_cast (by have := (mem_Icc.mp hq).1; lia : q ≠ 0)
      rw [sq_abs, div_mul_cancel₀ _ hq0]
    · simp
  · refine mul_le_mul_of_nonneg_left ?_ (sum_nonneg fun _ _ ↦ by split_ifs <;> positivity)
    have hsq : ∑ q ∈ Icc 1 M, q ≤ N := by
      calc ∑ q ∈ Icc 1 M, q ≤ #(Icc 1 M) • M :=
            sum_le_card_nsmul (Icc 1 M) id M fun q hq ↦ (mem_Icc.mp hq).2
        _ = M * M := by simp
        _ ≤ N := Nat.sqrt_le N
    rw [← Nat.cast_sum]
    exact_mod_cast hsq

/-- Shifting `valDensity p k = 1 / p ^ k - 1 / p ^ (k + 1)` to `1 / p ^ k` changes the small-prime
expectation by at most `√B_S`. -/
private lemma small_density_shift_sq_le (M : ℕ) (f : ArithmeticFunction ℝ) :
    (smallMean M f -
        ∑ p ∈ Nat.primesLE M, ∑ k ∈ Icc 1 (p.log M), f (p ^ k) * valDensity p k) ^ 2 ≤
      smallVar M f := by
  set S := (Nat.primesLE M).sigma fun p ↦ Icc 1 (p.log M)
  set μS := ∑ p ∈ Nat.primesLE M, ∑ k ∈ Icc 1 (p.log M), f (p ^ k) * valDensity p k
  have hB_nonneg : 0 ≤ smallVar M f := by
    rw [smallVar_eq]
    exact sum_nonneg fun _ _ ↦ sum_nonneg fun _ _ ↦ div_nonneg (sq_nonneg _) (by positivity)
  have hdiff : smallMean M f - μS = ∑ x ∈ S, f (x.1 ^ x.2) / (x.1 : ℝ) ^ (x.2 + 1) := by
    rw [sum_sigma, smallMean_eq]
    simp only [μS, valDensity_eq, ← sum_sub_distrib]
    exact sum_congr rfl fun _ _ ↦ sum_congr rfl fun _ _ ↦ by ring
  have hBS_eq : smallVar M f = ∑ x ∈ S, f (x.1 ^ x.2) ^ 2 / (x.1 : ℝ) ^ x.2 := by
    rw [smallVar_eq, sum_sigma]
  have hcs : (∑ x ∈ S, |f (x.1 ^ x.2)| / (x.1 : ℝ) ^ (x.2 + 1)) ^ 2 ≤
      smallVar M f * ∑ x ∈ S, ((x.1 : ℝ) ^ (x.2 + 2))⁻¹ := by
    rw [hBS_eq]
    refine sum_sq_le_sum_mul_sum_of_sq_le_mul S (fun _ _ ↦ by positivity)
      (fun _ _ ↦ by positivity) fun x hx ↦ ?_
    have hp0 : (x.1 : ℝ) ≠ 0 := mod_cast (Nat.prime_of_mem_primesLE (mem_sigma.mp hx).1).ne_zero
    rw [div_pow, sq_abs]; field_simp; exact le_of_eq (by ring)
  have htail : ∑ x ∈ S, ((x.1 : ℝ) ^ (x.2 + 2))⁻¹ ≤ 1 := by
    rw [sum_sigma]
    refine (sum_le_sum fun p _ ↦ ?_).trans
      (Nat.sum_primesLE_sum_Icc_two_inv_pow_le_one M fun p ↦ p.log M + 2)
    calc ∑ k ∈ Icc 1 (p.log M), ((p : ℝ) ^ (k + 2))⁻¹
        = ∑ j ∈ (Icc 1 (p.log M)).map ⟨(· + 2), add_left_injective 2⟩, ((p : ℝ) ^ j)⁻¹ := by
          rw [sum_map]; simp only [Function.Embedding.coeFn_mk]
      _ ≤ ∑ j ∈ Icc 2 (p.log M + 2), ((p : ℝ) ^ j)⁻¹ := by
          refine sum_le_sum_of_subset_of_nonneg (fun j hj ↦ ?_) fun _ _ _ ↦ by positivity
          obtain ⟨k, hk, rfl⟩ := mem_map.mp hj
          simp only [Function.Embedding.coeFn_mk, mem_Icc] at hk ⊢; lia
  have habs : |smallMean M f - μS| ≤ ∑ x ∈ S, |f (x.1 ^ x.2)| / (x.1 : ℝ) ^ (x.2 + 1) := by
    rw [hdiff]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun x _ ↦ ?_)
    have hx0 : (0 : ℝ) ≤ (x.1 : ℝ) ^ (x.2 + 1) := by positivity
    rw [abs_div, abs_of_nonneg hx0]
  calc (smallMean M f - μS) ^ 2 = |smallMean M f - μS| ^ 2 := (sq_abs _).symm
    _ ≤ (∑ x ∈ S, |f (x.1 ^ x.2)| / (x.1 : ℝ) ^ (x.2 + 1)) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) habs 2
    _ ≤ smallVar M f * ∑ x ∈ S, ((x.1 : ℝ) ^ (x.2 + 2))⁻¹ := hcs
    _ ≤ smallVar M f * 1 := mul_le_mul_of_nonneg_left htail hB_nonneg
    _ = smallVar M f := mul_one _

/-- Small prime powers `p ^ k ≤ M` (`M = Nat.sqrt N`) satisfy
`∑_{n ≤ N} (f_S(n) - A_S) ^ 2 ≤ 10 * N * B_S`. -/
private lemma sum_small_prime_powers_sub_sq_le (N : ℕ) (f : ArithmeticFunction ℝ) :
    ∑ n ∈ Icc 1 N, (smallPart N.sqrt f n - smallMean N.sqrt f) ^ 2 ≤
      10 * (N : ℝ) * smallVar N.sqrt f := by
  set M := N.sqrt
  set μS : ℝ := ∑ p ∈ Nat.primesLE M, ∑ k ∈ Icc 1 (p.log M), f (p ^ k) * valDensity p k
  set W : ℕ → ℝ := fun p ↦ ∑ k ∈ Icc 1 (p.log M), |f (p ^ k)|
  have hY_sum : ∀ n, ∑ p ∈ Nat.primesLE M, centeredPrimePart M f p n =
      smallPart M f n - μS := fun n ↦ by
    rw [smallPart_apply]
    simp only [centeredPrimePart_apply, μS, mul_sub, sum_sub_distrib, mul_ite, mul_one, mul_zero]
  have hcentered : ∑ n ∈ Icc 1 N, (smallPart M f n - μS) ^ 2 ≤
      (N : ℝ) * smallVar M f + 3 * (∑ p ∈ Nat.primesLE M, W p) ^ 2 := by
    calc ∑ n ∈ Icc 1 N, (smallPart M f n - μS) ^ 2
        = ∑ p ∈ Nat.primesLE M, ∑ q ∈ Nat.primesLE M,
            ∑ n ∈ Icc 1 N, centeredPrimePart M f p n * centeredPrimePart M f q n := by
          simp_rw [← hY_sum, sq, sum_mul_sum]
          rw [sum_comm]
          exact sum_congr rfl fun _ _ ↦ sum_comm
      _ ≤ ∑ p ∈ Nat.primesLE M, ∑ q ∈ Nat.primesLE M,
            ((if p = q then
                (N : ℝ) * ∑ k ∈ Icc 1 (p.log M), f (p ^ k) ^ 2 / (p : ℝ) ^ k else 0) +
              3 * (W p * W q)) := by
          refine sum_le_sum fun p hp ↦ sum_le_sum fun q hq ↦ ?_
          by_cases hpq : p = q
          · subst hpq
            simp only [ite_true, ← sq]
            have hdiag := sum_centered_single_prime_sq_le N M f (Nat.prime_of_mem_primesLE hp)
            linarith [sq_nonneg (W p)]
          · simp only [hpq, ite_false, zero_add]
            exact sum_small_centered_mul_le N M f (Nat.prime_of_mem_primesLE hp)
              (Nat.prime_of_mem_primesLE hq) hpq
      _ = (N : ℝ) * smallVar M f + 3 * (∑ p ∈ Nat.primesLE M, W p) ^ 2 := by
          simp only [sum_add_distrib]
          congr 1
          · rw [smallVar_eq, mul_sum]
            exact sum_congr rfl fun p hp ↦ sum_ite_eq_of_mem (Nat.primesLE M) p _ hp
          · rw [sq, sum_mul_sum, mul_sum]
            refine sum_congr rfl fun _ _ ↦ ?_
            rw [mul_sum]
  have hW_sq : (∑ p ∈ Nat.primesLE M, W p) ^ 2 ≤ (N : ℝ) * smallVar M f :=
    sum_primesLE_abs_pow_sq_le N f
  have hshift_sq : (smallMean M f - μS) ^ 2 ≤ smallVar M f := small_density_shift_sq_le M f
  -- Combine `2 * (1 + 3) * N * BS + 2 * N * BS = 10 * N * BS`.
  calc ∑ n ∈ Icc 1 N, (smallPart M f n - smallMean M f) ^ 2
      ≤ ∑ n ∈ Icc 1 N,
          (2 * (smallPart M f n - μS) ^ 2 + 2 * (smallMean M f - μS) ^ 2) :=
        sum_le_sum fun n _ ↦ by
          nlinarith [sq_nonneg ((smallPart M f n - μS) + (smallMean M f - μS))]
    _ = 2 * (∑ n ∈ Icc 1 N, (smallPart M f n - μS) ^ 2) +
          2 * (N : ℝ) * (smallMean M f - μS) ^ 2 := by
        simp only [sum_add_distrib, ← mul_sum, sum_const, Nat.card_Icc, add_tsub_cancel_right,
          nsmul_eq_mul]
        ring
    _ ≤ 2 * ((N : ℝ) * smallVar M f + 3 * ((N : ℝ) * smallVar M f)) +
          2 * (N : ℝ) * smallVar M f := by
        gcongr
        exact hcentered.trans (by linarith)
    _ = 10 * (N : ℝ) * smallVar M f := by ring

/-- Prime-power pairs `(p, k)` with `p ≤ N` prime, `1 ≤ k ≤ p.log N`, and `N.sqrt < p ^ k`. -/
private def largePrimePowers (N : ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  ((Nat.primesLE N).sigma fun p ↦ Icc 1 (p.log N)).filter fun x ↦ N.sqrt < x.1 ^ x.2

private lemma largePrimePowers_eq (N : ℕ) :
    largePrimePowers N =
      ((Nat.primesLE N).sigma fun p ↦ Icc 1 (p.log N)).filter fun x ↦ N.sqrt < x.1 ^ x.2 := rfl

private lemma prime_of_mem_largePrimePowers {N : ℕ} {x : Σ _ : ℕ, ℕ}
    (hx : x ∈ largePrimePowers N) : x.1.Prime := by
  rw [largePrimePowers_eq] at hx
  exact Nat.prime_of_mem_primesLE (mem_sigma.mp (mem_filter.mp hx).1).1

/-- Large-prime-power part `f_L(n)` over `largePrimePowers N`. -/
private def largePart (N : ℕ) (f : ArithmeticFunction ℝ) (n : ℕ) : ℝ :=
  ∑ x ∈ largePrimePowers N, if n.factorization x.1 = x.2 then f (x.1 ^ x.2) else 0

private lemma largePart_apply (N : ℕ) (f : ArithmeticFunction ℝ) (n : ℕ) :
    largePart N f n =
      ∑ x ∈ largePrimePowers N, if n.factorization x.1 = x.2 then f (x.1 ^ x.2) else 0 := rfl

/-- Expectation proxy `A_L` over `largePrimePowers N`. -/
private noncomputable def largeMean (N : ℕ) (f : ArithmeticFunction ℝ) : ℝ :=
  ∑ x ∈ largePrimePowers N, f (x.1 ^ x.2) / (x.1 : ℝ) ^ x.2

private lemma largeMean_eq (N : ℕ) (f : ArithmeticFunction ℝ) :
    largeMean N f = ∑ x ∈ largePrimePowers N, f (x.1 ^ x.2) / (x.1 : ℝ) ^ x.2 := rfl

/-- Variance proxy `B_L` over `largePrimePowers N`. -/
private noncomputable def largeVar (N : ℕ) (f : ArithmeticFunction ℝ) : ℝ :=
  ∑ x ∈ largePrimePowers N, f (x.1 ^ x.2) ^ 2 / (x.1 : ℝ) ^ x.2

private lemma largeVar_eq (N : ℕ) (f : ArithmeticFunction ℝ) :
    largeVar N f = ∑ x ∈ largePrimePowers N, f (x.1 ^ x.2) ^ 2 / (x.1 : ℝ) ^ x.2 := rfl

/-- At most one prime power exceeding `Nat.sqrt N` can exactly divide `n ∈ Icc 1 N`. -/
private lemma large_prime_powers_subsingleton {N n : ℕ} (hn : n ∈ Icc 1 N) :
    ∀ x ∈ largePrimePowers N, ∀ y ∈ largePrimePowers N,
      n.factorization x.1 = x.2 → n.factorization y.1 = y.2 → x = y := by
  intro x hx y hy hnx hny
  have hp : x.1.Prime := prime_of_mem_largePrimePowers hx
  have hq : y.1.Prime := prime_of_mem_largePrimePowers hy
  have hn0 : n ≠ 0 := by have := (mem_Icc.mp hn).1; lia
  rw [largePrimePowers_eq] at hx hy
  have hx_gt : N.sqrt + 1 ≤ x.1 ^ x.2 := (mem_filter.mp hx).2
  have hy_gt : N.sqrt + 1 ≤ y.1 ^ y.2 := (mem_filter.mp hy).2
  have hlt : n < x.1 ^ x.2 * y.1 ^ y.2 :=
    (mem_Icc.mp hn).2.trans_lt ((Nat.lt_succ_sqrt N).trans_le (Nat.mul_le_mul hx_gt hy_gt))
  have hpq : x.1 = y.1 :=
    hp.eq_of_pow_dvd_of_lt_mul hq hn0 (hnx ▸ Nat.ordProj_dvd n x.1)
      (hny ▸ Nat.ordProj_dvd n y.1) hlt
  exact Sigma.ext hpq (heq_of_eq (by rw [← hnx, ← hny, hpq]))

/-- Large primes (`k = 1`, `N.sqrt < p ≤ N`) have reciprocal sum at most `11`. -/
private lemma sum_large_prime_powers_exp_one_inv_le (N : ℕ) :
    ∑ x ∈ (largePrimePowers N).filter (fun x ↦ x.2 = 1), ((x.1 : ℝ) ^ x.2)⁻¹ ≤ 11 := by
  set L := largePrimePowers N
  have hinj : ∀ x ∈ L.filter (fun x ↦ x.2 = 1), ∀ y ∈ L.filter (fun x ↦ x.2 = 1),
      x.1 = y.1 → x = y := fun x hx y hy h ↦
    Sigma.ext h (heq_of_eq ((mem_filter.mp hx).2.trans (mem_filter.mp hy).2.symm))
  have himg : ∑ x ∈ L.filter (fun x ↦ x.2 = 1), ((x.1 : ℝ) ^ x.2)⁻¹ ≤
      ∑ p ∈ (Nat.primesLE N).filter (N.sqrt < ·), (p : ℝ)⁻¹ := by
    calc ∑ x ∈ L.filter (fun x ↦ x.2 = 1), ((x.1 : ℝ) ^ x.2)⁻¹
        = ∑ p ∈ (L.filter (fun x ↦ x.2 = 1)).image Sigma.fst, (p : ℝ)⁻¹ := by
          rw [sum_image hinj]
          exact sum_congr rfl fun x hx ↦ by rw [(mem_filter.mp hx).2, pow_one]
      _ ≤ ∑ p ∈ (Nat.primesLE N).filter (N.sqrt < ·), (p : ℝ)⁻¹ := by
          refine sum_le_sum_of_subset_of_nonneg (fun p hp ↦ ?_) fun _ _ _ ↦ by positivity
          obtain ⟨⟨p, k⟩, hx, rfl⟩ := mem_image.mp hp
          obtain ⟨hxL, rfl⟩ := mem_filter.mp hx
          simp only [L, largePrimePowers_eq] at hxL
          obtain ⟨hxsig, hxgt⟩ := mem_filter.mp hxL
          exact mem_filter.mpr ⟨(mem_sigma.mp hxsig).1, by simpa using hxgt⟩
  refine himg.trans ?_
  rcases lt_or_ge N 4 with hN4 | hN4
  · have hsub : (Nat.primesLE N).filter (N.sqrt < ·) ⊆ Icc 1 3 := fun p hp ↦ by
      have hp' := (mem_filter.mp hp).1
      exact mem_Icc.mpr ⟨(Nat.prime_of_mem_primesLE hp').pos,
        (Nat.le_of_mem_primesLE hp').trans (by lia)⟩
    refine (sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ ↦ by positivity).trans ?_
    norm_num [sum_Icc_succ_top]
  · set m := N.sqrt + 1
    have hm3 : 3 ≤ m := by have := Nat.le_sqrt.mpr (by lia : 2 * 2 ≤ N); lia
    have hm1 : (1 : ℝ) < m := mod_cast (by lia : 1 < m)
    have hlogm_pos : 0 < Real.log m := Real.log_pos hm1
    have hsub : (Nat.primesLE N).filter (N.sqrt < ·) ⊆
        (Nat.primesLE ⌊(N : ℝ)⌋₊).filter (fun p : ℕ ↦ (m : ℝ) ≤ (p : ℝ)) := fun p hp ↦ by
      obtain ⟨hpN, hgt⟩ := mem_filter.mp hp
      rw [Nat.floor_natCast]
      exact mem_filter.mpr ⟨hpN, mod_cast hgt⟩
    refine (sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ ↦ by positivity).trans
      ((Chebyshev.sum_primesLE_filter_ge_inv_le (mod_cast (by lia : 1 ≤ N)) hm1).trans ?_)
    have hlog3 : (2 : ℝ) / 3 ≤ Real.log m := by
      have hm3' : (3 : ℝ) ≤ m := mod_cast hm3
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1 / 3)
      rw [one_div, Real.log_inv] at h
      linarith [Real.log_le_log (by norm_num) hm3']
    have hlogN : Real.log N ≤ 2 * Real.log m := by
      have hsq : (N : ℝ) < (m : ℝ) ^ 2 := by
        simpa [m, sq] using (Nat.cast_lt (α := ℝ)).mpr (Nat.lt_succ_sqrt N)
      have := Real.log_lt_log (by positivity) hsq
      rw [Real.log_pow] at this; push_cast at this; linarith
    rw [div_le_iff₀ hlogm_pos]
    linarith [Real.log_four_le_two]

/-- Reciprocal sum over large prime powers `√N < p ^ k ≤ N` is at most `12`. -/
private lemma sum_large_prime_powers_inv_le (N : ℕ) :
    ∑ x ∈ largePrimePowers N, ((x.1 : ℝ) ^ x.2)⁻¹ ≤ 12 := by
  rw [← sum_filter_add_sum_filter_not (largePrimePowers N) (fun x ↦ x.2 = 1)]
  have h1 := sum_large_prime_powers_exp_one_inv_le N
  have h2 : ∑ x ∈ (largePrimePowers N).filter (fun x ↦ ¬ x.2 = 1), ((x.1 : ℝ) ^ x.2)⁻¹ ≤ 1 := by
    have hsub : (largePrimePowers N).filter (fun x ↦ ¬ x.2 = 1) ⊆
        (Nat.primesLE N).sigma fun p ↦ Icc 2 (p.log N) := fun x hx ↦ by
      obtain ⟨hxL, hne1⟩ := mem_filter.mp hx
      obtain ⟨hp, hk⟩ := mem_sigma.mp (mem_filter.mp (largePrimePowers_eq N ▸ hxL)).1
      rw [mem_Icc] at hk
      exact mem_sigma.mpr ⟨hp, mem_Icc.mpr ⟨by lia, hk.2⟩⟩
    refine (sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ ↦ by positivity).trans ?_
    rw [sum_sigma]
    exact Nat.sum_primesLE_sum_Icc_two_inv_pow_le_one N (·.log N)
  exact (add_le_add h1 h2).trans (by norm_num)

/-- Sum of squares of the large-prime-power part `f_L` on `Icc 1 N`. -/
private lemma sum_large_prime_powers_sq_le (N : ℕ) (f : ArithmeticFunction ℝ) :
    ∑ n ∈ Icc 1 N, largePart N f n ^ 2 ≤ (N : ℝ) * largeVar N f := by
  have hpt : ∀ n ∈ Icc 1 N, largePart N f n ^ 2 =
      ∑ x ∈ largePrimePowers N, if n.factorization x.1 = x.2 then f (x.1 ^ x.2) ^ 2 else 0 :=
    fun n hn ↦ by
      rw [largePart_apply]
      exact (largePrimePowers N).sum_ite_pow_of_subsingleton (fun x ↦ n.factorization x.1 = x.2)
        (fun x ↦ f (x.1 ^ x.2)) two_ne_zero (large_prime_powers_subsingleton hn)
  rw [sum_congr rfl hpt, sum_comm, largeVar_eq, mul_sum]
  refine sum_le_sum fun x _ ↦ ?_
  calc (∑ n ∈ Icc 1 N, if n.factorization x.1 = x.2 then f (x.1 ^ x.2) ^ 2 else 0)
      = f (x.1 ^ x.2) ^ 2 *
          ∑ n ∈ Icc 1 N, (if n.factorization x.1 = x.2 then (1 : ℝ) else 0) := by
        simp only [mul_sum, mul_boole]
    _ ≤ f (x.1 ^ x.2) ^ 2 * ((N : ℝ) / (x.1 : ℝ) ^ x.2) :=
        mul_le_mul_of_nonneg_left (Nat.sum_Icc_ite_factorization_le N x.1 x.2) (sq_nonneg _)
    _ = (N : ℝ) * (f (x.1 ^ x.2) ^ 2 / (x.1 : ℝ) ^ x.2) := by ring

/-- First-moment discrepancy of the large-prime-power part `f_L` on `Icc 1 N`. -/
private lemma abs_sum_large_prime_powers_sub_le (N : ℕ) (f : ArithmeticFunction ℝ) :
    |(∑ n ∈ Icc 1 N, largePart N f n) - (N : ℝ) * largeMean N f| ≤
      (N : ℝ) * ∑ x ∈ largePrimePowers N, |f (x.1 ^ x.2)| / (x.1 : ℝ) ^ x.2 := by
  have hS1_eq : (∑ n ∈ Icc 1 N, largePart N f n) - (N : ℝ) * largeMean N f =
      ∑ x ∈ largePrimePowers N, f (x.1 ^ x.2) *
        ((∑ n ∈ Icc 1 N, (if n.factorization x.1 = x.2 then (1 : ℝ) else 0)) -
          (N : ℝ) / (x.1 : ℝ) ^ x.2) := by
    simp only [largePart_apply, largeMean_eq, mul_sum]
    rw [sum_comm, ← sum_sub_distrib]
    refine sum_congr rfl fun x _ ↦ ?_
    rw [mul_sub, mul_sum]
    simp only [mul_boole]
    ring
  rw [hS1_eq, mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun x _ ↦ ?_)
  have hC0 : 0 ≤ ∑ n ∈ Icc 1 N, (if n.factorization x.1 = x.2 then (1 : ℝ) else 0) :=
    sum_nonneg fun _ _ ↦ by split_ifs <;> norm_num
  have hCle := Nat.sum_Icc_ite_factorization_le (α := ℝ) N x.1 x.2
  have hD0 : 0 ≤ (N : ℝ) / (x.1 : ℝ) ^ x.2 := by positivity
  have habs : |(∑ n ∈ Icc 1 N, (if n.factorization x.1 = x.2 then (1 : ℝ) else 0)) -
      (N : ℝ) / (x.1 : ℝ) ^ x.2| ≤ (N : ℝ) / (x.1 : ℝ) ^ x.2 := by
    generalize (N : ℝ) / (x.1 : ℝ) ^ x.2 = D at hCle hD0 ⊢
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  rw [abs_mul]
  exact (mul_le_mul_of_nonneg_left habs (abs_nonneg _)).trans_eq (by ring)

/-- Large prime powers `M < p ^ k ≤ N` (`M = Nat.sqrt N`) satisfy
`∑_{n ≤ N} (f_L(n) - A_L) ^ 2 ≤ 13 * N * B_L`. -/
private lemma sum_large_prime_powers_sub_sq_le (N : ℕ) (f : ArithmeticFunction ℝ) :
    ∑ n ∈ Icc 1 N, (largePart N f n - largeMean N f) ^ 2 ≤ 13 * (N : ℝ) * largeVar N f := by
  rcases eq_or_ne N 0 with rfl | hN0
  · simp [largeVar_eq]
  have hN_pos : (0 : ℝ) < N := mod_cast Nat.pos_of_ne_zero hN0
  have hB_nonneg : 0 ≤ largeVar N f := by
    rw [largeVar_eq]
    exact sum_nonneg fun _ _ ↦ div_nonneg (sq_nonneg _) (by positivity)
  have hcs : (∑ x ∈ largePrimePowers N, |f (x.1 ^ x.2)| / (x.1 : ℝ) ^ x.2) ^ 2 ≤
      12 * largeVar N f := by
    calc (∑ x ∈ largePrimePowers N, |f (x.1 ^ x.2)| / (x.1 : ℝ) ^ x.2) ^ 2
        ≤ largeVar N f * ∑ x ∈ largePrimePowers N, ((x.1 : ℝ) ^ x.2)⁻¹ := by
          rw [largeVar_eq]
          refine sum_sq_le_sum_mul_sum_of_sq_le_mul (largePrimePowers N) (fun _ _ ↦ by positivity)
            (fun _ _ ↦ by positivity) fun x hx ↦ ?_
          have hp0 : (x.1 : ℝ) ≠ 0 := mod_cast (prime_of_mem_largePrimePowers hx).ne_zero
          rw [div_pow, sq_abs]; field_simp; exact le_rfl
      _ ≤ largeVar N f * 12 :=
          mul_le_mul_of_nonneg_left (sum_large_prime_powers_inv_le N) hB_nonneg
      _ = 12 * largeVar N f := mul_comm _ _
  have hvar : ∑ n ∈ Icc 1 N, (largePart N f n - largeMean N f) ^ 2 ≤
      (∑ n ∈ Icc 1 N, largePart N f n ^ 2) +
        ((∑ n ∈ Icc 1 N, largePart N f n) - (N : ℝ) * largeMean N f) ^ 2 / (N : ℝ) := by
    simpa using (Icc 1 N).sum_sub_sq_le_sum_sq_add_div (largePart N f) (largeMean N f)
  have hmean : ((∑ n ∈ Icc 1 N, largePart N f n) - (N : ℝ) * largeMean N f) ^ 2 / (N : ℝ) ≤
      12 * (N : ℝ) * largeVar N f := by
    rw [div_le_iff₀ hN_pos]
    calc ((∑ n ∈ Icc 1 N, largePart N f n) - (N : ℝ) * largeMean N f) ^ 2
        = |(∑ n ∈ Icc 1 N, largePart N f n) - (N : ℝ) * largeMean N f| ^ 2 := (sq_abs _).symm
      _ ≤ ((N : ℝ) * ∑ x ∈ largePrimePowers N, |f (x.1 ^ x.2)| / (x.1 : ℝ) ^ x.2) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) (abs_sum_large_prime_powers_sub_le N f) 2
      _ = (N : ℝ) ^ 2 * (∑ x ∈ largePrimePowers N, |f (x.1 ^ x.2)| / (x.1 : ℝ) ^ x.2) ^ 2 :=
          mul_pow _ _ 2
      _ ≤ (N : ℝ) ^ 2 * (12 * largeVar N f) := mul_le_mul_of_nonneg_left hcs (sq_nonneg _)
      _ = 12 * (N : ℝ) * largeVar N f * (N : ℝ) := by ring
  exact hvar.trans ((add_le_add (sum_large_prime_powers_sq_le N f) hmean).trans_eq (by ring))

end SplitBounds

/-! ### The Turán–Kubilius inequality -/

namespace IsAdditive

/-- **The Turán–Kubilius inequality** (`Icc 1 (p.log N)` form). For any real-valued additive
arithmetic function `f` and any `N : ℕ`,
`∑ n ∈ Icc 1 N, (f n - A) ^ 2 ≤ 30 * N * B`, where
`A = ∑_{p ≤ N} ∑_{1 ≤ k ≤ log_p N} f(p ^ k) / p ^ k` and
`B = ∑_{p ≤ N} ∑_{1 ≤ k ≤ log_p N} f(p ^ k) ^ 2 / p ^ k`. -/
theorem sum_Icc_sub_sum_primesLE_Icc_log_sq_le {f : ArithmeticFunction ℝ} (hf : f.IsAdditive)
    (N : ℕ) :
    let A := ∑ p ∈ Nat.primesLE N, ∑ k ∈ Icc 1 (p.log N), f (p ^ k) / (p : ℝ) ^ k
    let B := ∑ p ∈ Nat.primesLE N, ∑ k ∈ Icc 1 (p.log N), f (p ^ k) ^ 2 / (p : ℝ) ^ k
    ∑ n ∈ Icc 1 N, (f n - A) ^ 2 ≤ 30 * (N : ℝ) * B := by
  intro A B
  set I := (Nat.primesLE N).sigma fun p ↦ Icc 1 (p.log N)
  have hnot_gt : I.filter (fun x ↦ ¬ N.sqrt < x.1 ^ x.2) =
      (Nat.primesLE N.sqrt).sigma fun p ↦ Icc 1 (p.log N.sqrt) := by
    simp_rw [not_lt]
    exact Nat.primesLE_sigma_Icc_log_filter_le (Nat.sqrt_le_self N)
  have hsplit : ∀ g : (Σ _ : ℕ, ℕ) → ℝ,
      (∑ p ∈ Nat.primesLE N, ∑ k ∈ Icc 1 (p.log N), g ⟨p, k⟩) =
        (∑ p ∈ Nat.primesLE N.sqrt, ∑ k ∈ Icc 1 (p.log N.sqrt), g ⟨p, k⟩) +
          ∑ x ∈ largePrimePowers N, g x := by
    intro g
    rw [← sum_sigma, ← sum_filter_add_sum_filter_not I (fun x ↦ N.sqrt < x.1 ^ x.2),
      hnot_gt, sum_sigma, ← largePrimePowers_eq, add_comm]
  have hf_eq : ∀ n ∈ Icc 1 N, f n = smallPart N.sqrt f n + largePart N f n := fun n hn ↦ by
    rw [smallPart_apply, largePart_apply]
    exact (hf.apply_eq_sum_primesLE_Icc_log (mem_Icc.mp hn).2).trans
      (hsplit fun x ↦ if n.factorization x.1 = x.2 then f (x.1 ^ x.2) else 0)
  have hA_eq : A = smallMean N.sqrt f + largeMean N f := by
    rw [smallMean_eq, largeMean_eq]
    exact hsplit fun x ↦ f (x.1 ^ x.2) / (x.1 : ℝ) ^ x.2
  have hB_eq : B = smallVar N.sqrt f + largeVar N f := by
    rw [smallVar_eq, largeVar_eq]
    exact hsplit fun x ↦ f (x.1 ^ x.2) ^ 2 / (x.1 : ℝ) ^ x.2
  have hBS_nonneg : 0 ≤ smallVar N.sqrt f := by
    rw [smallVar_eq]
    exact sum_nonneg fun _ _ ↦ sum_nonneg fun _ _ ↦ div_nonneg (sq_nonneg _) (by positivity)
  have hBL_nonneg : 0 ≤ largeVar N f := by
    rw [largeVar_eq]
    exact sum_nonneg fun _ _ ↦ div_nonneg (sq_nonneg _) (by positivity)
  have hsmall := sum_small_prime_powers_sub_sq_le N f
  have hlarge := sum_large_prime_powers_sub_sq_le N f
  -- Combine `2 * 10 * N * BS + 2 * 13 * N * BL ≤ 30 * N * (BS + BL) = 30 * N * B`.
  calc ∑ n ∈ Icc 1 N, (f n - A) ^ 2
      ≤ ∑ n ∈ Icc 1 N,
          (2 * (smallPart N.sqrt f n - smallMean N.sqrt f) ^ 2 +
            2 * (largePart N f n - largeMean N f) ^ 2) := by
        refine sum_le_sum fun n hn ↦ ?_
        rw [hf_eq n hn, hA_eq]
        nlinarith [sq_nonneg ((smallPart N.sqrt f n - smallMean N.sqrt f) -
          (largePart N f n - largeMean N f))]
    _ = 2 * (∑ n ∈ Icc 1 N, (smallPart N.sqrt f n - smallMean N.sqrt f) ^ 2) +
          2 * (∑ n ∈ Icc 1 N, (largePart N f n - largeMean N f) ^ 2) := by
        rw [sum_add_distrib, ← mul_sum, ← mul_sum]
    _ ≤ 2 * (10 * (N : ℝ) * smallVar N.sqrt f) + 2 * (13 * (N : ℝ) * largeVar N f) := by
        gcongr
    _ = 20 * (N : ℝ) * smallVar N.sqrt f + 26 * (N : ℝ) * largeVar N f := by ring
    _ ≤ 30 * (N : ℝ) * (smallVar N.sqrt f + largeVar N f) := by
        have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
        have h1 : 20 * (N : ℝ) * smallVar N.sqrt f ≤ 30 * (N : ℝ) * smallVar N.sqrt f :=
          mul_le_mul_of_nonneg_right (by linarith) hBS_nonneg
        have h2 : 26 * (N : ℝ) * largeVar N f ≤ 30 * (N : ℝ) * largeVar N f :=
          mul_le_mul_of_nonneg_right (by linarith) hBL_nonneg
        linarith
    _ = 30 * (N : ℝ) * B := by rw [hB_eq]

/-- **The Turán–Kubilius inequality.** For any real-valued additive arithmetic function `f` and
any `N : ℕ`, `∑ n ∈ Icc 1 N, (f n - A) ^ 2 ≤ 30 * N * B`, where `A` and `B` sum `f (p ^ k) / p ^ k`
and `f (p ^ k) ^ 2 / p ^ k` over primes `p ≤ N` and exponents `1 ≤ k ≤ N` with `p ^ k ≤ N`. -/
theorem sum_Icc_sub_sq_le {f : ArithmeticFunction ℝ} (hf : f.IsAdditive) (N : ℕ) :
    let A := ∑ p ∈ Nat.primesLE N, ∑ k ∈ Icc 1 N,
      if p ^ k ≤ N then f (p ^ k) / (p ^ k : ℕ) else 0
    let B := ∑ p ∈ Nat.primesLE N, ∑ k ∈ Icc 1 N,
      if p ^ k ≤ N then f (p ^ k) ^ 2 / (p ^ k : ℕ) else 0
    ∑ n ∈ Icc 1 N, (f n - A) ^ 2 ≤ 30 * (N : ℝ) * B := by
  intro A B
  have hA : A = ∑ p ∈ Nat.primesLE N, ∑ k ∈ Icc 1 (p.log N), f (p ^ k) / (p : ℝ) ^ k := by
    refine sum_congr rfl fun p hp ↦ ?_
    simpa [Nat.cast_pow] using Nat.sum_Icc_ite_pow_le_eq_sum_Icc_log
      (Nat.prime_of_mem_primesLE hp).one_lt N (fun k ↦ f (p ^ k) / (p ^ k : ℕ))
  have hB : B = ∑ p ∈ Nat.primesLE N, ∑ k ∈ Icc 1 (p.log N), f (p ^ k) ^ 2 / (p : ℝ) ^ k := by
    refine sum_congr rfl fun p hp ↦ ?_
    simpa [Nat.cast_pow] using Nat.sum_Icc_ite_pow_le_eq_sum_Icc_log
      (Nat.prime_of_mem_primesLE hp).one_lt N (fun k ↦ f (p ^ k) ^ 2 / (p ^ k : ℕ))
  rw [hA, hB]
  exact hf.sum_Icc_sub_sum_primesLE_Icc_log_sq_le N

end IsAdditive

namespace IsStronglyAdditive

/-- For a strongly additive function, the full prime-power variance proxy
`∑_{p ≤ N} ∑_{1 ≤ k ≤ log_p N} f(p ^ k) ^ 2 / p ^ k` is at most twice `∑_{p ≤ N} f(p) ^ 2 / p`. -/
theorem sum_primesLE_Icc_log_sq_le {f : ArithmeticFunction ℝ} (hf : f.IsStronglyAdditive)
    (N : ℕ) :
    (∑ p ∈ Nat.primesLE N, ∑ k ∈ Icc 1 (p.log N), f (p ^ k) ^ 2 / (p : ℝ) ^ k) ≤
       2 * ∑ p ∈ Nat.primesLE N, f p ^ 2 / (p : ℝ) := by
  rw [mul_sum]
  refine sum_le_sum fun p hp ↦ ?_
  have hp' := Nat.prime_of_mem_primesLE hp
  have hp2 : (2 : ℝ) ≤ p := mod_cast hp'.two_le
  have hrew : ∑ k ∈ Icc 1 (p.log N), f (p ^ k) ^ 2 / (p : ℝ) ^ k =
      f p ^ 2 * ∑ k ∈ Icc 1 (p.log N), ((p : ℝ) ^ k)⁻¹ := by
    rw [mul_sum]
    refine sum_congr rfl fun k hk ↦ ?_
    rw [hf.map_prime_pow hp' (by have := (mem_Icc.mp hk).1; lia), div_eq_mul_inv]
  rw [hrew]
  have hinv : ∑ k ∈ Icc 1 (p.log N), ((p : ℝ) ^ k)⁻¹ ≤ 2 / (p : ℝ) := by
    have h1 : 1 ≤ p.log N := Nat.log_pos hp'.one_lt (Nat.le_of_mem_primesLE hp)
    rw [← insert_Icc_add_one_left_eq_Icc h1, sum_insert (by simp), pow_one, ← one_div]
    have htail := TauCeti.sum_Icc_inv_pow_le hp'.ne_one (p.log N)
    have hp_pos : (0 : ℝ) < p := by linarith
    have hle : 1 / ((p : ℝ) * ((p : ℝ) - 1)) ≤ 1 / (p : ℝ) :=
      one_div_le_one_div_of_le hp_pos (by nlinarith)
    have htwo : (2 : ℝ) / (p : ℝ) = 1 / (p : ℝ) + 1 / (p : ℝ) := by ring
    linarith
  calc f p ^ 2 * ∑ k ∈ Icc 1 (p.log N), ((p : ℝ) ^ k)⁻¹
      ≤ f p ^ 2 * (2 / (p : ℝ)) := mul_le_mul_of_nonneg_left hinv (sq_nonneg _)
    _ = 2 * (f p ^ 2 / (p : ℝ)) := by ring

/-- For a strongly additive function, subtracting the prime sum `∑_{p ≤ N} f(p) / p` from the full
prime-power sum leaves the higher-power tail `∑_{p ≤ N} f(p) * ∑_{2 ≤ k ≤ log_p N} (p ^ k)⁻¹`. -/
theorem sum_primesLE_Icc_log_sub_sum_primesLE {f : ArithmeticFunction ℝ}
    (hf : f.IsStronglyAdditive) (N : ℕ) :
    (∑ p ∈ Nat.primesLE N, ∑ k ∈ Icc 1 (p.log N), f (p ^ k) / (p : ℝ) ^ k) -
        (∑ p ∈ Nat.primesLE N, f p / (p : ℝ)) =
      ∑ p ∈ Nat.primesLE N, f p * ∑ k ∈ Icc 2 (p.log N), ((p : ℝ) ^ k)⁻¹ := by
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun p hp ↦ ?_
  have hp' := Nat.prime_of_mem_primesLE hp
  have h1 : 1 ≤ p.log N := Nat.log_pos hp'.one_lt (Nat.le_of_mem_primesLE hp)
  rw [← insert_Icc_add_one_left_eq_Icc h1, sum_insert (by simp)]
  simp only [Nat.reduceAdd, pow_one]
  have h2 : (∑ k ∈ Icc 2 (p.log N), f (p ^ k) / (p : ℝ) ^ k) =
      f p * ∑ k ∈ Icc 2 (p.log N), ((p : ℝ) ^ k)⁻¹ := by
    rw [mul_sum]
    refine sum_congr rfl fun k hk ↦ ?_
    rw [hf.map_prime_pow hp' (by have := (mem_Icc.mp hk).1; lia), div_eq_mul_inv]
  rw [h2]; ring

/-- For a strongly additive function, the squared higher-power expectation tail `(A_full - A) ^ 2`
is bounded by `∑_{p ≤ N} f(p) ^ 2 / p`. -/
theorem sum_primesLE_Icc_log_sub_sum_primesLE_sq_le {f : ArithmeticFunction ℝ}
    (hf : f.IsStronglyAdditive) (N : ℕ) :
    ((∑ p ∈ Nat.primesLE N, ∑ k ∈ Icc 1 (p.log N), f (p ^ k) / (p : ℝ) ^ k) -
        ∑ p ∈ Nat.primesLE N, f p / (p : ℝ)) ^ 2 ≤
      ∑ p ∈ Nat.primesLE N, f p ^ 2 / (p : ℝ) := by
  set B := ∑ p ∈ Nat.primesLE N, f p ^ 2 / (p : ℝ)
  have hB_nonneg : 0 ≤ B := sum_nonneg fun _ _ ↦ div_nonneg (sq_nonneg _) (by positivity)
  have habs : |(∑ p ∈ Nat.primesLE N, ∑ k ∈ Icc 1 (p.log N), f (p ^ k) / (p : ℝ) ^ k) -
      ∑ p ∈ Nat.primesLE N, f p / (p : ℝ)| ≤
      ∑ p ∈ Nat.primesLE N, |f p| / ((p : ℝ) * ((p : ℝ) - 1)) := by
    rw [hf.sum_primesLE_Icc_log_sub_sum_primesLE N]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun p hp ↦ ?_)
    have hp' := Nat.prime_of_mem_primesLE hp
    have h0 : 0 ≤ ∑ k ∈ Icc 2 (p.log N), ((p : ℝ) ^ k)⁻¹ := sum_nonneg fun _ _ ↦ by positivity
    rw [abs_mul, abs_of_nonneg h0, div_eq_mul_inv, ← one_div]
    exact mul_le_mul_of_nonneg_left (TauCeti.sum_Icc_inv_pow_le hp'.ne_one _) (abs_nonneg _)
  have hcs : (∑ p ∈ Nat.primesLE N, |f p| / ((p : ℝ) * ((p : ℝ) - 1))) ^ 2 ≤
      B * ∑ p ∈ Nat.primesLE N, 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
    refine sum_sq_le_sum_mul_sum_of_sq_le_mul (Nat.primesLE N)
      (fun _ _ ↦ div_nonneg (sq_nonneg _) (by positivity))
      (fun p hp ↦ by
        have hp2 : (2 : ℝ) ≤ p := mod_cast (Nat.prime_of_mem_primesLE hp).two_le
        exact div_nonneg zero_le_one (mul_nonneg (by linarith) (by linarith)))
      fun p hp ↦ ?_
    have hp2 : (2 : ℝ) ≤ p := mod_cast (Nat.prime_of_mem_primesLE hp).two_le
    have hp0 : (0 : ℝ) < p := by linarith
    rw [div_pow, sq_abs]
    calc f p ^ 2 / ((p : ℝ) * ((p : ℝ) - 1)) ^ 2
        = f p ^ 2 / (p : ℝ) * (1 / ((p : ℝ) * ((p : ℝ) - 1) ^ 2)) := by field_simp
      _ ≤ f p ^ 2 / (p : ℝ) * (1 / ((p : ℝ) * ((p : ℝ) - 1))) := by
          refine mul_le_mul_of_nonneg_left ?_ (div_nonneg (sq_nonneg _) hp0.le)
          exact one_div_le_one_div_of_le (mul_pos hp0 (by linarith)) (by nlinarith)
  calc ((∑ p ∈ Nat.primesLE N, ∑ k ∈ Icc 1 (p.log N), f (p ^ k) / (p : ℝ) ^ k) -
        ∑ p ∈ Nat.primesLE N, f p / (p : ℝ)) ^ 2
      = |(∑ p ∈ Nat.primesLE N, ∑ k ∈ Icc 1 (p.log N), f (p ^ k) / (p : ℝ) ^ k) -
          ∑ p ∈ Nat.primesLE N, f p / (p : ℝ)| ^ 2 := (sq_abs _).symm
    _ ≤ (∑ p ∈ Nat.primesLE N, |f p| / ((p : ℝ) * ((p : ℝ) - 1))) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) habs 2
    _ ≤ B * ∑ p ∈ Nat.primesLE N, 1 / ((p : ℝ) * ((p : ℝ) - 1)) := hcs
    _ ≤ B * 1 := mul_le_mul_of_nonneg_left (Nat.sum_primesLE_one_div_mul_sub_one_le_one N)
        hB_nonneg
    _ = B := mul_one B

/-- **Distinct-prime Turán–Kubilius inequality for strongly additive functions.** For any
real-valued strongly additive function `f` and any `N : ℕ`, replacing the full prime-power sums by
the prime sums `A = ∑_{p ≤ N} f(p) / p` and `B = ∑_{p ≤ N} f(p) ^ 2 / p` yields
`∑ n ∈ Icc 1 N, (f n - A) ^ 2 ≤ 77 * N * B`. -/
theorem sum_Icc_sub_sq_le {f : ArithmeticFunction ℝ} (hf : f.IsStronglyAdditive) (N : ℕ) :
    let A := ∑ p ∈ Nat.primesLE N, f p / (p : ℝ)
    let B := ∑ p ∈ Nat.primesLE N, f p ^ 2 / (p : ℝ)
    ∑ n ∈ Icc 1 N, (f n - A) ^ 2 ≤ 77 * (N : ℝ) * B := by
  intro A B
  set Afull := ∑ p ∈ Nat.primesLE N, ∑ k ∈ Icc 1 (p.log N), f (p ^ k) / (p : ℝ) ^ k
  have hfull := hf.toIsAdditive.sum_Icc_sub_sum_primesLE_Icc_log_sq_le N
  have hBfull := hf.sum_primesLE_Icc_log_sq_le N
  have hAdiff := hf.sum_primesLE_Icc_log_sub_sum_primesLE_sq_le N
  -- Combine `(7 / 6) * (30 * N * (2 * B)) + 7 * N * B = (70 + 7) * N * B = 77 * N * B`.
  calc ∑ n ∈ Icc 1 N, (f n - A) ^ 2
      ≤ ∑ n ∈ Icc 1 N, ((7 / 6 : ℝ) * (f n - Afull) ^ 2 + 7 * (Afull - A) ^ 2) :=
        sum_le_sum fun n _ ↦ by nlinarith [sq_nonneg ((f n - Afull) - 6 * (Afull - A))]
    _ = (7 / 6 : ℝ) * (∑ n ∈ Icc 1 N, (f n - Afull) ^ 2) + 7 * (N : ℝ) * (Afull - A) ^ 2 := by
        simp only [sum_add_distrib, ← mul_sum, sum_const, Nat.card_Icc, add_tsub_cancel_right,
          nsmul_eq_mul]
        ring
    _ ≤ (7 / 6 : ℝ) * (30 * (N : ℝ) * (2 * B)) + 7 * (N : ℝ) * B := by
        have h1 : ∑ n ∈ Icc 1 N, (f n - Afull) ^ 2 ≤ 30 * (N : ℝ) * (2 * B) :=
          hfull.trans (mul_le_mul_of_nonneg_left hBfull (by positivity))
        gcongr
    _ = 77 * (N : ℝ) * B := by ring

end IsStronglyAdditive

/-- **Turán's inequality (1934)** for the distinct-prime-factor counting function
`ω = cardDistinctFactors`: for every `N : ℕ`,
`∑ n ∈ Icc 1 N, (ω n - ∑_{p ≤ N} 1 / p) ^ 2 ≤ 77 * N * ∑_{p ≤ N} 1 / p`. -/
theorem sum_Icc_cardDistinctFactors_sub_sq_le (N : ℕ) :
    ∑ n ∈ Icc 1 N,
        ((cardDistinctFactors n : ℝ) - ∑ p ∈ Nat.primesLE N, (p : ℝ)⁻¹) ^ 2 ≤
      77 * (N : ℝ) * ∑ p ∈ Nat.primesLE N, (p : ℝ)⁻¹ := by
  have h := (isStronglyAdditive_cardDistinctFactors.natCast (R := ℝ)).sum_Icc_sub_sq_le N
  simp only [natCoe_apply] at h
  have h1 : (∑ p ∈ Nat.primesLE N, (cardDistinctFactors p : ℝ) / (p : ℝ)) =
      ∑ p ∈ Nat.primesLE N, (p : ℝ)⁻¹ :=
    sum_congr rfl fun p hp ↦ by
      simp [cardDistinctFactors_apply_prime (Nat.prime_of_mem_primesLE hp), one_div]
  have h2 : (∑ p ∈ Nat.primesLE N, (cardDistinctFactors p : ℝ) ^ 2 / (p : ℝ)) =
      ∑ p ∈ Nat.primesLE N, (p : ℝ)⁻¹ :=
    sum_congr rfl fun p hp ↦ by
      simp [cardDistinctFactors_apply_prime (Nat.prime_of_mem_primesLE hp), one_div]
  simpa only [h1, h2] using h

end ArithmeticFunction
