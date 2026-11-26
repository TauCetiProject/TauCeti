/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DirichletCharacter.LFunction.SplitPrimeSum
public import TauCeti.NumberTheory.LFunctions.Zeros.Completion.Dirichlet.Hadamard
import TauCeti.NumberTheory.Chebyshev.Mertens
import TauCeti.NumberTheory.DirichletCharacter.LFunction.DerivBound
import TauCeti.NumberTheory.PrimeFactors.Bounds

/-!
# A real zero of a Dirichlet `L`-function forces a prime bias

Let `χ` be a primitive nonprincipal Dirichlet character of conductor `N`, and let `β > 0` be a
real zero of `L(s, χ)`, so that `β < 1`. Landau's deduction shows that if `β` is close to `1`,
then the primes `p` with `χ(p) = 1` carry little of the weight `∑_{p ≤ X} log p / p`:
there is one absolute constant `A` with

`∑_{p ≤ X, χ(p) = 1} log p / p ≤ A (log N + (1 - β) (log X) ^ 2)`

for every such `χ`, every such zero and every `X ≥ e`.

Two inequalities at `σ = 1 + 1 / log X` combine to give it. On the prime side,
`DirichletCharacter.exists_sum_primesLE_filter_eq_one_log_div_le` bounds the sum by
`(e / 2) (log X + C - re L′/L(σ, χ))`. On the zero side, the Hadamard product of the completed
`L`-function keeps the zero `β` and drops the other, nonnegative, zero terms
(`DirichletCharacter.one_div_sub_le_re_logDeriv_LFunction_add`):
`1 / (σ - β) ≤ re L′/L(σ, χ) + (log N) / 2 + C_Γ`. Adding them, the logarithmic derivative
cancels and `log X - 1 / (σ - β) = (1 - β) (log X) ^ 2 / (1 + (1 - β) log X)` is at most
`(1 - β) (log X) ^ 2`. Since `N ≥ 3`, `log N ≥ 1` absorbs the constants.

For a quadratic character `χ` every prime `p ∤ N` has `χ(p) = ±1`. Mertens's estimate
`∑_{p ≤ X} log p / p ≥ log X - (log 4 + 4)` and the bound `∑_{p ∣ N} log p / p ≤ (log N) / 2`
then show that the primes with `χ(p) = -1` carry all of the weight but

`A (log N + (1 - β) (log X) ^ 2)`.

At `X = N ^ C` this is `A (1 / C + C δ) log X` with `δ = (1 - β) log N`: a zero with small `δ`
leaves almost all of the weight `log X` to the primes with `χ(p) = -1`. Comparing this lower
bound with an upper bound `θ log X + O(1)`, `θ < 1`, for the same sum bounds `δ` from below, which
is how real zeros close to `1` are excluded.

## Main results

Both in namespace `DirichletCharacter`:

* `exists_sum_primesLE_filter_eq_one_log_div_le_of_LFunction_eq_zero`: the split primes carry at
  most `A (log N + (1 - β) (log X) ^ 2)`.
* `exists_log_sub_le_sum_primesLE_filter_eq_neg_one_log_div_of_LFunction_eq_zero`: for quadratic
  `χ`, the primes with `χ(p) = -1` carry at least
  `log X - A (log N + (1 - β) (log X) ^ 2)`.

## References

* OpenAI, *Uniform exclusion of Landau–Siegel zeros*, OpenAI mathematics release of
  1 October 2026, §2, Lemma 2 (prime bias forced by a real zero).
* H. Davenport, *Multiplicative Number Theory*, 3rd ed., Springer GTM 74 (2000), Chapter 14, for
  Landau's combination of `-ζ′/ζ` and `-L′/L` at a real point `σ > 1`.
-/

public section

open Finset

namespace DirichletCharacter

/-- **A real zero leaves few split primes.** There is an absolute constant `A > 0` such that for
every primitive nonprincipal Dirichlet character `χ` of conductor `N`, every real zero `β > 0` of
`L(s, χ)` and every `X ≥ e`,
`∑_{p ≤ X, χ(p) = 1} log p / p ≤ A (log N + (1 - β) (log X) ^ 2)`. -/
theorem exists_sum_primesLE_filter_eq_one_log_div_le_of_LFunction_eq_zero :
    ∃ A : ℝ, 0 < A ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → χ ≠ 1 →
      ∀ β : ℝ, 0 < β → χ.LFunction β = 0 → ∀ X : ℝ, Real.exp 1 ≤ X →
        ∑ p ∈ (Nat.primesLE ⌊X⌋₊).filter (fun p : ℕ ↦ χ (p : ZMod N) = 1), Real.log p / p ≤
          A * (Real.log N + (1 - β) * Real.log X ^ 2) := by
  obtain ⟨C, hC⟩ := exists_sum_primesLE_filter_eq_one_log_div_le
  set K := C + TauCeti.gammaLogDerivBound
  refine ⟨Real.exp 1 / 2 * (1 + |K|), by positivity, fun N _ χ hχ hne β hβ hzero X hX ↦ ?_⟩
  set L := Real.log X with hL_def
  have hL : 1 ≤ L := by simpa using Real.log_le_log (Real.exp_pos 1) hX
  have hL0 : 0 < L := one_pos.trans_le hL
  have hN := (one_lt_log_level_of_ne_one hne).le
  have hβ1 : β < 1 := by simpa using χ.re_lt_one_of_LFunction_eq_zero (.inr hne) hzero
  -- the zero side at Landau's point `σ = 1 + 1 / log X`
  have hσ : 1 + L⁻¹ ∈ Set.Icc (1 : ℝ) 2 :=
    ⟨le_add_of_nonneg_right (inv_nonneg.mpr hL0.le), by linarith [inv_le_one_of_one_le₀ hL]⟩
  have hρ := χ.one_div_sub_le_re_logDeriv_LFunction_add hχ hne hβ hzero hσ
  -- `log X - 1 / (σ - β) ≤ (1 - β) (log X) ^ 2`
  have hgap : L - 1 / (1 + L⁻¹ - β) ≤ (1 - β) * L ^ 2 := by
    have hpos : 0 < 1 + L⁻¹ - β := by linarith [inv_pos.mpr hL0]
    have hprod : (L - (1 - β) * L ^ 2) * (1 + L⁻¹ - β) = 1 - ((1 - β) * L) ^ 2 := by
      field_simp
      ring
    have : L - (1 - β) * L ^ 2 ≤ 1 / (1 + L⁻¹ - β) := by
      rw [le_div_iff₀ hpos, hprod]
      nlinarith
    linarith
  have hsplit := hC N χ X hX
  rw [← hL_def] at hsplit
  have hK : K ≤ |K| * Real.log N :=
    (le_abs_self K).trans (le_mul_of_one_le_right (abs_nonneg K) hN)
  have hu : 0 ≤ |K| * ((1 - β) * L ^ 2) := by
    have : 0 ≤ 1 - β := by linarith
    positivity
  calc _ ≤ Real.exp 1 / 2 * (L + C - (logDeriv (LFunction χ) ((1 + L⁻¹ : ℝ) : ℂ)).re) := hsplit
    _ ≤ Real.exp 1 / 2 * ((1 + |K|) * (Real.log N + (1 - β) * L ^ 2)) := by
        gcongr
        linarith
    _ = _ := by ring

/-- **A real zero leaves the Mertens weight to the inert primes.** There is an absolute constant
`A > 0` such that for every primitive nonprincipal quadratic Dirichlet character `χ` of conductor
`N`, every real zero `β > 0` of `L(s, χ)` and every `X ≥ e`, the primes with `χ(p) = -1` satisfy
`log X - A (log N + (1 - β) (log X) ^ 2) ≤ ∑_{p ≤ X, χ(p) = -1} log p / p`. -/
theorem exists_log_sub_le_sum_primesLE_filter_eq_neg_one_log_div_of_LFunction_eq_zero :
    ∃ A : ℝ, 0 < A ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → χ ≠ 1 →
      χ.IsQuadratic → ∀ β : ℝ, 0 < β → χ.LFunction β = 0 → ∀ X : ℝ, Real.exp 1 ≤ X →
        Real.log X - A * (Real.log N + (1 - β) * Real.log X ^ 2) ≤
          ∑ p ∈ (Nat.primesLE ⌊X⌋₊).filter (fun p : ℕ ↦ χ (p : ZMod N) = -1),
            Real.log p / p := by
  obtain ⟨A, hA, hsplit⟩ := exists_sum_primesLE_filter_eq_one_log_div_le_of_LFunction_eq_zero
  refine ⟨A + (Real.log 4 + 5), by positivity, fun N _ χ hχ hne hquad β hβ hzero X hX ↦ ?_⟩
  have hN := (one_lt_log_level_of_ne_one hne).le
  have hβ1 : β < 1 := by simpa using χ.re_lt_one_of_LFunction_eq_zero (.inr hne) hzero
  have hu : 0 ≤ (1 - β) * Real.log X ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  have h1 := hsplit N χ hχ hne β hβ hzero X hX
  set P := Nat.primesLE ⌊X⌋₊
  have hnonneg : ∀ p ∈ P, 0 ≤ Real.log p / p := fun p _ ↦ by positivity
  -- Mertens's estimate for the full prime weight
  have hmertens : Real.log X - (Real.log 4 + 4) ≤ ∑ p ∈ P, Real.log p / p := by
    have hX1 : 1 ≤ X := (Real.one_le_exp_iff.mpr zero_le_one).trans hX
    linarith [(abs_sub_le_iff.mp (Chebyshev.abs_sum_primesLE_log_div_sub_log_le hX1)).2]
  -- the primes with `χ(p) ≠ ±1` have `χ(p) = 0`, so they divide `N`
  have hram : (P.filter fun p : ℕ ↦ ¬χ (p : ZMod N) = 1).filter
      (fun p : ℕ ↦ ¬χ (p : ZMod N) = -1) ⊆ N.primeFactors := by
    intro p hp
    simp only [mem_filter] at hp
    obtain ⟨⟨hpP, hp1⟩, hp2⟩ := hp
    have hp : p.Prime := (Nat.mem_primesLE.mp hpP).2
    have h0 : χ (p : ZMod N) = 0 := by
      rcases hquad (p : ZMod N) with h | h | h
      exacts [h, absurd h hp1, absurd h hp2]
    have hdvd : p ∣ N := by
      by_contra hnd
      exact (IsUnit.map χ ((ZMod.isUnit_prime_iff_not_dvd hp).mpr hnd)).ne_zero h0
    exact Nat.mem_primeFactors.mpr ⟨hp, hdvd, NeZero.ne N⟩
  have hramsum : ∑ p ∈ (P.filter fun p : ℕ ↦ ¬χ (p : ZMod N) = 1).filter
      (fun p : ℕ ↦ ¬χ (p : ZMod N) = -1), Real.log p / p ≤ Real.log N / 2 :=
    (sum_le_sum_of_subset_of_nonneg hram fun p _ _ ↦ by positivity).trans
      (Nat.sum_primeFactors_log_div_le N)
  have hinert : ∑ p ∈ (P.filter fun p : ℕ ↦ ¬χ (p : ZMod N) = 1).filter
      (fun p : ℕ ↦ χ (p : ZMod N) = -1), Real.log p / p ≤
        ∑ p ∈ P.filter (fun p : ℕ ↦ χ (p : ZMod N) = -1), Real.log p / p :=
    sum_le_sum_of_subset_of_nonneg (filter_subset_filter _ (filter_subset _ _))
      fun p hp _ ↦ hnonneg p (mem_filter.mp hp).1
  have hall := sum_filter_add_sum_filter_not P (fun p : ℕ ↦ χ (p : ZMod N) = 1)
    (fun p ↦ Real.log p / p)
  have hrest := sum_filter_add_sum_filter_not (P.filter fun p : ℕ ↦ ¬χ (p : ZMod N) = 1)
    (fun p : ℕ ↦ χ (p : ZMod N) = -1) (fun p ↦ Real.log p / p)
  -- `(log 4 + 5) (log N + (1 - β) (log X) ^ 2)` absorbs `log 4 + 4` and `(log N) / 2`
  have habs : Real.log 4 + 4 + Real.log N / 2 ≤
      (Real.log 4 + 5) * (Real.log N + (1 - β) * Real.log X ^ 2) := by
    have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    nlinarith
  linarith

end DirichletCharacter
