/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.DedekindEta.Kronecker
public import TauCeti.NumberTheory.ModularForms.DedekindEta.Quotient

/-!
# Kronecker-symbol evaluation of the eta-quotient multiplier

Combines `TauCeti.ModularForm.etaQuotientMultiplier_eq_prod` with the odd-`d` Kronecker form
`TauCeti.ModularForm.etaMultiplier_eq_kroneckerSym_mul_of_odd_d` to evaluate
`etaQuotientMultiplier N r ⟨γ, hγ⟩` whenever `γ ∈ Γ₀(N)` has odd lower-right entry `γ 1 1`.

## Main results

* `TauCeti.ModularForm.etaQuotientMultiplier_eq_prod_kroneckerSym_mul_e24_of_odd_d`: factors
  `etaQuotientMultiplier N r ⟨γ, hγ⟩` into `∏ δ ∈ N.divisors, (kroneckerSym ((N / δ) * t) d) ^ r δ`
  times a single `e24` root of unity grouped along `∑ (N / δ) * r δ`, `∑ δ * r δ`, and `∑ r δ`.
-/

public section

open Complex CongruenceSubgroup ModularGroup TauCeti.ModularForm
open scoped MatrixGroups

namespace TauCeti.ModularForm

/-- Regrouping the even-`c` eta-multiplier exponent sum over `δ ∈ N.divisors` when `c = N * t`
into multiples of `∑ δ ∈ N.divisors, (N / δ) * r δ`, `∑ δ ∈ N.divisors, δ * r δ`, and
`∑ δ ∈ N.divisors, r δ`. -/
private theorem sum_mul_etaMultiplierExpEvenC (N : ℕ) (r : ℕ → ℤ) (a b d t : ℤ) :
    ∑ δ ∈ N.divisors, r δ * etaMultiplierExpEvenC a (b * δ) ((N / δ : ℕ) * t) d =
      (∑ δ ∈ N.divisors, ((N / δ : ℕ) : ℤ) * r δ) *
        ((a + d) * t - b * d * N * t ^ 2 - 3 * t * d) +
        (∑ δ ∈ N.divisors, (δ : ℤ) * r δ) * (b * d) +
        (∑ δ ∈ N.divisors, r δ) * (3 * d - 3) := by
  rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun δ hδ ↦ ?_
  have hmul : (δ : ℤ) * (N / δ : ℕ) = N := by
    exact_mod_cast Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hδ)
  rw [etaMultiplierExpEvenC_def]
  linear_combination (-(r δ * b * d * (N / δ : ℕ) * t ^ 2)) * hmul

/-- Evaluating the eta-quotient multiplier when `γ 1 0 = N * t` and `γ 1 1` is odd: each factor
`ε(γ_δ)` is given by the odd-`d` Kronecker form, factoring the multiplier into the product of
`(kroneckerSym ((N / δ : ℕ) * t) (γ 1 1)) ^ r δ` and `e24` of the regrouped exponent sum. -/
theorem etaQuotientMultiplier_eq_prod_kroneckerSym_mul_e24_of_odd_d {N : ℕ}
    (r : ℕ → ℤ) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N) {t : ℤ} (ht : γ 1 0 = N * t)
    (hdo : Odd (γ 1 1)) :
    etaQuotientMultiplier N r ⟨γ, hγ⟩ =
      (∏ δ ∈ N.divisors, (kroneckerSym ((N / δ : ℕ) * t) (γ 1 1) : ℂ) ^ r δ) *
        e24 ((∑ δ ∈ N.divisors, ((N / δ : ℕ) : ℤ) * r δ) *
            ((γ 0 0 + γ 1 1) * t - γ 0 1 * γ 1 1 * N * t ^ 2 - 3 * t * γ 1 1) +
          (∑ δ ∈ N.divisors, (δ : ℤ) * r δ) * (γ 0 1 * γ 1 1) +
          (∑ δ ∈ N.divisors, r δ) * (3 * γ 1 1 - 3)) := by
  have hε (δ : ℕ) (hδ : δ ∈ N.divisors) :
      etaMultiplier (conjScaleGamma0 (Nat.dvd_of_mem_divisors hδ) ⟨γ, hγ⟩) =
        (kroneckerSym ((N / δ : ℕ) * t) (γ 1 1) : ℂ) *
          e24 (etaMultiplierExpEvenC (γ 0 0) (γ 0 1 * δ) ((N / δ : ℕ) * t) (γ 1 1)) := by
    have h10 := conjScaleGamma0_apply_one_zero_of_eq (Nat.dvd_of_mem_divisors hδ) hγ ht
    rw [etaMultiplier_eq_kroneckerSym_mul_of_odd_d _ (by simpa using hdo), h10]
    simp [mul_comm (δ : ℤ)]
  rw [etaQuotientMultiplier_eq_prod r hγ hε, prod_mul_e24_zpow, sum_mul_etaMultiplierExpEvenC]

end TauCeti.ModularForm
