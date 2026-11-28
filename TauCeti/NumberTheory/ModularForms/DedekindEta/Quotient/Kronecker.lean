/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.DedekindEta.Kronecker
public import TauCeti.NumberTheory.ModularForms.DedekindEta.Quotient.Basic
import TauCeti.Data.Nat.Cast.Basic

/-!
# Kronecker-symbol evaluation of the eta-quotient multiplier

Combines `TauCeti.ModularForm.etaQuotientMultiplier_eq_prod` with the odd-`d` Kronecker form
`TauCeti.ModularForm.etaMultiplier_eq_kroneckerSym_mul_of_odd_d` to evaluate
`etaQuotientMultiplier N r ⟨γ, hγ⟩` whenever `γ ∈ Γ₀(N)` has odd lower-right entry `γ 1 1`.

## Main definitions

* `TauCeti.ModularForm.etaQuotientMultiplierExp`: the regrouped `e24` exponent sum in the odd-`d`
  evaluation, along `∑ (N / δ) * r δ`, `∑ δ * r δ`, and `∑ r δ`.

## Main results

* `TauCeti.ModularForm.etaQuotientMultiplierExp_modEq`: when the two weighted divisor sums are
  divisible by `24`, `etaQuotientMultiplierExp` reduces modulo `24` to `(∑ r δ) * (3 * d - 3)`.
* `TauCeti.ModularForm.etaQuotientMultiplier_eq_prod_kroneckerSym_mul_e24_of_odd_d`: factors
  `etaQuotientMultiplier N r ⟨γ, hγ⟩` into `∏ δ ∈ N.divisors, (kroneckerSym ((N / δ) * t) d) ^ r δ`
  times `e24 (etaQuotientMultiplierExp N r a b d t)`.
-/

public section

open Complex CongruenceSubgroup ModularGroup TauCeti.ModularForm
open scoped MatrixGroups

namespace TauCeti.ModularForm

/-- The regrouped `e24` exponent in
`etaQuotientMultiplier_eq_prod_kroneckerSym_mul_e24_of_odd_d`, grouping the divisor sum along
`∑ (N / δ) * r δ`, `∑ δ * r δ`, and `∑ r δ`. -/
def etaQuotientMultiplierExp (N : ℕ) (r : ℕ → ℤ) (a b d t : ℤ) : ℤ :=
  (∑ δ ∈ N.divisors, ((N / δ : ℕ) : ℤ) * r δ) *
      ((a + d) * t - b * d * N * t ^ 2 - 3 * t * d) +
    (∑ δ ∈ N.divisors, (δ : ℤ) * r δ) * (b * d) +
    (∑ δ ∈ N.divisors, r δ) * (3 * d - 3)

/-- Defining formula for `etaQuotientMultiplierExp`. -/
theorem etaQuotientMultiplierExp_def (N : ℕ) (r : ℕ → ℤ) (a b d t : ℤ) :
    etaQuotientMultiplierExp N r a b d t =
      (∑ δ ∈ N.divisors, ((N / δ : ℕ) : ℤ) * r δ) *
          ((a + d) * t - b * d * N * t ^ 2 - 3 * t * d) +
        (∑ δ ∈ N.divisors, (δ : ℤ) * r δ) * (b * d) +
        (∑ δ ∈ N.divisors, r δ) * (3 * d - 3) :=
  (rfl)

/-- When the two weighted divisor sums `∑ δ * r δ` and `∑ (N / δ) * r δ` are divisible by `24`,
`etaQuotientMultiplierExp N r a b d t` reduces modulo `24` to
`(∑ δ ∈ N.divisors, r δ) * (3 * d - 3)`. -/
theorem etaQuotientMultiplierExp_modEq {N : ℕ} {r : ℕ → ℤ}
    (h24 : (24 : ℤ) ∣ ∑ δ ∈ N.divisors, (δ : ℤ) * r δ)
    (h24' : (24 : ℤ) ∣ ∑ δ ∈ N.divisors, ((N / δ : ℕ) : ℤ) * r δ) (a b d t : ℤ) :
    etaQuotientMultiplierExp N r a b d t ≡ (∑ δ ∈ N.divisors, r δ) * (3 * d - 3) [ZMOD 24] := by
  obtain ⟨A, hA⟩ := h24
  obtain ⟨B, hB⟩ := h24'
  refine Int.modEq_iff_dvd.mpr
    ⟨-(B * ((a + d) * t - b * d * N * t ^ 2 - 3 * t * d) + A * (b * d)), ?_⟩
  rw [etaQuotientMultiplierExp_def, hA, hB]
  ring

/-- Regrouping the even-`c` eta-multiplier exponent sum over `δ ∈ N.divisors` when `c = N * t`
into `etaQuotientMultiplierExp N r a b d t`. -/
private theorem sum_mul_etaMultiplierExpEvenC (N : ℕ) (r : ℕ → ℤ) (a b d t : ℤ) :
    ∑ δ ∈ N.divisors, r δ * etaMultiplierExpEvenC a (b * δ) ((N / δ : ℕ) * t) d =
      etaQuotientMultiplierExp N r a b d t := by
  rw [etaQuotientMultiplierExp_def, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun δ hδ ↦ ?_
  rw [etaMultiplierExpEvenC_def]
  linear_combination (-(r δ * b * d * (N / δ : ℕ) * t ^ 2)) *
    (Nat.cast_mul_div_of_dvd (R := ℤ) (Nat.dvd_of_mem_divisors hδ))

/-- Evaluating the eta-quotient multiplier when `γ 1 0 = N * t` and `γ 1 1` is odd: each factor
`ε(γ_δ)` is given by the odd-`d` Kronecker form, factoring the multiplier into the product of
`(kroneckerSym ((N / δ : ℕ) * t) (γ 1 1)) ^ r δ` and `e24` of `etaQuotientMultiplierExp`. -/
theorem etaQuotientMultiplier_eq_prod_kroneckerSym_mul_e24_of_odd_d {N : ℕ}
    (r : ℕ → ℤ) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N) {t : ℤ} (ht : γ 1 0 = N * t)
    (hdo : Odd (γ 1 1)) :
    etaQuotientMultiplier N r ⟨γ, hγ⟩ =
      (∏ δ ∈ N.divisors, (kroneckerSym ((N / δ : ℕ) * t) (γ 1 1) : ℂ) ^ r δ) *
        e24 (etaQuotientMultiplierExp N r (γ 0 0) (γ 0 1) (γ 1 1) t) := by
  have hε (δ : ℕ) (hδ : δ ∈ N.divisors) :
      etaMultiplier (conjScaleGamma0 (Nat.dvd_of_mem_divisors hδ) ⟨γ, hγ⟩) =
        (kroneckerSym ((N / δ : ℕ) * t) (γ 1 1) : ℂ) *
          e24 (etaMultiplierExpEvenC (γ 0 0) (γ 0 1 * δ) ((N / δ : ℕ) * t) (γ 1 1)) := by
    have h10 := conjScaleGamma0_apply_one_zero_of_eq (Nat.dvd_of_mem_divisors hδ) hγ ht
    rw [etaMultiplier_eq_kroneckerSym_mul_of_odd_d _ (by simpa using hdo), h10]
    simp [mul_comm (δ : ℤ)]
  rw [etaQuotientMultiplier_eq_prod r hγ hε, prod_mul_e24_zpow, sum_mul_etaMultiplierExpEvenC]

end TauCeti.ModularForm
