/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Analysis.SpecialFunctions.Gamma.Archimedean
public import TauCeti.Analysis.SpecialFunctions.Gamma.Order
import TauCeti.Analysis.Meromorphic.TrailingCoefficient

/-!
# Leading coefficients of the archimedean gamma factors at nonpositive integers

Deligne's archimedean factors `Gammaℝ s = π ^ (-s / 2) Γ(s / 2)` and
`Gammaℂ s = 2 (2π) ^ (-s) Γ(s)` have simple poles at `-2m` and `-m` respectively.
This file computes their leading Laurent coefficients there:
`meromorphicTrailingCoeffAt Gammaℝ (-2m) = 2 π ^ m (-1) ^ m / m!` and
`meromorphicTrailingCoeffAt Gammaℂ (-m) = 2 (2π) ^ m (-1) ^ m / m!`, in particular `2` at `0`
(`Complex.meromorphicTrailingCoeffAt_Gammaℝ_zero`,
`Complex.meromorphicTrailingCoeffAt_Gammaℂ_zero`).

The functional equation of a Dedekind zeta function relates its behaviour at `1 - n` to its
value at `n` through the factor `Gammaℝ s ^ r₁ * Gammaℂ s ^ r₂`, so what enters is the ratio of
the value of each factor at `n` to its leading coefficient at `1 - n`. For every natural `k`,
* `Gammaℝ (2k) / meromorphicTrailingCoeffAt Gammaℝ (1 - 2k) = (-1) ^ k Gammaℂ (2k)`;
* `Gammaℝ (2k + 1) / meromorphicTrailingCoeffAt Gammaℝ (-2k) = (-1) ^ k (π / 2) Gammaℂ (2k + 1)`;
* `Gammaℂ (k + 1) / meromorphicTrailingCoeffAt Gammaℂ (-k) = (-1) ^ k (π / 2) Gammaℂ (k + 1) ^ 2`.

Since `Gammaℂ (k + 1) = 2 k! / (2π) ^ (k + 1)`, the last two are nonzero rational multiples of
powers of `π` for every `k`, and so is the first for `k ≥ 1` (it vanishes at `k = 0`).
For the reciprocal factor `s ↦ (Gammaℝ s)⁻¹ ^ r₁ * (Gammaℂ s)⁻¹ ^ r₂` and
`n ≥ 1` this gives:
* `TauCeti.analyticOrderAt_inv_Gammaℝ_pow_mul_inv_Gammaℂ_pow_one_sub`: the order of vanishing at
  `1 - n` is `d = r₂`, plus `r₁` when `n` is odd;
* `TauCeti.exists_rat_meromorphicTrailingCoeffAt_inv_Gammaℝ_pow_mul_inv_Gammaℂ_pow_one_sub`: its
  leading coefficient at `1 - n`, times `Gammaℝ n ^ r₁ * Gammaℂ n ^ r₂`, is a nonzero rational
  multiple of `π ^ (d - (r₁ + 2 r₂) n)`.

Equivalently, for the archimedean factor `s ↦ Gammaℝ s ^ r₁ * Gammaℂ s ^ r₂` itself:
* `TauCeti.meromorphicOrderAt_Gammaℝ_pow_mul_Gammaℂ_pow_one_sub_nat`: it has a pole of order
  exactly `d` at `1 - n`;
* `TauCeti.exists_rat_Gammaℝ_pow_mul_Gammaℂ_pow_eq_mul_meromorphicTrailingCoeffAt`: its value at
  `n` is a nonzero rational multiple of `π ^ (d - (r₁ + 2 r₂) n)` times its leading coefficient at
  `1 - n`.

These are the archimedean inputs to Borel's computation of the leading coefficient of a Dedekind
zeta function at a negative integer.

## References

* A. Borel, *Cohomologie de SLₙ et valeurs de fonctions zêta aux points entiers*, Ann. Sc. Norm.
  Super. Pisa (4) 4 (1977), §1.4 and §6.4.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §5.
-/

public section

open Real
open scoped Nat

namespace Complex

/-- The leading Laurent coefficient of `Gammaℂ` at its simple pole `-m` is
`2 (2π) ^ m (-1) ^ m / m!`. -/
@[simp]
theorem meromorphicTrailingCoeffAt_Gammaℂ_neg_nat (m : ℕ) :
    meromorphicTrailingCoeffAt Gammaℂ (-(m : ℂ)) = 2 * (2 * π) ^ m * (-1) ^ m / m ! := by
  have ha := analyticAt_two_mul_two_pi_cpow_neg (-(m : ℂ))
  rw [Gammaℂ_eq_mul_Gamma, ha.meromorphicAt.meromorphicTrailingCoeffAt_mul (Meromorphic.Gamma _),
    ha.meromorphicTrailingCoeffAt_of_ne_zero (by simp [pi_ne_zero]),
    meromorphicTrailingCoeffAt_Gamma_neg_nat, neg_neg, cpow_natCast]
  ring

/-- The leading Laurent coefficient of `Gammaℝ` at its simple pole `-2m` is
`2 π ^ m (-1) ^ m / m!`. -/
@[simp]
theorem meromorphicTrailingCoeffAt_Gammaℝ_neg_two_mul_nat (m : ℕ) :
    meromorphicTrailingCoeffAt Gammaℝ (-(2 * m : ℂ)) = 2 * π ^ m * (-1) ^ m / m ! := by
  have ha := analyticAt_pi_cpow_neg_div_two (-(2 * m : ℂ))
  have hdiv : (Gamma ∘ fun z : ℂ ↦ z / 2) = Gamma ∘ (· * 2⁻¹) := by simp only [div_eq_mul_inv]
  rw [Gammaℝ_eq_cpow_mul_Gamma_comp, hdiv, ha.meromorphicAt.meromorphicTrailingCoeffAt_mul
      ((Meromorphic.Gamma _).comp_analyticAt (by fun_prop)),
    ha.meromorphicTrailingCoeffAt_of_ne_zero (by simp [pi_ne_zero]),
    TauCeti.meromorphicTrailingCoeffAt_comp_mul_const (by norm_num),
    show -(2 * m : ℂ) * 2⁻¹ = -(m : ℂ) by ring, meromorphicOrderAt_Gamma_neg_nat,
    meromorphicTrailingCoeffAt_Gamma_neg_nat, show -(-(2 * m : ℂ)) / 2 = (m : ℂ) by ring,
    cpow_natCast, show (-1 : WithTop ℤ).untop₀ = -1 by simp]
  simp only [zpow_neg, zpow_one, inv_inv, smul_eq_mul]
  ring

/-- The leading Laurent coefficient of `Gammaℂ` at `0` is `2`. -/
@[simp]
theorem meromorphicTrailingCoeffAt_Gammaℂ_zero : meromorphicTrailingCoeffAt Gammaℂ 0 = 2 := by
  simpa using meromorphicTrailingCoeffAt_Gammaℂ_neg_nat 0

/-- The leading Laurent coefficient of `Gammaℝ` at `0` is `2`. -/
@[simp]
theorem meromorphicTrailingCoeffAt_Gammaℝ_zero : meromorphicTrailingCoeffAt Gammaℝ 0 = 2 := by
  simpa using meromorphicTrailingCoeffAt_Gammaℝ_neg_two_mul_nat 0

/-- At a nonpositive even integer `-2m`, the value of `Gammaℝ` at `2m + 1` divided by the leading
coefficient of `Gammaℝ` at `-2m` is `(-1) ^ m (π / 2) Gammaℂ (2m + 1)`. -/
theorem Gammaℝ_two_mul_natCast_add_one_div_meromorphicTrailingCoeffAt (m : ℕ) :
    Gammaℝ (2 * m + 1) / meromorphicTrailingCoeffAt Gammaℝ (-(2 * m : ℂ)) =
      (-1) ^ m * (π / 2) * Gammaℂ (2 * m + 1) := by
  have hdup := Gammaℝ_mul_Gammaℝ_add_one (2 * m + 1)
  rw [show (2 * m + 1 : ℂ) + 1 = 2 * m + 2 by ring, Gammaℝ_two_mul_natCast_add_two] at hdup
  rw [meromorphicTrailingCoeffAt_Gammaℝ_neg_two_mul_nat, ← hdup]
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr pi_ne_zero
  have hf : (m ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
  have h1 : ((-1 : ℂ) ^ m) ^ 2 = 1 := by rw [← pow_mul, pow_mul', neg_one_sq, one_pow]
  field_simp
  linear_combination -(Gammaℝ (2 * m + 1) * (π : ℂ) ^ (m + 1)) * h1

/-- At a negative odd integer `1 - 2k`, where `Gammaℝ` is analytic and nonzero, the value of
`Gammaℝ` at `2k` divided by its leading coefficient (its value) at `1 - 2k` is
`(-1) ^ k Gammaℂ (2k)`. For `k = 0` both sides vanish. -/
theorem Gammaℝ_two_mul_natCast_div_meromorphicTrailingCoeffAt (k : ℕ) :
    Gammaℝ (2 * k) / meromorphicTrailingCoeffAt Gammaℝ (1 - 2 * k) =
      (-1) ^ k * Gammaℂ (2 * k) := by
  have hodd (j : ℕ) : (2 * k : ℂ) ≠ -(2 * j + 1) := by
    intro h
    have := congrArg re h
    simp only [mul_re, re_ofNat, natCast_re, im_ofNat, natCast_im, mul_zero, sub_zero,
      neg_add_rev, add_re, neg_re, one_re] at this
    linarith [(k.cast_nonneg : (0 : ℝ) ≤ k), (j.cast_nonneg : (0 : ℝ) ≤ j)]
  have hne := Gammaℝ_one_sub_two_mul_natCast_ne_zero k
  rw [(analyticAt_Gammaℝ_of_ne_zero hne).meromorphicTrailingCoeffAt_of_ne_zero hne,
    Gammaℝ_div_Gammaℝ_one_sub hodd,
    show (π : ℂ) * (2 * k) / 2 = ((k * π : ℝ) : ℂ) by push_cast; ring, ← ofReal_cos,
    cos_nat_mul_pi]
  push_cast
  ring

/-- At a nonpositive integer `-k`, the value of `Gammaℂ` at `k + 1` divided by the leading
coefficient of `Gammaℂ` at `-k` is `(-1) ^ k (π / 2) Gammaℂ (k + 1) ^ 2`. -/
theorem Gammaℂ_natCast_add_one_div_meromorphicTrailingCoeffAt (k : ℕ) :
    Gammaℂ (k + 1) / meromorphicTrailingCoeffAt Gammaℂ (-(k : ℂ)) =
      (-1) ^ k * (π / 2) * Gammaℂ (k + 1) ^ 2 := by
  rw [meromorphicTrailingCoeffAt_Gammaℂ_neg_nat, Gammaℂ_natCast_add_one]
  have hf : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have h1 : ((-1 : ℂ) ^ k) ^ 2 = 1 := by rw [← pow_mul, pow_mul', neg_one_sq, one_pow]
  field_simp
  linear_combination -((2 * π : ℂ) ^ (k + 1)) * h1

end Complex

namespace TauCeti

open Complex

/-- For `n ≥ 1`, the entire reciprocal archimedean factor
`s ↦ (Gammaℝ s)⁻¹ ^ r₁ * (Gammaℂ s)⁻¹ ^ r₂` vanishes at `1 - n` to order exactly `r₂`, plus `r₁`
when `n` is odd: every complex factor has a simple pole there, and a real factor has one exactly
when `1 - n` is even. -/
theorem analyticOrderAt_inv_Gammaℝ_pow_mul_inv_Gammaℂ_pow_one_sub (r₁ r₂ : ℕ) {n : ℕ}
    (hn : 1 ≤ n) :
    analyticOrderAt (fun s : ℂ ↦ (Gammaℝ s)⁻¹ ^ r₁ * (Gammaℂ s)⁻¹ ^ r₂) (1 - n) =
      (((if Even n then 0 else r₁) + r₂ : ℕ) : ℕ∞) := by
  have hCo : meromorphicOrderAt Gammaℂ (1 - n) = -1 :=
    (meromorphicOrderAt_Gammaℂ_eq_neg_one_iff _).mpr ⟨n - 1, by push_cast [hn]; ring⟩
  have hRo := meromorphicOrderAt_Gammaℝ_one_sub_nat n
  have hm : meromorphicOrderAt (fun s : ℂ ↦ (Gammaℝ s)⁻¹ ^ r₁ * (Gammaℂ s)⁻¹ ^ r₂) (1 - n) =
      (((if Even n then 0 else r₁) + r₂ : ℕ) : ℤ) := by
    rw [fun_meromorphicOrderAt_mul (by fun_prop) (by fun_prop),
      fun_meromorphicOrderAt_pow (by fun_prop), fun_meromorphicOrderAt_pow (by fun_prop),
      fun_meromorphicOrderAt_inv, fun_meromorphicOrderAt_inv, hRo, hCo]
    split_ifs <;> simp
  have ha : AnalyticAt ℂ (fun s : ℂ ↦ (Gammaℝ s)⁻¹ ^ r₁ * (Gammaℂ s)⁻¹ ^ r₂) (1 - n) :=
    analyticAt_inv_Gammaℝ_pow_mul_inv_Gammaℂ_pow r₁ r₂ (1 - n)
  rw [ha.meromorphicOrderAt_eq] at hm
  exact ENat.map_natCast_injective (hm.trans (ENat.map_natCast _ _).symm)

/-- `Γ_ℂ(k + 1)` as a rational multiple of `π ^ (-(k + 1))`. -/
private theorem Gammaℂ_natCast_add_one_eq_rat_mul_zpow (k : ℕ) :
    Gammaℂ (k + 1) = ((2 * k ! / 2 ^ (k + 1) : ℚ) : ℂ) * (π : ℂ) ^ (-((k : ℤ) + 1)) := by
  rw [Gammaℂ_natCast_add_one, show -((k : ℤ) + 1) = -((k + 1 : ℕ) : ℤ) by push_cast; ring,
    zpow_neg, zpow_natCast, mul_pow]
  push_cast
  field_simp

private theorem exists_rat_Gammaℝ_div_meromorphicTrailingCoeffAt_one_sub {n : ℕ} (hn : 1 ≤ n) :
    ∃ q : ℚ, q ≠ 0 ∧ Gammaℝ n / meromorphicTrailingCoeffAt Gammaℝ (1 - n) =
      q * (π : ℂ) ^ ((if Even n then 0 else 1 : ℤ) - n) := by
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    refine ⟨(-1) ^ (j + 1) * (2 * (2 * j + 1) ! / 2 ^ (2 * j + 2)), by positivity, ?_⟩
    have h := Gammaℝ_two_mul_natCast_div_meromorphicTrailingCoeffAt (j + 1)
    rw [ite_eq_left (even_two_mul _)]
    push_cast at h ⊢
    rw [h, show (2 * ((j : ℂ) + 1)) = ((2 * j + 1 : ℕ) : ℂ) + 1 by push_cast; ring,
      Gammaℂ_natCast_add_one_eq_rat_mul_zpow,
      show (0 : ℤ) - 2 * ((j : ℤ) + 1) = -(((2 * j + 1 : ℕ) : ℤ) + 1) by push_cast; ring]
    push_cast
    ring
  · refine ⟨(-1) ^ k * ((2 * k) ! / 2 ^ (2 * k + 1)), by positivity, ?_⟩
    have h := Gammaℝ_two_mul_natCast_add_one_div_meromorphicTrailingCoeffAt k
    rw [ite_eq_right (Nat.not_even_bit1 k), show (1 : ℂ) - ((2 * k + 1 : ℕ) : ℂ) = -(2 * k : ℂ)
      by push_cast; ring]
    push_cast
    rw [h, show (2 * (k : ℂ) + 1) = ((2 * k : ℕ) : ℂ) + 1 by push_cast; ring,
      Gammaℂ_natCast_add_one_eq_rat_mul_zpow,
      show (1 : ℤ) - (2 * k + 1) = -(((2 * k : ℕ) : ℤ) + 1) + 1 by push_cast; ring,
      zpow_add_one₀ (ofReal_ne_zero.mpr pi_ne_zero)]
    push_cast
    ring

private theorem exists_rat_Gammaℂ_div_meromorphicTrailingCoeffAt_one_sub {n : ℕ} (hn : 1 ≤ n) :
    ∃ q : ℚ, q ≠ 0 ∧ Gammaℂ n / meromorphicTrailingCoeffAt Gammaℂ (1 - n) =
      q * (π : ℂ) ^ (1 - 2 * n : ℤ) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  refine ⟨(-1) ^ k * (2 * k ! / 2 ^ (k + 1)) ^ 2 / 2, by positivity, ?_⟩
  have h := Gammaℂ_natCast_add_one_div_meromorphicTrailingCoeffAt k
  rw [show (1 : ℂ) - ((k + 1 : ℕ) : ℂ) = -(k : ℂ) by push_cast; ring]
  push_cast
  rw [h, Gammaℂ_natCast_add_one_eq_rat_mul_zpow,
    show (1 : ℤ) - 2 * ((k : ℤ) + 1) = -((k : ℤ) + 1) + -((k : ℤ) + 1) + 1 by ring,
    zpow_add_one₀ (ofReal_ne_zero.mpr pi_ne_zero), zpow_add₀ (ofReal_ne_zero.mpr pi_ne_zero)]
  push_cast
  ring

/-- For `n ≥ 1`, the leading coefficient at `1 - n` of the entire reciprocal archimedean factor
`s ↦ (Gammaℝ s)⁻¹ ^ r₁ * (Gammaℂ s)⁻¹ ^ r₂`, multiplied by the value
`Gammaℝ n ^ r₁ * Gammaℂ n ^ r₂` of the archimedean factor at `n`, is a nonzero rational multiple
of `π ^ (d - (r₁ + 2 r₂) n)`, where `d` is the order of vanishing at `1 - n`
(`analyticOrderAt_inv_Gammaℝ_pow_mul_inv_Gammaℂ_pow_one_sub`). -/
theorem exists_rat_meromorphicTrailingCoeffAt_inv_Gammaℝ_pow_mul_inv_Gammaℂ_pow_one_sub
    (r₁ r₂ : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    ∃ q : ℚ, q ≠ 0 ∧
      meromorphicTrailingCoeffAt (fun s : ℂ ↦ (Gammaℝ s)⁻¹ ^ r₁ * (Gammaℂ s)⁻¹ ^ r₂) (1 - n) *
          (Gammaℝ n ^ r₁ * Gammaℂ n ^ r₂) =
        q * (π : ℂ) ^ ((((if Even n then 0 else r₁) + r₂ : ℕ) : ℤ) - (r₁ + 2 * r₂) * n) := by
  obtain ⟨qR, hqR, hR⟩ := exists_rat_Gammaℝ_div_meromorphicTrailingCoeffAt_one_sub hn
  obtain ⟨qC, hqC, hC⟩ := exists_rat_Gammaℂ_div_meromorphicTrailingCoeffAt_one_sub hn
  refine ⟨qR ^ r₁ * qC ^ r₂, mul_ne_zero (pow_ne_zero _ hqR) (pow_ne_zero _ hqC), ?_⟩
  have he : (((if Even n then 0 else r₁) + r₂ : ℕ) : ℤ) - (r₁ + 2 * r₂) * n =
      ((if Even n then 0 else 1 : ℤ) - n) * r₁ + (1 - 2 * n) * r₂ := by
    split_ifs <;> push_cast <;> ring
  rw [MeromorphicAt.meromorphicTrailingCoeffAt_fun_mul (by fun_prop) (by fun_prop),
    MeromorphicAt.meromorphicTrailingCoeffAt_fun_pow (by fun_prop),
    MeromorphicAt.meromorphicTrailingCoeffAt_fun_pow (by fun_prop),
    meromorphicTrailingCoeffAt_fun_inv, meromorphicTrailingCoeffAt_fun_inv,
    show ∀ a b c d : ℂ, a⁻¹ ^ r₁ * b⁻¹ ^ r₂ * (c ^ r₁ * d ^ r₂) = (c / a) ^ r₁ * (d / b) ^ r₂
      from fun a b c d ↦ by ring, hR, hC, he, zpow_add₀ (ofReal_ne_zero.mpr pi_ne_zero),
    zpow_mul, zpow_mul, zpow_natCast, zpow_natCast]
  push_cast
  ring

/-- The product `Γ_ℝ(s) ^ r₁ Γ_ℂ(s) ^ r₂` of archimedean factors has a pole of order `r₂` at
`1 - n` for even `n ≥ 1` and of order `r₁ + r₂` for odd `n`: the factor `Γ_ℂ` has a pole at every
nonpositive integer, while `Γ_ℝ` has one only at the nonpositive even integers. -/
theorem meromorphicOrderAt_Gammaℝ_pow_mul_Gammaℂ_pow_one_sub_nat (r₁ r₂ : ℕ) {n : ℕ}
    (hn : 1 ≤ n) :
    meromorphicOrderAt (fun s ↦ Gammaℝ s ^ r₁ * Gammaℂ s ^ r₂) (1 - n) =
      -((if Even n then r₂ else r₁ + r₂ : ℕ) : ℤ) := by
  have hR := meromorphic_Gammaℝ (1 - n)
  have hC := meromorphic_Gammaℂ (1 - n)
  -- both orders as integers cast into `WithTop ℤ`, so that `norm_cast` reduces to `ℤ`
  have hCord : meromorphicOrderAt Gammaℂ (1 - n) = ((-1 : ℤ) : WithTop ℤ) :=
    (meromorphicOrderAt_Gammaℂ_eq_neg_one_iff _).mpr ⟨n - 1, by push_cast [hn]; ring⟩
  have hRord :
      meromorphicOrderAt Gammaℝ (1 - n) = ((if Even n then 0 else -1 : ℤ) : WithTop ℤ) := by
    rw [meromorphicOrderAt_Gammaℝ_one_sub_nat]; split_ifs <;> simp
  have he : (fun s ↦ Gammaℝ s ^ r₁ * Gammaℂ s ^ r₂) = Gammaℝ ^ r₁ * Gammaℂ ^ r₂ := by
    ext; simp
  rw [he, meromorphicOrderAt_mul (hR.pow r₁) (hC.pow r₂), meromorphicOrderAt_pow hR,
    meromorphicOrderAt_pow hC, hCord, hRord]
  norm_cast
  split_ifs <;> push_cast <;> ring

/-- **The leading coefficient of the archimedean factors at `1 - n`.** For `n ≥ 1`, the value at
`n` of `Γ_ℝ(s) ^ r₁ Γ_ℂ(s) ^ r₂` is a nonzero rational multiple of `π ^ (d - (r₁ + 2 r₂) n)` times
its leading Laurent coefficient at `1 - n`, where `d` is the pole order there: `r₂` for even `n`
and `r₁ + r₂` for odd `n` (`meromorphicOrderAt_Gammaℝ_pow_mul_Gammaℂ_pow_one_sub_nat`). For the
signature `(r₁, r₂)` of a number field of degree `r₁ + 2 r₂` and `n ≥ 2`, this is the
archimedean part of the leading term of its Dedekind zeta function at `1 - n` (Borel 1977, §1.4);
at `n = 1` the pole of the completed zeta function at `0` also contributes. -/
theorem exists_rat_Gammaℝ_pow_mul_Gammaℂ_pow_eq_mul_meromorphicTrailingCoeffAt
    (r₁ r₂ : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    ∃ q : ℚ, q ≠ 0 ∧ Gammaℝ n ^ r₁ * Gammaℂ n ^ r₂ =
      q * (π : ℂ) ^ (((if Even n then r₂ else r₁ + r₂ : ℕ) : ℤ) - (r₁ + 2 * r₂ : ℕ) * n) *
        meromorphicTrailingCoeffAt (fun s ↦ Gammaℝ s ^ r₁ * Gammaℂ s ^ r₂) (1 - n) := by
  obtain ⟨q, hq, h⟩ :=
    exists_rat_meromorphicTrailingCoeffAt_inv_Gammaℝ_pow_mul_inv_Gammaℂ_pow_one_sub r₁ r₂ hn
  have hc : meromorphicTrailingCoeffAt (fun s ↦ Gammaℝ s ^ r₁ * Gammaℂ s ^ r₂) (1 - n) ≠ 0 :=
    MeromorphicAt.meromorphicTrailingCoeffAt_ne_zero (by fun_prop) (by
      rw [meromorphicOrderAt_Gammaℝ_pow_mul_Gammaℂ_pow_one_sub_nat r₁ r₂ hn]
      exact WithTop.coe_ne_top)
  have hinv : (fun s : ℂ ↦ (Gammaℝ s)⁻¹ ^ r₁ * (Gammaℂ s)⁻¹ ^ r₂) =
      fun s ↦ (Gammaℝ s ^ r₁ * Gammaℂ s ^ r₂)⁻¹ := by
    ext s
    rw [inv_pow, inv_pow, mul_inv]
  have he : ((if Even n then r₂ else r₁ + r₂ : ℕ) : ℤ) - (r₁ + 2 * r₂ : ℕ) * n =
      (((if Even n then 0 else r₁) + r₂ : ℕ) : ℤ) - (r₁ + 2 * r₂) * n := by
    split_ifs <;> push_cast <;> ring
  rw [hinv, meromorphicTrailingCoeffAt_fun_inv] at h
  refine ⟨q, hq, ?_⟩
  rw [he, ← h]
  field_simp

end TauCeti
