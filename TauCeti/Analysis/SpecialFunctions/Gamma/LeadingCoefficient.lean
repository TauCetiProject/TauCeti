/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Analysis.SpecialFunctions.Gamma.Order

/-!
# Leading coefficients of the archimedean gamma factors at nonpositive integers

Deligne's archimedean factors `Gammaℝ s = π ^ (-s / 2) Γ(s / 2)` and
`Gammaℂ s = 2 (2π) ^ (-s) Γ(s)` have simple poles at `-2m` and `-m` respectively.
This file computes their leading Laurent coefficients there:
`meromorphicTrailingCoeffAt Gammaℝ (-2m) = 2 π ^ m (-1) ^ m / m!` and
`meromorphicTrailingCoeffAt Gammaℂ (-m) = 2 (2π) ^ m (-1) ^ m / m!`.

The functional equation of a Dedekind zeta function relates its behaviour at `1 - n` to its
value at `n` through the factor `Gammaℝ s ^ r₁ * Gammaℂ s ^ r₂`, so what enters is the ratio of
the value of each factor at `n` to its leading coefficient at `1 - n`. For every natural `k`,
* `Gammaℝ (2k) / meromorphicTrailingCoeffAt Gammaℝ (1 - 2k) = (-1) ^ k Gammaℂ (2k)`;
* `Gammaℝ (2k + 1) / meromorphicTrailingCoeffAt Gammaℝ (-2k) = (-1) ^ k (π / 2) Gammaℂ (2k + 1)`;
* `Gammaℂ (k + 1) / meromorphicTrailingCoeffAt Gammaℂ (-k) = (-1) ^ k (π / 2) Gammaℂ (k + 1) ^ 2`.

Since `Gammaℂ (k + 1) = 2 k! / (2π) ^ (k + 1)`, all three are nonzero rational multiples of
powers of `π`. For the reciprocal factor `s ↦ (Gammaℝ s)⁻¹ ^ r₁ * (Gammaℂ s)⁻¹ ^ r₂` and
`n ≥ 1` this gives:
* `TauCeti.analyticOrderAt_inv_Gammaℝ_pow_mul_inv_Gammaℂ_pow_one_sub`: the order of vanishing at
  `1 - n` is `d = r₂`, plus `r₁` when `n` is odd;
* `TauCeti.exists_rat_meromorphicTrailingCoeffAt_inv_Gammaℝ_pow_mul_inv_Gammaℂ_pow_one_sub`: its
  leading coefficient at `1 - n`, times `Gammaℝ n ^ r₁ * Gammaℂ n ^ r₂`, is a nonzero rational
  multiple of `π ^ (d - (r₁ + 2 r₂) n)`.

These are the archimedean inputs to Borel's computation of the leading coefficient of a Dedekind
zeta function at a negative integer.

## References

* A. Borel, *Cohomologie de SLₙ et valeurs de fonctions zêta aux points entiers*, Ann. Sc. Norm.
  Super. Pisa (4) 4 (1977), §1.4 and §6.4.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §5.
-/

public section

open Real Filter Topology
open scoped Nat

namespace Complex

/-- The complex archimedean factor at a positive integer: `Γ_ℂ(k + 1) = 2 k! / (2π) ^ (k + 1)`. -/
theorem Gammaℂ_natCast_add_one (k : ℕ) :
    Gammaℂ (k + 1) = 2 * k ! / (2 * π) ^ (k + 1) := by
  rw [Gammaℂ_def, Gamma_nat_eq_factorial,
    show -((k : ℂ) + 1) = -((k + 1 : ℕ) : ℂ) by push_cast; ring, cpow_neg, cpow_natCast]
  ring

/-- The real archimedean factor at a positive even integer: `Γ_ℝ(2k + 2) = k! / π ^ (k + 1)`. -/
theorem Gammaℝ_two_mul_natCast_add_two (k : ℕ) :
    Gammaℝ (2 * k + 2) = k ! / π ^ (k + 1) := by
  rw [Gammaℝ_def, show (2 * (k : ℂ) + 2) / 2 = k + 1 by ring, Gamma_nat_eq_factorial,
    show -(2 * (k : ℂ) + 2) / 2 = -((k + 1 : ℕ) : ℂ) by push_cast; ring, cpow_neg, cpow_natCast]
  ring

/-- The leading Laurent coefficient of `Gammaℂ` at its simple pole `-m` is
`2 (2π) ^ m (-1) ^ m / m!`. -/
@[simp]
theorem meromorphicTrailingCoeffAt_Gammaℂ_neg_nat (m : ℕ) :
    meromorphicTrailingCoeffAt Gammaℂ (-(m : ℂ)) = 2 * (2 * π) ^ m * (-1) ^ m / m ! := by
  have he : Gammaℂ = (fun z : ℂ ↦ 2 * (2 * π : ℂ) ^ (-z)) * Gamma := funext Gammaℂ_def
  have ha : AnalyticAt ℂ (fun z : ℂ ↦ 2 * (2 * π : ℂ) ^ (-z)) (-(m : ℂ)) := by
    have hp : (2 * π : ℂ) ∈ slitPlane :=
      Or.inl (by simpa using mul_pos (by norm_num : (0 : ℝ) < 2) pi_pos)
    exact analyticAt_const.mul (analyticAt_const.cpow (by fun_prop) hp)
  rw [he, ha.meromorphicAt.meromorphicTrailingCoeffAt_mul (Meromorphic.Gamma _),
    ha.meromorphicTrailingCoeffAt_of_ne_zero (by simp [pi_ne_zero]),
    meromorphicTrailingCoeffAt_Gamma_neg_nat, neg_neg, cpow_natCast]
  ring

/-- The leading Laurent coefficient of `Gammaℝ` at its simple pole `-2m` is
`2 π ^ m (-1) ^ m / m!`. -/
@[simp]
theorem meromorphicTrailingCoeffAt_Gammaℝ_neg_two_mul_nat (m : ℕ) :
    meromorphicTrailingCoeffAt Gammaℝ (-(2 * m : ℂ)) = 2 * π ^ m * (-1) ^ m / m ! := by
  set g : ℂ → ℂ := fun z ↦ z / 2
  have he : Gammaℝ = (fun z : ℂ ↦ (π : ℂ) ^ (-z / 2)) * (Gamma ∘ g) := funext Gammaℝ_def
  have ha : AnalyticAt ℂ (fun z : ℂ ↦ (π : ℂ) ^ (-z / 2)) (-(2 * m : ℂ)) := by
    fun_prop (disch := exact Or.inl (by simpa using pi_pos))
  have hg : AnalyticAt ℂ g (-(2 * m : ℂ)) := by fun_prop
  have hgx : g (-(2 * m : ℂ)) = -(m : ℂ) := by simp only [g]; ring
  have hg' : deriv g (-(2 * m : ℂ)) ≠ 0 := by
    simp [g, deriv_div_const]
  have hgo : analyticOrderAt (fun z ↦ g z - g (-(2 * m : ℂ))) (-(2 * m : ℂ)) = 1 :=
    hg.analyticOrderAt_sub_eq_one_of_deriv_ne_zero hg'
  have hnc : ¬EventuallyConst g (𝓝 (-(2 * m : ℂ))) := by
    simp [eventuallyConst_iff_analyticOrderAt_sub_eq_top, hgo]
  -- The linear factor `z / 2 + m` has leading coefficient `1 / 2` at `-2m`.
  have hlin : meromorphicTrailingCoeffAt (fun z ↦ g z - g (-(2 * m : ℂ))) (-(2 * m : ℂ)) =
      1 / 2 := by
    have hfun : (fun z ↦ g z - g (-(2 * m : ℂ))) =
        (fun _ : ℂ ↦ (1 / 2 : ℂ)) * (· - (-(2 * m : ℂ))) := by
      funext z
      simp only [g, Pi.mul_apply]
      ring
    classical
    rw [hfun, analyticAt_const.meromorphicAt.meromorphicTrailingCoeffAt_mul (by fun_prop),
      meromorphicTrailingCoeffAt_const, meromorphicTrailingCoeffAt_id_sub_const]
    simp
  have hcomp := (Meromorphic.Gamma (g (-(2 * m : ℂ)))).meromorphicTrailingCoeffAt_comp hg hnc
  rw [hlin, hgx, meromorphicOrderAt_Gamma_neg_nat, meromorphicTrailingCoeffAt_Gamma_neg_nat]
    at hcomp
  rw [he, ha.meromorphicAt.meromorphicTrailingCoeffAt_mul
      ((Meromorphic.Gamma _).comp_analyticAt hg),
    ha.meromorphicTrailingCoeffAt_of_ne_zero (by simp [pi_ne_zero]), hcomp]
  rw [show -(-(2 * m : ℂ)) / 2 = (m : ℂ) by ring, cpow_natCast]
  rw [show (-1 : WithTop ℤ).untop₀ = -1 by simp]
  simp only [zpow_neg, zpow_one, smul_eq_mul]
  ring

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
  field_simp
  ring_nf
  rw [pow_mul', neg_one_sq, one_pow, mul_one]

/-- `Gammaℝ` does not vanish at the odd integers `1 - 2k`, which are not among its poles. -/
theorem Gammaℝ_one_sub_two_mul_natCast_ne_zero (k : ℕ) : Gammaℝ (1 - 2 * k) ≠ 0 := by
  rw [Ne, Gammaℝ_eq_zero_iff]
  rintro ⟨j, hj⟩
  have h := congrArg re hj
  simp only [sub_re, one_re, mul_re, re_ofNat, natCast_re, im_ofNat, natCast_im, mul_zero,
    sub_zero, neg_re] at h
  have hreal : (1 : ℝ) = 2 * (k - j) := by linarith
  have hint : (1 : ℤ) = 2 * ((k : ℤ) - j) := by exact_mod_cast hreal
  omega

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
  have ha : AnalyticAt ℂ Gammaℝ (1 - 2 * k) := by
    have := (differentiable_Gammaℝ_inv.analyticAt (1 - 2 * k : ℂ)).inv (inv_ne_zero hne)
    simpa only [Pi.inv_def, inv_inv] using this
  rw [ha.meromorphicTrailingCoeffAt_of_ne_zero hne, Gammaℝ_div_Gammaℝ_one_sub hodd,
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
  field_simp
  ring_nf
  rw [pow_mul', neg_one_sq, one_pow]
  ring

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
  have hRo : meromorphicOrderAt Gammaℝ (1 - n) = if Even n then 0 else -1 := by
    rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
    · rw [ite_eq_left (even_two_mul k), meromorphicOrderAt_Gammaℝ_eq_zero_iff]
      push_cast
      exact Gammaℝ_one_sub_two_mul_natCast_ne_zero k
    · rw [ite_eq_right (Nat.not_even_bit1 k), meromorphicOrderAt_Gammaℝ_eq_neg_one_iff]
      exact ⟨k, by push_cast; ring⟩
  have hm : meromorphicOrderAt (fun s : ℂ ↦ (Gammaℝ s)⁻¹ ^ r₁ * (Gammaℂ s)⁻¹ ^ r₂) (1 - n) =
      (((if Even n then 0 else r₁) + r₂ : ℕ) : ℤ) := by
    rw [fun_meromorphicOrderAt_mul (by fun_prop) (by fun_prop),
      fun_meromorphicOrderAt_pow (by fun_prop), fun_meromorphicOrderAt_pow (by fun_prop),
      fun_meromorphicOrderAt_inv, fun_meromorphicOrderAt_inv, hRo, hCo]
    split_ifs <;> simp
  have ha : AnalyticAt ℂ (fun s : ℂ ↦ (Gammaℝ s)⁻¹ ^ r₁ * (Gammaℂ s)⁻¹ ^ r₂) (1 - n) :=
    ((differentiable_Gammaℝ_inv.analyticAt _).pow r₁).mul
      ((differentiable_Gammaℂ_inv.analyticAt _).pow r₂)
  rw [ha.meromorphicOrderAt_eq] at hm
  cases ho : analyticOrderAt (fun s : ℂ ↦ (Gammaℝ s)⁻¹ ^ r₁ * (Gammaℂ s)⁻¹ ^ r₂) (1 - n) with
  | top =>
    simp only [ho, ENat.map_top] at hm
    exact (WithTop.top_ne_coe hm).elim
  | coe k =>
    simp only [ho, ENat.map_natCast] at hm
    exact_mod_cast hm

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
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr pi_ne_zero
  rw [MeromorphicAt.meromorphicTrailingCoeffAt_fun_mul (by fun_prop) (by fun_prop),
    MeromorphicAt.meromorphicTrailingCoeffAt_fun_pow (by fun_prop),
    MeromorphicAt.meromorphicTrailingCoeffAt_fun_pow (by fun_prop),
    meromorphicTrailingCoeffAt_fun_inv, meromorphicTrailingCoeffAt_fun_inv,
    show ∀ a b c d : ℂ, a⁻¹ ^ r₁ * b⁻¹ ^ r₂ * (c ^ r₁ * d ^ r₂) = (c / a) ^ r₁ * (d / b) ^ r₂
      from fun a b c d ↦ by ring, hR, hC, mul_pow, mul_pow,
    ← zpow_natCast ((π : ℂ) ^ ((if Even n then 0 else 1 : ℤ) - n)) r₁,
    ← zpow_natCast ((π : ℂ) ^ (1 - 2 * n : ℤ)) r₂, ← zpow_mul, ← zpow_mul]
  push_cast
  rw [show ∀ a b c d : ℂ, a * b * (c * d) = a * c * (b * d) from fun a b c d ↦ by ring,
    ← zpow_add₀ hπ]
  congr 2
  split_ifs <;> ring

end TauCeti
