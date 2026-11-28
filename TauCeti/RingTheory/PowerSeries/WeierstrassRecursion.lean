/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.Topology.MetricSpace.Ultra.Basic
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Non-vanishing recursion for power series satisfying a cubic ODE

Let `x` be a formal power series satisfying the Weierstrass-type differential equations
`(d⁄dX x) ^ 2 = 4 * x ^ 3 + C a₁ ^ 2 * x ^ 2 + 4 * x` and
`d⁄dX (d⁄dX x) = 6 * x ^ 2 + C a₁ ^ 2 * x + 2`.
Differentiating `x ^ n * d⁄dX x` yields the three-term linear identity
`d⁄dX (x ^ n * d⁄dX x) = (4 n + 6) • x ^ (n + 2) + ((n + 1) a₁ ^ 2) • x ^ (n + 1) +`
`(4 n + 2) • x ^ n`.

Over an ultrametric normed field `K` where an odd prime `p = 2 m + 1` has `‖(p : K)‖ < 1` and
every integer coprime to `p` has norm `1`, extracting the `z ^ (p - 1)` coefficient produces a
recursion modulo the maximal ideal. If `‖coeff (p - 1) x‖ < 1`, two-step induction forces
`‖coeff (p - 1) (x ^ n)‖ < 1` for all `n ≤ m`; when `X ^ 2 ∣ x` and `coeff 2 x = 1`, this
contradicts `coeff (2 m) (x ^ m) = 1`, forcing `‖coeff (p - 1) x‖ = 1`.

## Main results

* `TauCeti.derivative_pow_mul_derivative_of_sq_eq`: the algebraic ODE identity for
  `d⁄dX (x ^ n * d⁄dX x)` over any commutative ring.
* `TauCeti.coeff_two_mul_pow_eq_one`: if `X ^ 2 ∣ x` and `coeff 2 x = 1`, then
  `coeff (2 * m) (x ^ m) = 1`.
* `TauCeti.norm_coeff_pow_lt_one_of_cubic_ode`: two-step induction propagating
  `‖coeff (p - 1) (x ^ n)‖ < 1` up to `n ≤ m`.
* `TauCeti.norm_coeff_eq_one_of_cubic_ode`: unit-norm criterion `‖coeff (p - 1) x‖ = 1`.

## Provenance

Adapted from `New.CMLattice.derivative_pow_mul_derivative_taylorVia_translatedX`,
`New.CMLattice.coeff_two_mul_taylorVia_translatedX_pow`,
`New.CMLattice.norm_coeff_pow_taylorVia_translatedX_lt_one`, and
`New.CMLattice.norm_coeff_taylorVia_translatedX_eq_one` in
`grh/src/New/Derivatives/FormalGroup/FrobeniusCongruence.lean` of
[lsernau/grh-lean](https://github.com/lsernau/grh-lean), commit
`72fead102f663d5c7a407964a13dc0cf9d977207` (Apache 2.0, Copyright 2026 Anthropic, PBC).
-/

public section

namespace TauCeti

open PowerSeries

/-- Algebraic recursion for a formal power series `x` satisfying the cubic ODE
`(d⁄dX x) ^ 2 = 4 * x ^ 3 + C a₁ ^ 2 * x ^ 2 + 4 * x` and
`d⁄dX (d⁄dX x) = 6 * x ^ 2 + C a₁ ^ 2 * x + 2`. -/
theorem derivative_pow_mul_derivative_of_sq_eq {R : Type*} [CommRing R] {x : PowerSeries R}
    {a₁ : R} (hsq : d⁄dX x ^ 2 = 4 * x ^ 3 + C a₁ ^ 2 * x ^ 2 + 4 * x)
    (hdd : d⁄dX (d⁄dX x) = 6 * x ^ 2 + C a₁ ^ 2 * x + 2) (n : ℕ) :
    d⁄dX (x ^ n * d⁄dX x) =
      ((4 * n + 6 : ℕ) : R) • x ^ (n + 2) +
      ((n + 1 : ℕ) * a₁ ^ 2 : R) • x ^ (n + 1) +
      ((4 * n + 2 : ℕ) : R) • x ^ n := by
  rw [Derivation.leibniz, Derivation.leibniz_pow, hdd]
  simp only [smul_eq_C_mul, smul_eq_mul, nsmul_eq_mul, map_mul, map_pow, map_natCast]
  cases n with
  | zero => simp
  | succ n =>
    rw [Nat.add_sub_cancel]
    push_cast
    linear_combination (n + 1) * x ^ n * hsq

/-- If `X ^ 2 ∣ x` and `coeff 2 x = 1`, then `coeff (2 * m) (x ^ m) = 1`. -/
theorem coeff_two_mul_pow_eq_one {R : Type*} [CommSemiring R] {x : PowerSeries R}
    (hdvd : X ^ 2 ∣ x) (h2 : coeff 2 x = 1) (m : ℕ) :
    coeff (2 * m) (x ^ m) = 1 := by
  obtain ⟨u, rfl⟩ := hdvd
  have hu : constantCoeff u = 1 := by simpa [coeff_X_pow_mul'] using h2
  simp [mul_pow, ← pow_mul, coeff_X_pow_mul', hu]

/-- Over an ultrametric normed field `K` where an odd prime `p = 2 * m + 1` has `‖(p : K)‖ < 1`
and integers coprime to `p` have norm `1`, if `x` satisfies the cubic ODE recursion and
`‖coeff (p - 1) x‖ < 1`, then `‖coeff (p - 1) (x ^ n)‖ < 1` for every `n ≤ m`. -/
theorem norm_coeff_pow_lt_one_of_cubic_ode {K : Type*} [NormedField K] [IsUltrametricDist K]
    {p m : ℕ} (hp : p.Prime) (hp_eq : p = 2 * m + 1) (hp_lt : ‖(p : K)‖ < 1)
    (h_int : ∀ k : ℕ, ‖(k : K)‖ ≤ 1) (h_cop : ∀ k : ℕ, p.Coprime k → ‖(k : K)‖ = 1)
    {x : PowerSeries K} {a₁ : K} (ha₁ : ‖a₁‖ ≤ 1)
    (hsq : d⁄dX x ^ 2 = 4 * x ^ 3 + C a₁ ^ 2 * x ^ 2 + 4 * x)
    (hdd : d⁄dX (d⁄dX x) = 6 * x ^ 2 + C a₁ ^ 2 * x + 2)
    (h_top : ∀ n : ℕ, n + 2 ≤ m → ‖coeff p (x ^ n * d⁄dX x)‖ ≤ 1)
    (h_lt : ‖coeff (p - 1) x‖ < 1) {n : ℕ} (hn : n ≤ m) :
    ‖coeff (p - 1) (x ^ n)‖ < 1 := by
  induction n using Nat.twoStepInduction with
  | zero => simp [coeff_one, Nat.sub_ne_zero_of_lt hp.one_lt]
  | one => simpa only [pow_one] using h_lt
  | more n ih₀ ih₁ =>
    set c₀ := coeff (p - 1) (x ^ n)
    set c₁ := coeff (p - 1) (x ^ (n + 1))
    set c₂ := coeff (p - 1) (x ^ (n + 2))
    have h_rec : ‖((4 * n + 6 : ℕ) : K) * c₂ + ((n + 1 : ℕ) * a₁ ^ 2) * c₁ +
        ((4 * n + 2 : ℕ) : K) * c₀‖ < 1 := by
      have h_eq := congrArg (coeff (p - 1)) (derivative_pow_mul_derivative_of_sq_eq hsq hdd n)
      rw [coeff_derivative, ← Nat.cast_add_one, Nat.sub_add_cancel hp.one_le] at h_eq
      simp only [map_add, coeff_smul, smul_eq_mul] at h_eq
      rw [← h_eq, norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (h_top n hn)).trans_lt hp_lt
    have h_lead : ‖((4 * n + 6 : ℕ) : K)‖ = 1 :=
      h_cop (4 * n + 6) (by
        rw [show 4 * n + 6 = 2 * (2 * n + 3) by omega]
        exact .mul_right (Nat.coprime_two_right.mpr ⟨m, hp_eq⟩)
          (Nat.coprime_of_lt_prime (Nat.succ_ne_zero _) (by omega) hp))
    have h_prev : ‖((n + 1 : ℕ) * a₁ ^ 2) * c₁ + ((4 * n + 2 : ℕ) : K) * c₀‖ < 1 := by
      refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)
      · rw [norm_mul, norm_mul, norm_pow]
        have hf : ‖((n + 1 : ℕ) : K)‖ * ‖a₁‖ ^ 2 ≤ 1 :=
          (mul_le_of_le_one_left (by positivity) (h_int (n + 1))).trans
            (pow_le_one₀ (norm_nonneg _) ha₁)
        exact (mul_le_of_le_one_left (norm_nonneg _) hf).trans_lt (ih₁ (by omega))
      · rw [norm_mul]
        exact (mul_le_of_le_one_left (norm_nonneg _) (h_int (4 * n + 2))).trans_lt (ih₀ (by omega))
    calc ‖c₂‖ = ‖((4 * n + 6 : ℕ) : K) * c₂‖ := by rw [norm_mul, h_lead, one_mul]
      _ = ‖(((4 * n + 6 : ℕ) : K) * c₂ + ((n + 1 : ℕ) * a₁ ^ 2) * c₁ +
            ((4 * n + 2 : ℕ) : K) * c₀) +
            -(((n + 1 : ℕ) * a₁ ^ 2) * c₁ + ((4 * n + 2 : ℕ) : K) * c₀)‖ := by ring_nf
      _ < 1 := (IsUltrametricDist.norm_add_le_max _ _).trans_lt
          (max_lt h_rec (by rwa [norm_neg]))

/-- Under the hypotheses of `TauCeti.norm_coeff_pow_lt_one_of_cubic_ode`, if in addition
`X ^ 2 ∣ x`, `coeff 2 x = 1`, and `‖coeff (p - 1) x‖ ≤ 1`, then `‖coeff (p - 1) x‖ = 1`. -/
theorem norm_coeff_eq_one_of_cubic_ode {K : Type*} [NormedField K] [IsUltrametricDist K]
    {p m : ℕ} (hp : p.Prime) (hp_eq : p = 2 * m + 1) (hp_lt : ‖(p : K)‖ < 1)
    (h_int : ∀ k : ℕ, ‖(k : K)‖ ≤ 1) (h_cop : ∀ k : ℕ, p.Coprime k → ‖(k : K)‖ = 1)
    {x : PowerSeries K} {a₁ : K} (ha₁ : ‖a₁‖ ≤ 1)
    (hsq : d⁄dX x ^ 2 = 4 * x ^ 3 + C a₁ ^ 2 * x ^ 2 + 4 * x)
    (hdd : d⁄dX (d⁄dX x) = 6 * x ^ 2 + C a₁ ^ 2 * x + 2)
    (hdvd : X ^ 2 ∣ x) (h2 : coeff 2 x = 1)
    (h_top : ∀ n : ℕ, n + 2 ≤ m → ‖coeff p (x ^ n * d⁄dX x)‖ ≤ 1)
    (h_le : ‖coeff (p - 1) x‖ ≤ 1) :
    ‖coeff (p - 1) x‖ = 1 := by
  refine h_le.eq_of_not_lt fun h_lt ↦ ?_
  have h_last := norm_coeff_pow_lt_one_of_cubic_ode hp hp_eq hp_lt h_int h_cop ha₁ hsq hdd
    h_top h_lt le_rfl
  rw [show p - 1 = 2 * m by omega, coeff_two_mul_pow_eq_one hdvd h2 m, norm_one] at h_last
  exact lt_irrefl 1 h_last

end TauCeti
