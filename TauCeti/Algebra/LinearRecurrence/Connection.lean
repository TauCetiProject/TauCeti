/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Factorial.DoubleFactorial

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-!
# Connection identity for three-term recurrences with linear lowering weight

Let `R` be a commutative ring, let `z, c₁, c₂ : R`, and let `P, Q : ℕ → R` be two sequences with
common initial term `P 0 = Q 0` satisfying the three-term recurrences

  `z * P m = P (m + 1) + m * c₁ * P (m - 1)`   and   `z * Q m = Q (m + 1) + m * c₂ * Q (m - 1)`

for all `m : ℕ` (at `m = 0` the lowering coefficient `0 * cᵢ` annihilates `P (-1)` and `Q (-1)`).
This file proves the explicit connection formula relating the two families across their variance
parameters `c₁` and `c₂`:

  `P n = ∑ k ∈ Finset.range (n / 2 + 1),`
  `  (n.choose (2 * k) * (2 * k - 1)‼) • ((c₂ - c₁) ^ k * Q (n - 2 * k))`.

No characteristic-zero or invertibility hypothesis on `R` is required; the combinatorial weights
`n.choose (2 * k) * (2 * k - 1)‼` (the number of partial matchings of `2 * k` elements chosen from
`n`) are natural numbers acting by `•`.

Specializing `(c₁, c₂)` connects variance-rescaled Appell and Hermite-type sequences uniformly:
* `c₁ = 1`, `c₂ = c ^ 2` gives the scaling (multiplication) expansion;
* `c₁ = 0`, `c₂ = 1` gives monomial-to-Hermite inversion (`z ^ n` in terms of `Q (n - 2 * k)`);
* `c₁ = 1`, `c₂ = a ^ 2 + b ^ 2` (and its dual) gives the Feldheim–Carlitz linear-combination
  expansion and Runge's rotational addition identity when `a ^ 2 + b ^ 2 = 1`.

## Main results

* `TauCeti.eq_sum_choose_mul_doubleFactorial_smul_of_mul_eq_add`: the connection expansion of `P n`
  in terms of `Q (n - 2 * k)` and powers of `c₂ - c₁`.

## References

* E. Feldheim, *Relations entre les polynômes de Jacobi, Laguerre et Hermite*, Acta Math. **74**
  (1941), 117–138.
* L. Carlitz, *Some formulas of E. Feldheim*, Acta Math. Acad. Sci. Hungar. **14** (1963), 21–29.
* A. Erdélyi et al., *Higher Transcendental Functions*, Vol. II, §10.13.
-/

public section

namespace TauCeti

open scoped Nat

/-- Auxiliary connection sum indexed up to `n`; terms with `2 * k > n` vanish via
`Nat.choose_eq_zero_of_lt`. -/
private def connectionSum {R : Type*} [CommRing R] (d : R) (Q : ℕ → R) (n : ℕ) : R :=
  ∑ k ∈ Finset.range (n + 1),
    (n.choose (2 * k) * (2 * k - 1)‼) • (d ^ k * Q (n - 2 * k))

private lemma connectionSum_eq_sum_div_two {R : Type*} [CommRing R] (d : R) (Q : ℕ → R) (n : ℕ) :
    connectionSum d Q n =
      ∑ k ∈ Finset.range (n / 2 + 1),
        (n.choose (2 * k) * (2 * k - 1)‼) • (d ^ k * Q (n - 2 * k)) := by
  unfold connectionSum
  refine (Finset.sum_subset (Finset.range_mono (by lia)) fun k _ hk => ?_).symm
  have hlt : n < 2 * k := by simp only [Finset.mem_range, not_lt] at hk; lia
  simp [Nat.choose_eq_zero_of_lt hlt]

private lemma connectionSum_mul_expand {R : Type*} [CommRing R] {z c₂ : R} (d : R) {Q : ℕ → R}
    (hQ : ∀ m, z * Q m = Q (m + 1) + m * c₂ * Q (m - 1)) (n : ℕ) :
    z * connectionSum d Q (n + 1) =
      (∑ k ∈ Finset.range (n + 2),
          (((n + 1).choose (2 * k) * (2 * k - 1)‼ : ℕ) : R) *
            (d ^ k * Q (n + 2 - 2 * k))) +
        (∑ k ∈ Finset.range (n + 2),
          (((n + 1).choose (2 * k) * (n + 1 - 2 * k) * (2 * k - 1)‼ : ℕ) : R) *
            (c₂ * d ^ k * Q (n - 2 * k))) := by
  unfold connectionSum
  simp_rw [nsmul_eq_mul]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rcases le_or_gt (2 * k) (n + 1) with hle | hgt
  · have hsub1 : n + 1 - 2 * k + 1 = n + 2 - 2 * k := by lia
    have hsub2 : n + 1 - 2 * k - 1 = n - 2 * k := by lia
    have hQm := hQ (n + 1 - 2 * k)
    rw [hsub1, hsub2] at hQm
    calc
      z * ((((n + 1).choose (2 * k) * (2 * k - 1)‼ : ℕ) : R) * (d ^ k * Q (n + 1 - 2 * k))) =
          (((n + 1).choose (2 * k) * (2 * k - 1)‼ : ℕ) : R) * d ^ k *
            (z * Q (n + 1 - 2 * k)) := by ring
      _ = _ := by
        rw [hQm]
        push_cast
        ring
  · simp [Nat.choose_eq_zero_of_lt hgt]

private lemma connectionSum_lower_c₁ {R : Type*} [CommRing R] (c₁ d : R) (Q : ℕ → R) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 2),
        (((n + 1).choose (2 * k) * (n + 1 - 2 * k) * (2 * k - 1)‼ : ℕ) : R) *
          (c₁ * d ^ k * Q (n - 2 * k))) =
      (n + 1 : ℕ) * c₁ * connectionSum d Q n := by
  unfold connectionSum
  simp_rw [nsmul_eq_mul]
  rw [Finset.sum_range_succ _ (n + 1)]
  have htop : (n + 1).choose (2 * (n + 1)) = 0 := Nat.choose_eq_zero_of_lt (by lia)
  rw [htop, zero_mul, zero_mul, Nat.cast_zero, zero_mul, add_zero, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hbinom : (n + 1).choose (2 * k) * (n + 1 - 2 * k) = n.choose (2 * k) * (n + 1) :=
    (Nat.choose_mul_succ_eq n (2 * k)).symm
  rw [hbinom]
  push_cast
  ring

private lemma connectionSum_raise_add_diff {R : Type*} [CommRing R] (d : R) (Q : ℕ → R) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 2),
        (((n + 1).choose (2 * k) * (2 * k - 1)‼ : ℕ) : R) *
          (d ^ k * Q (n + 2 - 2 * k))) +
      (∑ k ∈ Finset.range (n + 2),
        (((n + 1).choose (2 * k) * (n + 1 - 2 * k) * (2 * k - 1)‼ : ℕ) : R) *
          (d * d ^ k * Q (n - 2 * k))) =
      connectionSum d Q (n + 2) := by
  unfold connectionSum
  simp_rw [nsmul_eq_mul]
  rw [Finset.sum_range_succ' _ (n + 1), Finset.sum_range_succ' _ (n + 2)]
  simp only [Nat.mul_zero, Nat.sub_zero, Nat.choose_zero_right, pow_zero, one_mul]
  rw [Finset.sum_range_succ _ (n + 1), Finset.sum_range_succ _ (n + 1)]
  have htop1 : (n + 1).choose (2 * (n + 1)) = 0 := Nat.choose_eq_zero_of_lt (by lia)
  have htop2 : (n + 2).choose (2 * (n + 1 + 1)) = 0 := Nat.choose_eq_zero_of_lt (by lia)
  rw [htop1, htop2]
  simp only [zero_mul, Nat.cast_zero, add_zero]
  have hcomb :
      (∑ k ∈ Finset.range (n + 1),
          (((n + 1).choose (2 * (k + 1)) * (2 * (k + 1) - 1)‼ : ℕ) : R) *
            (d ^ (k + 1) * Q (n + 2 - 2 * (k + 1)))) +
        (∑ k ∈ Finset.range (n + 1),
          (((n + 1).choose (2 * k) * (n + 1 - 2 * k) * (2 * k - 1)‼ : ℕ) : R) *
            (d * d ^ k * Q (n - 2 * k))) =
        ∑ k ∈ Finset.range (n + 1),
          (((n + 2).choose (2 * (k + 1)) * (2 * (k + 1) - 1)‼ : ℕ) : R) *
            (d ^ (k + 1) * Q (n + 2 - 2 * (k + 1))) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hodd : 2 * (k + 1) - 1 = 2 * k + 1 := by lia
    have hsub : n + 2 - 2 * (k + 1) = n - 2 * k := by lia
    have hnat :
        (n + 1).choose (2 * (k + 1)) * (2 * (k + 1) - 1)‼ +
            (n + 1).choose (2 * k) * (n + 1 - 2 * k) * (2 * k - 1)‼ =
          (n + 2).choose (2 * (k + 1)) * (2 * (k + 1) - 1)‼ := by
      rw [hodd, ← Nat.choose_succ_right_eq (n + 1) (2 * k), mul_assoc,
        Nat.doubleFactorial_add_one (2 * k), mul_add 2 k 1,
        ← add_mul, add_comm ((n + 1).choose (2 * k + 2)),
        ← Nat.choose_succ_succ' (n + 1) (2 * k + 1)]
    rw [hsub, pow_succ', ← add_mul, ← Nat.cast_add, hnat]
  rw [add_right_comm, hcomb]

/-- One-step recurrence for `connectionSum`: if `z Q_m = Q_{m+1} + m c₂ Q_{m-1}`, then
`S_n = connectionSum (c₂ - c₁) Q n` satisfies `z S_{n+1} = S_{n+2} + (n + 1) c₁ S_n`. -/
private lemma mul_connectionSum_succ {R : Type*} [CommRing R] {z c₁ c₂ : R} {Q : ℕ → R}
    (hQ : ∀ m, z * Q m = Q (m + 1) + m * c₂ * Q (m - 1)) (n : ℕ) :
    z * connectionSum (c₂ - c₁) Q (n + 1) =
      connectionSum (c₂ - c₁) Q (n + 2) + (n + 1 : ℕ) * c₁ * connectionSum (c₂ - c₁) Q n := by
  set d : R := c₂ - c₁
  have hstep1 := connectionSum_mul_expand d hQ n
  have hstep2 := connectionSum_lower_c₁ c₁ d Q n
  have hstep3 := connectionSum_raise_add_diff d Q n
  have hc₂ : ∀ k, c₂ * d ^ k * Q (n - 2 * k) =
      c₁ * d ^ k * Q (n - 2 * k) + d * d ^ k * Q (n - 2 * k) := fun k => by
    dsimp [d]; ring
  simp_rw [hc₂, mul_add, Finset.sum_add_distrib] at hstep1
  rw [hstep1, hstep2, ← add_assoc, add_right_comm _ ((n + 1 : ℕ) * c₁ * _), hstep3, add_comm]

/-- **Variance-connection identity for three-term recurrences.** In any commutative ring `R`, if
two sequences `P, Q : ℕ → R` agree at `0` (`P 0 = Q 0`) and satisfy
`z * P m = P (m + 1) + m * c₁ * P (m - 1)` and `z * Q m = Q (m + 1) + m * c₂ * Q (m - 1)` for all
`m : ℕ`, then
`P n = ∑_{k=0}^{⌊n/2⌋} (C(n, 2k) (2k - 1)‼) • ((c₂ - c₁)^k * Q_{n - 2k})`. -/
theorem eq_sum_choose_mul_doubleFactorial_smul_of_mul_eq_add {R : Type*} [CommRing R]
    {z c₁ c₂ : R} {P Q : ℕ → R} (h0 : P 0 = Q 0)
    (hP : ∀ m, z * P m = P (m + 1) + m * c₁ * P (m - 1))
    (hQ : ∀ m, z * Q m = Q (m + 1) + m * c₂ * Q (m - 1)) (n : ℕ) :
    P n = ∑ k ∈ Finset.range (n / 2 + 1),
      (n.choose (2 * k) * (2 * k - 1)‼) • ((c₂ - c₁) ^ k * Q (n - 2 * k)) := by
  rw [← connectionSum_eq_sum_div_two]
  induction n using Nat.twoStepInduction with
  | zero =>
    simp [connectionSum, h0]
  | one =>
    have h1 : P 1 = Q 1 := by
      have hP1 := hP 0
      have hQ1 := hQ 0
      simp only [Nat.cast_zero, zero_mul, add_zero] at hP1 hQ1
      rw [← hP1, ← hQ1, h0]
    simp [connectionSum, Finset.sum_range_succ, h1]
  | more n ih0 ih1 =>
    have hP_step := hP (n + 1)
    have hS_step := mul_connectionSum_succ (c₁ := c₁) hQ n
    rw [Nat.add_sub_cancel, ih0, ih1] at hP_step
    exact add_right_cancel (hP_step.symm.trans hS_step)

end TauCeti
