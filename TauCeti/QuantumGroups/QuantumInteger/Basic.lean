/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Field.Defs

import Mathlib.Tactic

/-!
# Quantum integers

This file develops the symmetric quantum integers associated to a generic nonzero parameter
in a field.  Besides the quotient definition, it provides a denominator-free Laurent sum,
the sign and three-term recurrence identities, and the nonvanishing result needed for the
ladder coefficients of generic rank-one quantum-group representations.
-/

public section

open scoped BigOperators

namespace TauCeti

variable {K : Type*} [Field K]

/-- An element of a field is a generic quantum parameter if it is nonzero and none of its
positive natural powers is one. -/
def IsGenericQuantumParameter (q : K) : Prop :=
  q ≠ 0 ∧ ∀ n : ℕ, 0 < n → q ^ n ≠ 1

/-- Characterization of generic quantum parameters: nonzero, with no positive natural power
equal to one. -/
theorem isGenericQuantumParameter_iff {q : K} :
    IsGenericQuantumParameter q ↔ q ≠ 0 ∧ ∀ n : ℕ, 0 < n → q ^ n ≠ 1 :=
  Iff.rfl

namespace IsGenericQuantumParameter

/-- A generic quantum parameter is nonzero. -/
theorem ne_zero {q : K} (hq : IsGenericQuantumParameter q) : q ≠ 0 :=
  hq.1

/-- No positive natural power of a generic quantum parameter is one. -/
theorem pow_ne_one {q : K} (hq : IsGenericQuantumParameter q) {n : ℕ} (hn : 0 < n) :
    q ^ n ≠ 1 :=
  hq.2 n hn

/-- The natural powers of a generic quantum parameter are pairwise distinct. -/
theorem pow_injective {q : K} (hq : IsGenericQuantumParameter q) :
    Function.Injective (q ^ · : ℕ → K) := by
  intro m n h
  wlog hmn : m ≤ n generalizing m n
  · exact (this h.symm (by omega)).symm
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
  dsimp only at h
  rw [pow_add, left_eq_mul₀ (pow_ne_zero _ hq.ne_zero)] at h
  by_contra hd
  exact hq.pow_ne_one (n := d) (by omega) h

/-- The integer powers of a generic quantum parameter are pairwise distinct. -/
theorem zpow_injective {q : K} (hq : IsGenericQuantumParameter q) :
    Function.Injective (q ^ · : ℤ → K) := by
  intro m n h
  wlog hmn : m ≤ n generalizing m n
  · exact (this h.symm (by omega)).symm
  obtain ⟨d, rfl⟩ := Int.le.dest hmn
  have h : q ^ d = 1 := by simpa [zpow_add₀ hq.ne_zero, zpow_ne_zero, hq.ne_zero] using h.symm
  simpa using hq.pow_injective (h.trans (pow_zero q).symm)

/-- At a generic parameter in a field of characteristic not two, a signed power `ε q ^ m` is an
integral power of `q` only for the positive sign. -/
theorem eq_one_of_units_mul_zpow_eq_zpow [NeZero (2 : K)] {q : K}
    (hq : IsGenericQuantumParameter q) {ε : ℤˣ} {m n : ℤ} (h : ((ε : ℤ) : K) * q ^ m = q ^ n) :
    ε = 1 := by
  rcases Int.units_eq_one_or ε with rfl | rfl
  · rfl
  exfalso
  have hsq : q ^ (m * 2) = q ^ (n * 2) := by
    rw [zpow_mul, zpow_mul, ← h, zpow_two, zpow_two]
    push_cast
    ring
  obtain rfl : m = n := by have := hq.zpow_injective hsq; omega
  have : (2 : K) * q ^ m = 0 := by
    push_cast at h
    linear_combination -h
  exact mul_ne_zero two_ne_zero (zpow_ne_zero m hq.ne_zero) this

/-- A generic quantum parameter is not equal to its inverse. -/
theorem ne_inv {q : K} (hq : IsGenericQuantumParameter q) : q ≠ q⁻¹ := by
  intro h
  have hsq : q ^ 2 = 1 := by
    calc
      q ^ 2 = q * q := pow_two q
      _ = q⁻¹ * q := congrArg (· * q) h
      _ = 1 := inv_mul_cancel₀ hq.ne_zero
  exact hq.pow_ne_one (n := 2) (by omega) hsq

/-- The denominator in the symmetric quantum-integer formula is nonzero at a generic
parameter. -/
theorem sub_inv_ne_zero {q : K} (hq : IsGenericQuantumParameter q) : q - q⁻¹ ≠ 0 :=
  sub_ne_zero.mpr hq.ne_inv

/-- The inverse of a generic quantum parameter is generic. -/
theorem inv {q : K} (hq : IsGenericQuantumParameter q) : IsGenericQuantumParameter q⁻¹ := by
  refine ⟨inv_ne_zero hq.ne_zero, fun n hn hpow => ?_⟩
  apply hq.pow_ne_one hn
  simpa [inv_pow] using congrArg Inv.inv hpow

/-- A positive natural power of a generic quantum parameter is generic. -/
theorem pow {q : K} (hq : IsGenericQuantumParameter q) {k : ℕ} (hk : 0 < k) :
    IsGenericQuantumParameter (q ^ k) := by
  refine ⟨pow_ne_zero k hq.ne_zero, fun n hn hpow => ?_⟩
  rw [← pow_mul] at hpow
  exact hq.pow_ne_one (Nat.mul_pos hk hn) hpow

/-- For nonzero `c`, the multiples `q ^ n * c` of a generic quantum parameter `q` are pairwise
distinct. -/
theorem pow_mul_injective {q c : K} (hq : IsGenericQuantumParameter q) (hc : c ≠ 0) :
    Function.Injective fun n : ℕ => q ^ n * c :=
  fun _ _ h => hq.pow_injective (mul_right_cancel₀ hc h)

end IsGenericQuantumParameter

/-- If `q - q⁻¹` is nonzero, then so is `q`. -/
theorem ne_zero_of_sub_inv_ne_zero {q : K} (hq : q - q⁻¹ ≠ 0) : q ≠ 0 := by
  rintro rfl
  simp at hq

/-- The symmetric quantum integer `[r]_q = (q^r - q⁻ʳ) / (q - q⁻¹)`. -/
noncomputable def quantumInteger (q : K) (r : ℤ) : K :=
  (q ^ r - q ^ (-r)) / (q - q⁻¹)

/-- The defining quotient formula for the symmetric quantum integer. -/
theorem quantumInteger_def (q : K) (r : ℤ) :
    quantumInteger q r = (q ^ r - q ^ (-r)) / (q - q⁻¹) := by
  rw [quantumInteger]

/-- `(q - q⁻¹) [n]_q = q^n - q^(-n)` for natural `n`. -/
theorem sub_inv_mul_quantumInteger_natCast {q : K} (hq : q - q⁻¹ ≠ 0) (n : ℕ) :
    (q - q⁻¹) * quantumInteger q n = q ^ n - q⁻¹ ^ n := by
  rw [quantumInteger_def, mul_div_cancel₀ _ hq, zpow_neg, zpow_natCast, inv_pow]

/-- The zeroth quantum integer is zero. -/
@[simp] theorem quantumInteger_zero (q : K) : quantumInteger q 0 = 0 := by
  simp [quantumInteger]

/-- The first quantum integer is one whenever its defining denominator is nonzero. -/
@[simp] theorem quantumInteger_one {q : K} (hq : q - q⁻¹ ≠ 0) :
    quantumInteger q 1 = 1 := by
  simp [quantumInteger, hq]

/-- Negating the index negates the quantum integer. -/
@[simp] theorem quantumInteger_neg (q : K) (r : ℤ) :
    quantumInteger q (-r) = -quantumInteger q r := by
  simp only [quantumInteger, neg_neg]
  ring

/-- Replacing the parameter by its inverse leaves every quantum integer unchanged. -/
@[simp] theorem quantumInteger_inv (q : K) (r : ℤ) :
    quantumInteger q⁻¹ r = quantumInteger q r := by
  simp only [quantumInteger, inv_zpow, inv_inv]
  rw [← zpow_neg q r, ← zpow_neg q (-r)]
  have hinv_sub : q⁻¹ - q = -(q - q⁻¹) := by ring
  rw [hinv_sub, div_neg]
  ring_nf

/-- The first-order recurrence used to obtain the Laurent expansion of positive quantum
integers. -/
theorem quantumInteger_natCast_succ {q : K} (hq : q - q⁻¹ ≠ 0) (n : ℕ) :
    quantumInteger q (n + 1) = q⁻¹ * quantumInteger q n + q ^ n := by
  have hq0 := ne_zero_of_sub_inv_ne_zero hq
  simp only [quantumInteger]
  rw [zpow_add₀ hq0]
  have hneg_succ : -((n : ℤ) + 1) = -(n : ℤ) + -1 := by omega
  rw [hneg_succ, zpow_add₀ hq0]
  simp only [zpow_one, zpow_neg, zpow_natCast]
  rw [div_eq_iff hq]
  rw [add_mul, mul_assoc, div_mul_cancel₀ _ hq]
  field_simp [hq0]
  ring

/-- For a positive index, the quantum integer is a Laurent polynomial with coefficients one:
`[n]_q = q^(1-n) + q^(3-n) + ⋯ + q^(n-1)`. -/
theorem quantumInteger_natCast_eq_sum {q : K} (hq : q - q⁻¹ ≠ 0) (n : ℕ) :
    quantumInteger q n = ∑ j ∈ Finset.range n, q ^ (2 * (j : ℤ) + 1 - (n : ℤ)) := by
  have hq0 := ne_zero_of_sub_inv_ne_zero hq
  have hterm : ∀ j ∈ Finset.range n,
      q ^ (2 * (j : ℤ) + 1 - (n : ℤ)) = q ^ j * q⁻¹ ^ (n - 1 - j) := by
    intro j hj
    have hj : j < n := Finset.mem_range.mp hj
    have hexp : 2 * (j : ℤ) + 1 - (n : ℤ) = (j : ℤ) + -((n - 1 - j : ℕ) : ℤ) := by omega
    simp only [hexp, zpow_add₀ hq0, zpow_neg, zpow_natCast, inv_pow]
  rw [Finset.sum_congr rfl hterm, quantumInteger, div_eq_iff hq, geom_sum₂_mul]
  simp only [zpow_neg, zpow_natCast, inv_pow]

/-- The symmetric quantum integers satisfy the usual three-term recurrence. -/
theorem quantumInteger_add_one (q : K) (r : ℤ) :
    quantumInteger q (r + 1) =
      (q + q⁻¹) * quantumInteger q r - quantumInteger q (r - 1) := by
  by_cases hq : q - q⁻¹ = 0
  · simp [quantumInteger, hq]
  have hq0 := ne_zero_of_sub_inv_ne_zero hq
  simp only [quantumInteger]
  rw [zpow_add₀ hq0, zpow_sub₀ hq0]
  have hneg_add_one : -(r + 1) = -r + -1 := by omega
  rw [hneg_add_one, zpow_add₀ hq0]
  have hneg_sub_one : -(r - 1) = -r - -1 := by omega
  rw [hneg_sub_one, zpow_sub₀ hq0]
  simp only [zpow_one, zpow_neg]
  field_simp [hq0, hq]
  ring

/-- The addition formula `[a + b]_q = q^a [b]_q + q^(-b) [a]_q`. -/
theorem quantumInteger_add (q : K) (a b : ℤ) :
    quantumInteger q (a + b) = q ^ a * quantumInteger q b + q ^ (-b) * quantumInteger q a := by
  by_cases hq : q - q⁻¹ = 0
  · simp [quantumInteger, hq]
  have hq0 := ne_zero_of_sub_inv_ne_zero hq
  simp only [quantumInteger, neg_add, zpow_add₀ hq0]
  field_simp
  ring

/-- The difference of two quantum integers as a determinant of neighbouring quantum integers:
`[a - b]_q = [a]_q [b + 1]_q - [a + 1]_q [b]_q`. -/
theorem quantumInteger_sub (q : K) (a b : ℤ) :
    quantumInteger q (a - b) =
      quantumInteger q a * quantumInteger q (b + 1) -
        quantumInteger q (a + 1) * quantumInteger q b := by
  by_cases hq : q - q⁻¹ = 0
  · simp [quantumInteger, hq]
  have hq0 := ne_zero_of_sub_inv_ne_zero hq
  have h2 : q ^ 2 - 1 ≠ 0 := by
    intro h
    apply hq
    field_simp
    linear_combination h
  simp only [quantumInteger, zpow_sub₀ hq0, zpow_add₀ hq0, zpow_neg, neg_add, zpow_one]
  field_simp
  ring

/-- Every nonzero-index quantum integer is nonzero at a generic parameter. -/
theorem quantumInteger_ne_zero {q : K} (hq : IsGenericQuantumParameter q) {r : ℤ}
    (hr : r ≠ 0) : quantumInteger q r ≠ 0 := by
  rw [quantumInteger, div_ne_zero_iff]
  refine ⟨fun h => ?_, hq.sub_inv_ne_zero⟩
  have hfin : ¬IsOfFinOrder q := by
    rw [isOfFinOrder_iff_pow_eq_one]
    rintro ⟨n, hn, hpow⟩
    exact hq.pow_ne_one hn hpow
  refine hfin (isOfFinOrder_iff_zpow_eq_one.mpr ⟨r - -r, by omega, ?_⟩)
  rw [zpow_sub₀ hq.ne_zero, sub_eq_zero.mp h, div_self (zpow_ne_zero _ hq.ne_zero)]

end TauCeti
