/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Ring.Hom.Defs

import Mathlib.Tactic

/-!
# Quantum integers

This file develops the symmetric quantum integers associated to a generic nonzero parameter
in a field.  Besides the quotient definition, it provides a denominator-free Laurent sum,
the sign and three-term recurrence identities, and the nonvanishing result needed for the
ladder coefficients of generic rank-one quantum-group representations.

The predicate `TauCeti.IsGenericQuantumParameter` (nonzero and not a root of unity) is defined in
any monoid with zero, and each of its lemmas assumes only the cancellation, inverses or
subtraction that it needs.
-/

public section

open scoped BigOperators

namespace TauCeti

section MonoidWithZero

variable {M₀ : Type*} [MonoidWithZero M₀]

/-- An element of a monoid with zero is a generic quantum parameter if it is nonzero and none of
its positive natural powers is one. -/
def IsGenericQuantumParameter (q : M₀) : Prop :=
  q ≠ 0 ∧ ∀ n : ℕ, 0 < n → q ^ n ≠ 1

/-- Characterization of generic quantum parameters: nonzero, with no positive natural power
equal to one. -/
theorem isGenericQuantumParameter_iff {q : M₀} :
    IsGenericQuantumParameter q ↔ q ≠ 0 ∧ ∀ n : ℕ, 0 < n → q ^ n ≠ 1 :=
  Iff.rfl

namespace IsGenericQuantumParameter

/-- A generic quantum parameter is nonzero. -/
theorem ne_zero {q : M₀} (hq : IsGenericQuantumParameter q) : q ≠ 0 :=
  hq.1

/-- No positive natural power of a generic quantum parameter is one. -/
theorem pow_ne_one {q : M₀} (hq : IsGenericQuantumParameter q) {n : ℕ} (hn : 0 < n) :
    q ^ n ≠ 1 :=
  hq.2 n hn

/-- A positive natural power of a generic quantum parameter is generic. -/
theorem pow [NoZeroDivisors M₀] {q : M₀} (hq : IsGenericQuantumParameter q) {k : ℕ}
    (hk : 0 < k) : IsGenericQuantumParameter (q ^ k) := by
  refine ⟨pow_ne_zero k hq.ne_zero, fun n hn hpow => ?_⟩
  rw [← pow_mul] at hpow
  exact hq.pow_ne_one (Nat.mul_pos hk hn) hpow

/-- The natural powers of a generic quantum parameter are pairwise distinct. -/
theorem pow_injective [IsRightCancelMulZero M₀] {q : M₀} (hq : IsGenericQuantumParameter q) :
    Function.Injective (q ^ · : ℕ → M₀) := by
  intro m n h
  wlog hmn : m ≤ n generalizing m n
  · exact (this h.symm (by omega)).symm
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le' hmn
  dsimp only at h
  rw [pow_add, right_eq_mul₀ (pow_ne_zero _ hq.ne_zero)] at h
  by_contra hd
  exact hq.pow_ne_one (n := d) (by omega) h

/-- For nonzero `c`, the multiples `q ^ n * c` of a generic quantum parameter `q` are pairwise
distinct. -/
theorem pow_mul_injective [IsRightCancelMulZero M₀] {q c : M₀} (hq : IsGenericQuantumParameter q)
    (hc : c ≠ 0) : Function.Injective fun n : ℕ => q ^ n * c :=
  fun _ _ h => hq.pow_injective (mul_right_cancel₀ hc h)

end IsGenericQuantumParameter

end MonoidWithZero

section GroupWithZero

variable {G₀ : Type*} [GroupWithZero G₀]

namespace IsGenericQuantumParameter

/-- The integer powers of a generic quantum parameter are pairwise distinct. -/
theorem zpow_injective {q : G₀} (hq : IsGenericQuantumParameter q) :
    Function.Injective (q ^ · : ℤ → G₀) := by
  intro m n h
  wlog hmn : m ≤ n generalizing m n
  · exact (this h.symm (by omega)).symm
  obtain ⟨d, rfl⟩ := Int.le.dest hmn
  have h : q ^ d = 1 := by simpa [zpow_add₀ hq.ne_zero, zpow_ne_zero, hq.ne_zero] using h.symm
  simpa using hq.pow_injective (h.trans (pow_zero q).symm)

/-- A generic quantum parameter is not equal to its inverse. -/
theorem ne_inv {q : G₀} (hq : IsGenericQuantumParameter q) : q ≠ q⁻¹ := fun h =>
  hq.pow_ne_one two_pos (by rwa [sq, mul_eq_one_iff_eq_inv₀ hq.ne_zero])

/-- The inverse of a generic quantum parameter is generic. -/
theorem inv {q : G₀} (hq : IsGenericQuantumParameter q) : IsGenericQuantumParameter q⁻¹ := by
  refine ⟨inv_ne_zero hq.ne_zero, fun n hn hpow => ?_⟩
  apply hq.pow_ne_one hn
  simpa [inv_pow] using congrArg Inv.inv hpow

end IsGenericQuantumParameter

end GroupWithZero

section DivisionRing

variable {K : Type*} [DivisionRing K]

/-- Since `ε = ±1`, the inverse of a signed power `ε q ^ k` is `ε q ^ (-k)`. -/
theorem units_mul_zpow_inv (q : K) (ε : ℤˣ) (k : ℤ) :
    (((ε : ℤ) : K) * q ^ k)⁻¹ = ((ε : ℤ) : K) * q ^ (-k) := by
  rcases Int.units_eq_one_or ε with rfl | rfl <;> simp [zpow_neg]

namespace IsGenericQuantumParameter

/-- At a generic parameter in a division ring of characteristic not two, a signed power
`ε q ^ m` is an integral power of `q` only for the positive sign. -/
theorem eq_one_of_units_mul_zpow_eq_zpow [NeZero (2 : K)] {q : K}
    (hq : IsGenericQuantumParameter q) {ε : ℤˣ} {m n : ℤ} (h : ((ε : ℤ) : K) * q ^ m = q ^ n) :
    ε = 1 := by
  rcases Int.units_eq_one_or ε with rfl | rfl
  · rfl
  exfalso
  simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_one_mul] at h
  have hsq : q ^ (m * 2) = q ^ (n * 2) := by
    rw [zpow_mul, zpow_mul, ← h, even_two.neg_zpow]
  obtain rfl : m = n := by have := hq.zpow_injective hsq; omega
  have : (2 : K) * q ^ m = 0 := by
    rw [two_mul, ← neg_eq_iff_add_eq_zero, h]
  exact mul_ne_zero two_ne_zero (zpow_ne_zero m hq.ne_zero) this

/-- At a generic parameter in a division ring of characteristic not two, a signed power
`ε q ^ m` determines both the sign `ε` and the exponent `m`. -/
theorem units_mul_zpow_inj [NeZero (2 : K)] {q : K} (hq : IsGenericQuantumParameter q)
    {ε δ : ℤˣ} {m n : ℤ} :
    ((ε : ℤ) : K) * q ^ m = ((δ : ℤ) : K) * q ^ n ↔ ε = δ ∧ m = n := by
  refine ⟨fun h => ?_, by rintro ⟨rfl, rfl⟩; rfl⟩
  -- Moving `δ` across gives `(δ ε) q ^ m = q ^ n`, which forces the sign `δ ε` to be one.
  have hδε : δ * ε = 1 := hq.eq_one_of_units_mul_zpow_eq_zpow (m := m) (n := n) <| by
    rw [Units.val_mul, Int.cast_mul, mul_assoc, h, ← mul_assoc, ← Int.cast_mul, ← Units.val_mul,
      Int.units_mul_self, Units.val_one, Int.cast_one, one_mul]
  obtain rfl : ε = δ := by
    rw [← mul_right_inj δ, hδε, Int.units_mul_self]
  refine ⟨rfl, hq.zpow_injective (mul_left_cancel₀ ?_ h)⟩
  rcases Int.units_eq_one_or ε with rfl | rfl <;> simp

/-- The denominator in the symmetric quantum-integer formula is nonzero at a generic
parameter. -/
theorem sub_inv_ne_zero {q : K} (hq : IsGenericQuantumParameter q) : q - q⁻¹ ≠ 0 :=
  sub_ne_zero.mpr hq.ne_inv

end IsGenericQuantumParameter

/-- If `q - q⁻¹` is nonzero, then so is `q`. -/
theorem ne_zero_of_sub_inv_ne_zero {q : K} (hq : q - q⁻¹ ≠ 0) : q ≠ 0 := by
  rintro rfl
  simp at hq

end DivisionRing

variable {K : Type*} [Field K]

/-- The symmetric quantum integer `[r]_q = (q^r - q⁻ʳ) / (q - q⁻¹)`. -/
noncomputable def quantumInteger (q : K) (r : ℤ) : K :=
  (q ^ r - q ^ (-r)) / (q - q⁻¹)

/-- The defining quotient formula for the symmetric quantum integer. -/
theorem quantumInteger_def (q : K) (r : ℤ) :
    quantumInteger q r = (q ^ r - q ^ (-r)) / (q - q⁻¹) := by
  rw [quantumInteger]

/-- `(q - q⁻¹) [n]_q = q^n - q^(-n)` for natural `n`. -/
theorem sub_inv_mul_quantumInteger_natCast (q : K) (n : ℕ) :
    (q - q⁻¹) * quantumInteger q n = q ^ n - q⁻¹ ^ n := by
  by_cases hq : q - q⁻¹ = 0
  · rw [hq, zero_mul]
    exact (sub_eq_zero.mpr (congrArg (· ^ n) (sub_eq_zero.mp hq))).symm
  · rw [quantumInteger_def, mul_div_cancel₀ _ hq, zpow_neg, zpow_natCast, inv_pow]

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
  simp only [quantumInteger_def, inv_zpow', inv_inv, neg_neg]
  rw [← neg_sub q, div_neg, ← neg_div, neg_sub]

/-- The addition formula `[a + b]_q = q^a [b]_q + q^(-b) [a]_q`. -/
theorem quantumInteger_add (q : K) (a b : ℤ) :
    quantumInteger q (a + b) = q ^ a * quantumInteger q b + q ^ (-b) * quantumInteger q a := by
  by_cases hq : q - q⁻¹ = 0
  · simp [quantumInteger, hq]
  have hq0 := ne_zero_of_sub_inv_ne_zero hq
  simp only [quantumInteger, neg_add, zpow_add₀ hq0]
  field_simp
  ring

/-- The first-order recurrence used to obtain the Laurent expansion of positive quantum
integers. -/
theorem quantumInteger_natCast_succ {q : K} (hq : q - q⁻¹ ≠ 0) (n : ℕ) :
    quantumInteger q (n + 1) = q⁻¹ * quantumInteger q n + q ^ n := by
  rw [quantumInteger_add, quantumInteger_one hq, zpow_neg_one, zpow_natCast, mul_one, add_comm]

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

/-- The geometric sum `∑_(i ≤ n) q^(2i)` is `q^n [n + 1]_q`. -/
theorem sum_range_pow_two_mul_eq_pow_mul_quantumInteger {q : K} (hq : q - q⁻¹ ≠ 0) (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), q ^ (2 * i) = q ^ n * quantumInteger q ((n : ℤ) + 1) := by
  have hq0 := ne_zero_of_sub_inv_ne_zero hq
  have h := quantumInteger_natCast_eq_sum hq (n + 1)
  push_cast at h
  rw [h, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hq0]
  congr 1
  push_cast
  ring

/-- The symmetric quantum integers satisfy the usual three-term recurrence. -/
theorem quantumInteger_add_one (q : K) (r : ℤ) :
    quantumInteger q (r + 1) =
      (q + q⁻¹) * quantumInteger q r - quantumInteger q (r - 1) := by
  -- Add the addition formula at `b = 1` and at `b = -1`; the `q ^ r [1]_q` terms cancel.
  have h₁ := quantumInteger_add q r 1
  have h₂ := quantumInteger_add q r (-1)
  rw [quantumInteger_neg, ← sub_eq_add_neg, neg_neg, zpow_one] at h₂
  rw [zpow_neg_one] at h₁
  linear_combination h₁ + h₂

/-- The difference of two quantum integers as a determinant of neighbouring quantum integers:
`[a - b]_q = [a]_q [b + 1]_q - [a + 1]_q [b]_q`. -/
theorem quantumInteger_sub (q : K) (a b : ℤ) :
    quantumInteger q (a - b) =
      quantumInteger q a * quantumInteger q (b + 1) -
        quantumInteger q (a + 1) * quantumInteger q b := by
  by_cases hq : q - q⁻¹ = 0
  · simp [quantumInteger, hq]
  have hq0 := ne_zero_of_sub_inv_ne_zero hq
  -- `field_simp` uses this to clear the denominators `q ^ 2 - 1` left by `q - q⁻¹`.
  have h2 : q ^ 2 - 1 ≠ 0 := by
    intro h
    apply hq
    field_simp
    linear_combination h
  simp only [quantumInteger, zpow_sub₀ hq0, zpow_add₀ hq0, zpow_neg, neg_add, zpow_one]
  field_simp
  ring

/-- For `q ≠ 0`, the quantum integer `[r]_q` vanishes exactly when `q^(2r) = 1`. When
`q - q⁻¹ = 0`, that is `q = ±1`, both sides hold: `[r]_q = 0` by the field convention. -/
theorem quantumInteger_eq_zero_iff {q : K} (hq : q ≠ 0) (r : ℤ) :
    quantumInteger q r = 0 ↔ q ^ (2 * r) = 1 := by
  by_cases hd : q - q⁻¹ = 0
  · -- Here `q² = 1`, so both sides hold.
    have hsq : q ^ 2 = 1 := by
      field_simp at hd
      linear_combination hd
    simp [quantumInteger_def, hd, zpow_mul, hsq]
  have := zpow_ne_zero r hq
  rw [quantumInteger_def, div_eq_zero_iff, or_iff_left hd, sub_eq_zero, two_mul, zpow_add₀ hq,
    zpow_neg]
  constructor <;> intro h <;> field_simp at h ⊢ <;> linear_combination h

/-- Every nonzero-index quantum integer is nonzero at a generic parameter. -/
theorem quantumInteger_ne_zero {q : K} (hq : IsGenericQuantumParameter q) {r : ℤ}
    (hr : r ≠ 0) : quantumInteger q r ≠ 0 := by
  rw [ne_eq, quantumInteger_eq_zero_iff hq.ne_zero]
  exact fun h => hr (by have := hq.zpow_injective (h.trans (zpow_zero q).symm); omega)

section Map

variable {L F : Type*} [Field L] [FunLike F K L] [RingHomClass F K L]

/-- Ring homomorphisms between fields commute with the quantum integers. -/
@[simp]
theorem map_quantumInteger (φ : F) (q : K) (r : ℤ) :
    φ (quantumInteger q r) = quantumInteger (φ q) r := by
  simp [quantumInteger_def]

end Map

end TauCeti
