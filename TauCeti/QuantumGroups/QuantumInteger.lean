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

end IsGenericQuantumParameter

/-- The symmetric quantum integer `[r]_q = (q^r - q⁻ʳ) / (q - q⁻¹)`. -/
noncomputable def quantumInteger (q : K) (r : ℤ) : K :=
  (q ^ r - q ^ (-r)) / (q - q⁻¹)

/-- The defining quotient formula for the symmetric quantum integer. -/
theorem quantumInteger_def (q : K) (r : ℤ) :
    quantumInteger q r = (q ^ r - q ^ (-r)) / (q - q⁻¹) := by
  rw [quantumInteger]

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
  have hq0 : q ≠ 0 := by
    intro h
    subst q
    simp at hq
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
  have hq0 : q ≠ 0 := by
    intro h
    subst q
    simp at hq
  rw [quantumInteger, div_eq_iff hq, zpow_neg, zpow_natCast, ← inv_pow, ← geom_sum₂_mul]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj : j < n := Finset.mem_range.mp hj
  rw [inv_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_neg, ← zpow_add₀ hq0]
  congr 1
  omega

/-- The symmetric quantum integers satisfy the usual three-term recurrence. -/
theorem quantumInteger_add_one (q : K) (r : ℤ) :
    quantumInteger q (r + 1) =
      (q + q⁻¹) * quantumInteger q r - quantumInteger q (r - 1) := by
  by_cases hq : q - q⁻¹ = 0
  · simp [quantumInteger, hq]
  have hq0 : q ≠ 0 := by
    intro h
    subst q
    simp at hq
  simp only [quantumInteger]
  rw [zpow_add₀ hq0, zpow_sub₀ hq0]
  have hneg_add_one : -(r + 1) = -r + -1 := by omega
  rw [hneg_add_one, zpow_add₀ hq0]
  have hneg_sub_one : -(r - 1) = -r - -1 := by omega
  rw [hneg_sub_one, zpow_sub₀ hq0]
  simp only [zpow_one, zpow_neg]
  field_simp [hq0, hq]
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
