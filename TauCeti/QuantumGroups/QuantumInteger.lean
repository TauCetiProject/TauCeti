/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Complex.Basic

import Mathlib.Tactic

/-!
# Quantum integers

This file develops the symmetric quantum integers associated to a generic nonzero complex
parameter.  Besides the quotient definition, it provides a denominator-free Laurent sum,
the sign and three-term recurrence identities, and the nonvanishing result needed for the
ladder coefficients of generic rank-one quantum-group representations.
-/

public section

open scoped BigOperators

namespace TauCeti

/-- A complex number is a generic quantum parameter if it is nonzero and none of its positive
natural powers is one. -/
def IsGenericQuantumParameter (q : ℂ) : Prop :=
  q ≠ 0 ∧ ∀ n : ℕ, 0 < n → q ^ n ≠ 1

namespace IsGenericQuantumParameter

/-- A generic quantum parameter is nonzero. -/
theorem ne_zero {q : ℂ} (hq : IsGenericQuantumParameter q) : q ≠ 0 :=
  hq.1

/-- No positive natural power of a generic quantum parameter is one. -/
theorem pow_ne_one {q : ℂ} (hq : IsGenericQuantumParameter q) {n : ℕ} (hn : 0 < n) :
    q ^ n ≠ 1 :=
  hq.2 n hn

/-- A generic quantum parameter is not equal to its inverse. -/
theorem ne_inv {q : ℂ} (hq : IsGenericQuantumParameter q) : q ≠ q⁻¹ := by
  intro h
  have hsq : q ^ 2 = 1 := by
    calc
      q ^ 2 = q * q := pow_two q
      _ = q⁻¹ * q := congrArg (· * q) h
      _ = 1 := inv_mul_cancel₀ hq.ne_zero
  exact hq.pow_ne_one (n := 2) (by omega) hsq

/-- The denominator in the symmetric quantum-integer formula is nonzero at a generic
parameter. -/
theorem sub_inv_ne_zero {q : ℂ} (hq : IsGenericQuantumParameter q) : q - q⁻¹ ≠ 0 :=
  sub_ne_zero.mpr hq.ne_inv

end IsGenericQuantumParameter

/-- The symmetric quantum integer `[r]_q = (q^r - q⁻ʳ) / (q - q⁻¹)`. -/
noncomputable def quantumInteger (q : ℂ) (r : ℤ) : ℂ :=
  (q ^ r - q ^ (-r)) / (q - q⁻¹)

/-- The zeroth quantum integer is zero. -/
@[simp] theorem quantumInteger_zero (q : ℂ) : quantumInteger q 0 = 0 := by
  simp [quantumInteger]

/-- The first quantum integer is one whenever its defining denominator is nonzero. -/
@[simp] theorem quantumInteger_one {q : ℂ} (hq : q - q⁻¹ ≠ 0) :
    quantumInteger q 1 = 1 := by
  simp [quantumInteger, hq]

/-- Negating the index negates the quantum integer. -/
@[simp] theorem quantumInteger_neg (q : ℂ) (r : ℤ) :
    quantumInteger q (-r) = -quantumInteger q r := by
  simp only [quantumInteger, neg_neg]
  ring

/-- Replacing the parameter by its inverse leaves every quantum integer unchanged. -/
@[simp] theorem quantumInteger_inv (q : ℂ) (r : ℤ) :
    quantumInteger q⁻¹ r = quantumInteger q r := by
  simp only [quantumInteger, inv_zpow, inv_inv]
  rw [← zpow_neg q r, ← zpow_neg q (-r)]
  rw [show q⁻¹ - q = -(q - q⁻¹) by ring, div_neg]
  ring_nf

/-- The first-order recurrence used to obtain the Laurent expansion of positive quantum
integers. -/
theorem quantumInteger_natCast_succ {q : ℂ} (hq : q - q⁻¹ ≠ 0) (n : ℕ) :
    quantumInteger q (n + 1) = q⁻¹ * quantumInteger q n + q ^ n := by
  have hq0 : q ≠ 0 := by
    intro h
    subst q
    simp at hq
  simp only [quantumInteger]
  rw [zpow_add₀ hq0]
  rw [show (-((n : ℤ) + 1)) = -(n : ℤ) + -1 by omega, zpow_add₀ hq0]
  simp only [zpow_one, zpow_neg, zpow_natCast]
  rw [div_eq_iff hq]
  rw [add_mul, mul_assoc, div_mul_cancel₀ _ hq]
  field_simp [hq0]
  ring

/-- For a positive index, the quantum integer is a Laurent polynomial with coefficients one:
`[n]_q = q^(1-n) + q^(3-n) + ⋯ + q^(n-1)`. -/
theorem quantumInteger_natCast_eq_sum {q : ℂ} (hq : q - q⁻¹ ≠ 0) (n : ℕ) :
    quantumInteger q n = ∑ j ∈ Finset.range n, q ^ (2 * (j : ℤ) + 1 - (n : ℤ)) := by
  have hq0 : q ≠ 0 := by
    intro h
    subst q
    simp at hq
  induction n with
  | zero => simp
  | succ n ih =>
      rw [show ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 by omega,
        quantumInteger_natCast_succ hq, Finset.sum_range_succ, ih]
      rw [Finset.mul_sum]
      congr 1
      · apply Finset.sum_congr rfl
        intro j hj
        calc
          q⁻¹ * q ^ (2 * (j : ℤ) + 1 - (n : ℤ)) =
              q ^ (-1 : ℤ) * q ^ (2 * (j : ℤ) + 1 - (n : ℤ)) := by
                rw [zpow_neg_one]
          _ = q ^ ((-1 : ℤ) + (2 * (j : ℤ) + 1 - (n : ℤ))) := by
                rw [zpow_add₀ hq0]
          _ = q ^ (2 * (j : ℤ) + 1 - ((n : ℤ) + 1)) := by
                congr 1
                omega
      · rw [← zpow_natCast]
        congr 1
        omega

/-- The symmetric quantum integers satisfy the usual three-term recurrence. -/
theorem quantumInteger_add_one {q : ℂ} (hq : q - q⁻¹ ≠ 0) (r : ℤ) :
    quantumInteger q (r + 1) =
      (q + q⁻¹) * quantumInteger q r - quantumInteger q (r - 1) := by
  have hq0 : q ≠ 0 := by
    intro h
    subst q
    simp at hq
  simp only [quantumInteger]
  rw [zpow_add₀ hq0, zpow_sub₀ hq0]
  rw [show (-(r + 1)) = -r + -1 by omega, zpow_add₀ hq0]
  rw [show (-(r - 1)) = -r - -1 by omega, zpow_sub₀ hq0]
  simp only [zpow_one, zpow_neg]
  field_simp [hq0, hq]
  ring

/-- Every nonzero-index quantum integer is nonzero at a generic parameter. -/
theorem quantumInteger_ne_zero {q : ℂ} (hq : IsGenericQuantumParameter q) {r : ℤ}
    (hr : r ≠ 0) : quantumInteger q r ≠ 0 := by
  rw [quantumInteger, div_ne_zero_iff]
  refine ⟨?_, hq.sub_inv_ne_zero⟩
  intro h
  have hpowers : q ^ r = q ^ (-r) := sub_eq_zero.mp h
  have hroot : q ^ (2 * r.natAbs) = 1 := by
    have habs : (r.natAbs : ℤ) = r ∨ (r.natAbs : ℤ) = -r := by
      omega
    rcases habs with habs | habs
    · rw [← habs] at hpowers
      simp only [zpow_natCast, zpow_neg] at hpowers
      calc
        q ^ (2 * r.natAbs) = (q ^ r.natAbs) ^ 2 := pow_mul' q 2 r.natAbs
        _ = (q ^ r.natAbs)⁻¹ * q ^ r.natAbs := by
          rw [pow_two]
          exact congrArg (· * q ^ r.natAbs) hpowers
        _ = 1 := inv_mul_cancel₀ (pow_ne_zero _ hq.ne_zero)
    · have hr : r = -(r.natAbs : ℤ) := by omega
      rw [hr] at hpowers
      simp only [neg_neg, zpow_natCast, zpow_neg] at hpowers
      calc
        q ^ (2 * r.natAbs) = (q ^ r.natAbs) ^ 2 := pow_mul' q 2 r.natAbs
        _ = (q ^ r.natAbs)⁻¹ * q ^ r.natAbs := by
          rw [pow_two]
          exact congrArg (· * q ^ r.natAbs) hpowers.symm
        _ = 1 := inv_mul_cancel₀ (pow_ne_zero _ hq.ne_zero)
  exact hq.pow_ne_one (n := 2 * r.natAbs) (by positivity) hroot

end TauCeti
