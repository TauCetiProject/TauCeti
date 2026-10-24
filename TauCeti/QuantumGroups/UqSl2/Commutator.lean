/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.QuantumGroups.QuantumInteger.Basic
public import TauCeti.QuantumGroups.UqSl2.Basic

import Mathlib.Tactic

/-!
# Commuting powers in `U_q(sl₂)`

This file gives the closed formula for commuting the raising generator `E` past a power of the
lowering generator `F`.  It is the calculation that detects the highest weight of a finite
lowering string, and is also used in the finite-dimensional complete-reducibility argument.
We also record a parameter-free form, valid even at `q = ±1`, that only remembers that the
correction term is `F ^ n` times a combination of `K` and `K⁻¹`.

The convention follows A. Virelizier, *Quantum groups*, Section 2.4.
-/

public section

namespace TauCeti.UqSl2

variable {q : ℂ}

/-- Commuting `K` past a natural power of `F`. -/
theorem k_mul_f_pow (r : ℕ) :
    k q * f q ^ r = (q⁻¹ ^ 2) ^ r • (f q ^ r * k q) := by
  have h : SemiconjBy (k q) (f q) (q⁻¹ ^ 2 • f q) := by
    rw [SemiconjBy, k_mul_f, smul_mul_assoc]
  rw [(h.pow_right r).eq, smul_pow, smul_mul_assoc]

/-- Commuting `K⁻¹` past a natural power of `F`. -/
theorem kInv_mul_f_pow (r : ℕ) :
    kInv q * f q ^ r = (q ^ 2) ^ r • (f q ^ r * kInv q) := by
  have h : SemiconjBy (kInv q) (f q) (q ^ 2 • f q) := by
    rw [SemiconjBy, kInv_mul_f, smul_mul_assoc]
  rw [(h.pow_right r).eq, smul_pow, smul_mul_assoc]

/-- The commutator formula for `E` and a natural power of `F`:
`E F^r = F^r E + [r]_q F^(r-1) (q^(1-r) K - q^(r-1) K⁻¹) / (q-q⁻¹)`. -/
theorem e_mul_f_pow (hq : q - q⁻¹ ≠ 0) (r : ℕ) :
    e q * f q ^ r = f q ^ r * e q +
      (quantumInteger q r * (q - q⁻¹)⁻¹) • (f q ^ (r - 1) *
        (q⁻¹ ^ (r - 1) • k q - q ^ (r - 1) • kInv q)) := by
  induction r with
  | zero => simp
  | succ r ih =>
    -- The first nontrivial power is precisely the defining commutator relation.
    have hef : e q * f q = f q * e q + (q - q⁻¹)⁻¹ • (k q - kInv q) :=
      eq_add_of_sub_eq' e_mul_f_sub_f_mul_e
    rcases r with _ | r
    · simpa [quantumInteger_one hq] using hef
    have hq0 := ne_zero_of_sub_inv_ne_zero hq
    have hf (n : ℕ) (x : UqSl2 q) : f q ^ n * (f q * x) = f q ^ (n + 1) * x := by
      rw [← mul_assoc, ← pow_succ]
    -- The `K` and `K⁻¹` coefficients are two forms of the quantum-integer recurrence.
    have hk : (q - q⁻¹)⁻¹ + quantumInteger q (r + 1) * (q - q⁻¹)⁻¹ * q⁻¹ ^ 2 * q⁻¹ ^ r =
        quantumInteger q (r + 1 + 1) * (q - q⁻¹)⁻¹ * q⁻¹ ^ (r + 1) := by
      have h := quantumInteger_natCast_succ hq (r + 1)
      push_cast at h
      rw [h]
      simp only [inv_pow]
      field_simp
      ring
    have hkInv : (q - q⁻¹)⁻¹ + quantumInteger q (r + 1) * (q - q⁻¹)⁻¹ * q ^ 2 * q ^ r =
        quantumInteger q (r + 1 + 1) * (q - q⁻¹)⁻¹ * q ^ (r + 1) := by
      have h := quantumInteger_natCast_succ (q := q⁻¹) (by rwa [inv_inv, ← neg_sub, neg_ne_zero])
        (r + 1)
      push_cast [quantumInteger_inv, inv_inv] at h
      rw [h]
      simp only [inv_pow]
      field_simp
      ring
    rw [pow_succ, ← mul_assoc, ih]
    simp only [Nat.add_sub_cancel, add_mul, sub_mul, mul_add, mul_sub, smul_mul_assoc,
      mul_smul_comm, mul_assoc, hef, k_mul_f, kInv_mul_f, smul_sub, smul_smul, hf]
    push_cast
    linear_combination (norm := module)
      hk • (f q ^ (r + 1) * k q) - hkInv • (f q ^ (r + 1) * kInv q)

/-- Commuting `E` past a positive power of `F` leaves a correction `F ^ n (α K + β K⁻¹)`.
Unlike `e_mul_f_pow`, this holds for every `q`, including `q = ±1`. -/
theorem exists_e_mul_f_pow_succ (n : ℕ) : ∃ α β : ℂ,
    e q * f q ^ (n + 1) = f q ^ (n + 1) * e q + f q ^ n * (α • k q + β • kInv q) := by
  rcases eq_or_ne (q - q⁻¹) 0 with hq | hq
  · -- At `q = ±1` the defining relation makes `E` and `F` commute.
    have hef : Commute (e q) (f q) := by
      have := e_mul_f_sub_f_mul_e (q := q)
      rw [hq, inv_zero, zero_smul, sub_eq_zero] at this
      exact this
    exact ⟨0, 0, by simp [(hef.pow_right (n + 1)).eq]⟩
  · refine ⟨quantumInteger q (n + 1) * (q - q⁻¹)⁻¹ * q⁻¹ ^ n,
      -(quantumInteger q (n + 1) * (q - q⁻¹)⁻¹ * q ^ n), ?_⟩
    rw [e_mul_f_pow hq, Nat.add_sub_cancel]
    simp only [mul_add, mul_sub, mul_smul_comm, smul_sub, smul_smul, neg_smul, mul_neg,
      Nat.cast_add, Nat.cast_one]
    abel

end TauCeti.UqSl2
