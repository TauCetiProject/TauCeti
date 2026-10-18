/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.QuantumGroups.QuantumInteger
public import TauCeti.QuantumGroups.UqSl2.Basic

import Mathlib.Tactic

/-!
# Commuting powers in `U_q(sl₂)`

This file gives the closed formula for commuting the raising generator `E` past a power of the
lowering generator `F`.  It is the calculation that detects the highest weight of a finite
lowering string, and is also used in the finite-dimensional complete-reducibility argument.

The convention follows A. Virelizier, *Quantum groups*, Section 2.4.
-/

public section

namespace TauCeti.UqSl2

variable {q : ℂ}

/-- Commuting `K` past a natural power of `F`. -/
theorem k_mul_f_pow (r : ℕ) :
    k q * f q ^ r = (q⁻¹ ^ 2) ^ r • (f q ^ r * k q) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ, ← mul_assoc, ih, smul_mul_assoc, mul_assoc (f q ^ r), k_mul_f,
      mul_smul_comm, smul_smul, pow_succ]
    congr 1
    rw [mul_assoc]

/-- Commuting `K⁻¹` past a natural power of `F`. -/
theorem kInv_mul_f_pow (r : ℕ) :
    kInv q * f q ^ r = (q ^ 2) ^ r • (f q ^ r * kInv q) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ, ← mul_assoc, ih, smul_mul_assoc, mul_assoc (f q ^ r), kInv_mul_f,
      mul_smul_comm, smul_smul, pow_succ]
    congr 1
    rw [mul_assoc]

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
    have hef : e q * f q = f q * e q + (q - q⁻¹)⁻¹ • (k q - kInv q) := by
      exact eq_add_of_sub_eq' e_mul_f_sub_f_mul_e
    rcases r with _ | r
    · simpa [quantumInteger_one hq] using hef
    rw [pow_succ, ← mul_assoc, ih, add_mul, mul_assoc (f q ^ (r + 1)),
      hef, mul_add, ← pow_succ]
    simp only [add_assoc]
    rw [← mul_assoc (f q ^ (r + 1)) (f q) (e q), ← pow_succ]
    congr 1
    -- Commute the two weight generators through the final `F`, leaving only scalar identities.
    rw [smul_mul_assoc, mul_assoc (f q ^ (r + 1 - 1)), sub_mul, smul_mul_assoc,
      smul_mul_assoc, k_mul_f, kInv_mul_f, smul_smul, smul_smul,
      mul_sub]
    simp_rw [mul_smul_comm]
    rw [← mul_assoc (f q ^ (r + 1 - 1)), ← mul_assoc (f q ^ (r + 1 - 1)), ← pow_succ]
    simp only [Nat.succ_sub_one, Nat.cast_succ]
    simp only [mul_sub, smul_sub, smul_smul]
    simp_rw [mul_smul_comm]
    rw [show r + (1 + 1) - 1 = r + 1 by omega]
    simp only [smul_smul]
    have hq0 : q ≠ 0 := fun h => by subst q; simp at hq
    -- The two scalar identities are the two inverse-parameter forms of the quantum-integer
    -- recurrence.  They give the `K` and `K⁻¹` coefficients separately.
    have hrec : quantumInteger q (r + 2) =
        q⁻¹ * quantumInteger q (r + 1) + q ^ (r + 1) := by
      convert quantumInteger_natCast_succ hq (r + 1) using 1 <;> norm_num
      congr 1
    have hqInv : q⁻¹ - (q⁻¹)⁻¹ ≠ 0 := by simpa [inv_inv] using neg_ne_zero.mpr hq
    have hrecInv : quantumInteger q⁻¹ (r + 2) =
        q * quantumInteger q⁻¹ (r + 1) + q⁻¹ ^ (r + 1) := by
      convert quantumInteger_natCast_succ hqInv (r + 1) using 1 <;> norm_num
      congr 1
    simp only [quantumInteger_inv] at hrecInv
    have hpow : q ^ r * q⁻¹ ^ r = 1 := by
      rw [← mul_pow]
      simp [hq0]
    have hpow' : q * q ^ r * q⁻¹ * q⁻¹ ^ r = 1 := by
      calc
        q * q ^ r * q⁻¹ * q⁻¹ ^ r = (q * q⁻¹) * (q ^ r * q⁻¹ ^ r) := by ring
        _ = 1 := by rw [mul_inv_cancel₀ hq0, hpow, mul_one]
    have hk :
        (q - q⁻¹)⁻¹ +
            quantumInteger q ((r : ℤ) + 1) * (q - q⁻¹)⁻¹ *
              (q⁻¹ ^ r * q⁻¹ ^ 2) =
          quantumInteger q ((r : ℤ) + 2) * (q - q⁻¹)⁻¹ *
            q⁻¹ ^ (r + 1) := by
      rw [hrec]
      simp only [pow_succ]
      ring_nf
      rw [hpow']
      ring
    have hkInv :
        (q - q⁻¹)⁻¹ +
            quantumInteger q ((r : ℤ) + 1) * (q - q⁻¹)⁻¹ *
              (q ^ r * q ^ 2) =
          quantumInteger q ((r : ℤ) + 2) * (q - q⁻¹)⁻¹ *
            q ^ (r + 1) := by
      rw [hrecInv]
      simp only [pow_succ]
      ring_nf
      rw [hpow']
      ring
    rw [show r + (1 + 1) = r + 2 by omega]
    rw [show ((r + 2 : ℕ) : ℤ) = (r : ℤ) + 2 by omega]
    rw [← hk, ← hkInv]
    module

end TauCeti.UqSl2
