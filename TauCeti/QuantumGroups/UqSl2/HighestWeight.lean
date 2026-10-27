/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.QuantumGroups.UqSl2.Commutator
public import TauCeti.QuantumGroups.UqSl2.Weights

import Mathlib.Tactic

/-!
# Finite highest-weight strings for `U_q(sl₂)`

At a generic parameter, a nonzero highest-weight vector in a finite-dimensional module has a
finite nonzero lowering string.  Commuting `E` past the first vanishing power of `F` forces its
weight to be `ε q^m` for a sign `ε`.  This is the numerical step in the classification of
finite-dimensional simple modules by the signed ladder modules.

The calculation follows A. Virelizier, *Quantum groups*, Section 2.4.
-/

public noncomputable section

namespace TauCeti.UqSl2

variable {q : ℂ} {V : Type*} [AddCommGroup V] [Module ℂ V]
  [Module (UqSl2 q) V] [IsScalarTower ℂ (UqSl2 q) V]

/-- A finite nonzero lowering string from a highest-weight vector has signed integral highest
weight.  The returned `m` is the last nonvanishing index of the string. -/
theorem exists_eq_sign_mul_pow_of_highest_weight_vector [FiniteDimensional ℂ V]
    (hq : IsGenericQuantumParameter q) {μ : ℂ} {v : V} (hv : v ∈ weightSpace q V μ)
    (hv0 : v ≠ 0) (hev : e q • v = 0) :
    ∃ (m : ℕ) (ε : ℤˣ), μ = ε * q ^ m ∧
      f q ^ (m + 1) • v = 0 ∧ f q ^ m • v ≠ 0 := by
  obtain ⟨m, hFm, hFm1⟩ :=
    exists_pow_smul_ne_zero_and_smul_eq_zero hv0 (exists_f_pow_smul_eq_zero hq v)
  have hN : f q ^ (m + 1) • v = 0 := by rwa [pow_succ', mul_smul]
  have hμ := weight_ne_zero hv hv0
  have hkInv : kInv q • v = μ⁻¹ • v := by
    have hk : μ • (kInv q • v) = v := by
      calc
        μ • (kInv q • v) = kInv q • (μ • v) := smul_comm _ _ _
        _ = kInv q • (k q • v) := by rw [mem_weightSpace_iff.mp hv]
        _ = (kInv q * k q) • v := (mul_smul _ _ _).symm
        _ = v := by rw [kInv_mul_k, one_smul]
    calc
      kInv q • v = μ⁻¹ • (μ • (kInv q • v)) := by simp [smul_smul, hμ]
      _ = μ⁻¹ • v := by rw [hk]
  -- Apply the commutator formula to `v`; only the `K`, `K⁻¹` term survives.
  have hcomm : (quantumInteger q (m + 1) * (q - q⁻¹)⁻¹ * (q⁻¹ ^ m * μ - q ^ m * μ⁻¹)) •
      f q ^ m • v = 0 := by
    have hf (c : ℂ) (w : V) : f q ^ m • c • w = c • f q ^ m • w := smul_comm _ _ _
    have h := congrArg (· • v) (e_mul_f_pow hq.sub_inv_ne_zero (m + 1))
    simp only [mul_smul, hN, hev, smul_zero, add_smul, zero_add, smul_assoc,
      sub_smul, mem_weightSpace_iff.mp hv, hkInv, Nat.add_sub_cancel, Nat.cast_add,
      Nat.cast_one, smul_sub, hf] at h
    generalize f q ^ m • v = w at h ⊢
    linear_combination (norm := module) -h
  have hcoefficient : q⁻¹ ^ m * μ - q ^ m * μ⁻¹ = 0 := by
    have hqi : quantumInteger q ((m : ℤ) + 1) * (q - q⁻¹)⁻¹ ≠ 0 :=
      mul_ne_zero (quantumInteger_ne_zero hq (by omega)) (inv_ne_zero hq.sub_inv_ne_zero)
    exact (mul_eq_zero.mp ((smul_eq_zero.mp hcomm).resolve_right hFm)).resolve_left hqi
  have hsq : μ ^ 2 = (q ^ m) ^ 2 := by
    have hqm : q ^ m * q⁻¹ ^ m = 1 := by rw [← mul_pow, mul_inv_cancel₀ hq.ne_zero, one_pow]
    linear_combination
      (μ * q ^ m) * hcoefficient - μ ^ 2 * hqm + (q ^ m) ^ 2 * mul_inv_cancel₀ hμ
  rcases eq_or_eq_neg_of_sq_eq_sq μ (q ^ m) hsq with hpos | hneg
  · exact ⟨m, 1, by simpa using hpos, hN, hFm⟩
  · exact ⟨m, -1, by simpa using hneg, hN, hFm⟩

end TauCeti.UqSl2
