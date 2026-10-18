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
  classical
  have hex : ∃ n : ℕ, f q ^ n • v = 0 := exists_f_pow_smul_eq_zero hq hv
  let N := Nat.find hex
  have hN : f q ^ N • v = 0 := Nat.find_spec hex
  have hNpos : 0 < N := by
    by_contra! h
    exact hv0 (by simpa [Nat.eq_zero_of_le_zero h] using hN)
  let m := N - 1
  have hNm : N = m + 1 := by omega
  have hFm : f q ^ m • v ≠ 0 := by
    exact Nat.find_min hex (by omega)
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
  have hcomm := congrArg (fun a : UqSl2 q => a • v) (e_mul_f_pow hq.sub_inv_ne_zero N)
  rw [mul_smul, hN, smul_zero, add_smul, mul_smul, hev, smul_zero, zero_add,
    smul_assoc] at hcomm
  simp only [smul_assoc, mul_smul, sub_smul] at hcomm
  rw [mem_weightSpace_iff.mp hv, hkInv, smul_smul, smul_smul, hNm,
    Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] at hcomm
  simp only [smul_smul] at hcomm
  rw [← sub_smul, smul_comm (f q ^ m), smul_smul] at hcomm
  have hcoefficient : q⁻¹ ^ m * μ - q ^ m * μ⁻¹ = 0 := by
    have hqi : quantumInteger q ((m : ℤ) + 1) * (q - q⁻¹)⁻¹ ≠ 0 :=
      mul_ne_zero (quantumInteger_ne_zero hq (by omega)) (inv_ne_zero hq.sub_inv_ne_zero)
    have hproduct := (smul_eq_zero.mp hcomm.symm).resolve_right hFm
    exact (mul_eq_zero.mp hproduct).resolve_left hqi
  have hsq : μ ^ 2 = (q ^ m) ^ 2 := by
    field_simp [hq.ne_zero, hμ] at hcoefficient
    rw [mul_zero, sub_eq_zero, one_div, inv_pow] at hcoefficient
    have hs := (inv_mul_eq_iff_eq_mul₀ (pow_ne_zero m hq.ne_zero)).mp hcoefficient
    simpa [pow_two] using hs
  have hfactor : (μ - q ^ m) * (μ + q ^ m) = 0 := by
    calc
      (μ - q ^ m) * (μ + q ^ m) = μ ^ 2 - (q ^ m) ^ 2 := by ring
      _ = 0 := sub_eq_zero.mpr hsq
  rcases mul_eq_zero.mp hfactor with hpos | hneg
  · refine ⟨m, 1, ?_, hNm ▸ hN, hFm⟩
    simpa using sub_eq_zero.mp hpos
  · refine ⟨m, -1, ?_, hNm ▸ hN, hFm⟩
    have := add_eq_zero_iff_eq_neg.mp hneg
    simpa using this

end TauCeti.UqSl2
