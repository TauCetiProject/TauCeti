/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.QuantumGroups.UqSl2.Commutator
public import TauCeti.QuantumGroups.UqSl2.Weights

import TauCeti.Algebra.Ring.Int.Units
import Mathlib.Tactic

/-!
# Finite highest-weight strings for `U_q(sl₂)`

At a generic parameter, a nonzero highest-weight vector in a finite-dimensional module has a
finite nonzero lowering string.  Commuting `E` past the first vanishing power of `F` forces its
weight to be `ε q^m` for a sign `ε`.  This is the numerical step in the classification of
finite-dimensional simple modules by the signed ladder modules.  Conversely, the lowering string
of a highest-weight vector of weight `ε q^m` in a finite-dimensional module stops after `m + 1`
steps, so such a vector generates a copy of the signed ladder module `L_m^ε`.

The vanishing holds more generally for a generalized weight vector `w` of weight `ε q^m` killed by
`E`: the commutator formula
`E F^(r+1) = F^(r+1) E + [r+1]_q F^r (q^(-r) K - q^r K⁻¹) / (q - q⁻¹)` shows that `F^r w ≠ 0` for
`w ≠ 0` and `r ≤ m`, and that `F^(m+1) w = 0`. Moreover `K` acts on such a `w` by the scalar
`ε q^m`, so `w` is an honest weight vector. No diagonalizability of `K` is assumed; these are the
weight-space inputs to complete reducibility.

## Main results

* `TauCeti.UqSl2.exists_eq_sign_mul_pow_of_highest_weight_vector`: a nonzero highest-weight
  vector in a finite-dimensional module has weight `ε q^m`.
* `TauCeti.UqSl2.eq_zero_of_f_pow_smul_eq_zero`: a generalized weight vector of weight `ε q^m`
  killed by `E` and by `F^r` for some `r ≤ m` is zero.
* `TauCeti.UqSl2.f_pow_smul_eq_zero_of_e_smul_eq_zero`: a generalized weight vector of weight
  `ε q^m` killed by `E` is killed by `F^(m+1)`; its special case for honest weight vectors is
  `TauCeti.UqSl2.f_pow_succ_smul_eq_zero_of_highest_weight_vector`.
* `TauCeti.UqSl2.mem_weightSpace_of_e_smul_eq_zero`: a generalized weight vector of weight
  `ε q^m` killed by `E` is an honest weight vector.

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

/-! ### The top generalized weight space -/

section Top

variable {m : ℕ} {ε : ℤˣ}

/-- For a vector `w` killed by `E` and by `F^(r+1)`, the commutator formula gives
`F^r (q^(-r) K w - q^r K⁻¹ w) = 0`. -/
private theorem f_pow_smul_k_smul_sub_kInv_smul (hq : IsGenericQuantumParameter q) {r : ℕ}
    {w : V} (he : e q • w = 0) (hf : f q ^ (r + 1) • w = 0) :
    f q ^ r • (q⁻¹ ^ r • k q • w - q ^ r • kInv q • w) = 0 := by
  have h := congrArg (· • w) (e_mul_f_pow hq.sub_inv_ne_zero (r + 1))
  simp only [mul_smul, add_smul, smul_assoc, hf, he, smul_zero, zero_add, Nat.add_sub_cancel,
    sub_smul, smul_sub] at h
  have hc : quantumInteger q ((r + 1 : ℕ) : ℤ) * (q - q⁻¹)⁻¹ ≠ 0 :=
    mul_ne_zero (quantumInteger_ne_zero hq (by omega)) (inv_ne_zero hq.sub_inv_ne_zero)
  rw [smul_sub]
  generalize f q ^ r • q⁻¹ ^ r • k q • w = X at h ⊢
  generalize f q ^ r • q ^ r • kInv q • w = Y at h ⊢
  apply smul_right_injective V hc
  linear_combination (norm := module) -h

/-- For a vector `w` killed by `E` and by `F^(r+1)`, the vector `p = F^r w` satisfies
`K² p = q^(-2r) p`. -/
private theorem k_sq_smul_f_pow_smul (hq : IsGenericQuantumParameter q) {r : ℕ} {w : V}
    (he : e q • w = 0) (hf : f q ^ (r + 1) • w = 0) :
    k q ^ 2 • f q ^ r • w = (q⁻¹ ^ r) ^ 2 • f q ^ r • w := by
  have hq0 := hq.ne_zero
  set p := f q ^ r • w with hp_def
  -- Commute `F^r` past `K` and `K⁻¹`.
  have hk : k q • p = (q⁻¹ ^ 2) ^ r • f q ^ r • k q • w := by
    rw [hp_def, ← mul_smul, k_mul_f_pow, smul_assoc, mul_smul]
  have hkInv : kInv q • p = (q ^ 2) ^ r • f q ^ r • kInv q • w := by
    rw [hp_def, ← mul_smul, kInv_mul_f_pow, smul_assoc, mul_smul]
  clear_value p
  have h := f_pow_smul_k_smul_sub_kInv_smul hq he hf
  rw [smul_sub, smul_comm _ (q⁻¹ ^ r), smul_comm _ (q ^ r)] at h
  -- Hence `q^r K p = q^(-r) K⁻¹ p`, and applying `K` gives `K² p = q^(-2r) p`.
  have hqr : q ^ r * q⁻¹ ^ r = 1 := by simp [hq0]
  have hmain : q ^ r • k q • p = q⁻¹ ^ r • kInv q • p := by
    have hX : q ^ r * (q⁻¹ ^ 2) ^ r = q⁻¹ ^ r := by linear_combination q⁻¹ ^ r * hqr
    have hY : q⁻¹ ^ r * (q ^ 2) ^ r = q ^ r := by linear_combination q ^ r * hqr
    rw [hk, hkInv]
    generalize f q ^ r • k q • w = X at h ⊢
    generalize f q ^ r • kInv q • w = Y at h ⊢
    linear_combination (norm := module) h + hX • X - hY • Y
  have h2 := congrArg (k q • ·) hmain
  simp only [smul_comm (k q) (q ^ r), smul_comm (k q) (q⁻¹ ^ r), ← mul_smul, k_mul_kInv,
    one_smul] at h2
  rw [sq (k q)]
  generalize (k q * k q) • p = Z at h2 ⊢
  linear_combination (norm := module) q⁻¹ ^ r • h2 - hqr • Z

/-- At a generic parameter, the weight `(q⁻²)^r ε q^m` differs from `± q^(-r)` unless `r = m`. -/
private theorem mul_inv_pow_ne_of_ne (hq : IsGenericQuantumParameter q) {r : ℕ} (hr : r ≠ m)
    {s : ℂ} (hs : s ^ 2 = 1) : s * q⁻¹ ^ r ≠ (q⁻¹ ^ 2) ^ r * (ε * q ^ m) := by
  intro h
  have hq0 := hq.ne_zero
  have hqr : q ^ r * q⁻¹ ^ r = 1 := by simp [hq0]
  have a1 : q⁻¹ ^ r * q ^ (2 * r) = q ^ r := by linear_combination q ^ r * hqr
  have a2 : (q⁻¹ ^ 2) ^ r * q ^ (2 * r) = 1 := by
    linear_combination (q ^ r * q⁻¹ ^ r + 1) * hqr
  have hε := Int.cast_units_sq (R := ℂ) ε
  have h1 : (ε : ℂ) * q ^ m = s * q ^ r := by
    linear_combination -q ^ (2 * r) * h + s * a1 - (ε * q ^ m) * a2
  have h2 : q ^ (2 * m) = q ^ (2 * r) := by
    linear_combination (ε * q ^ m + s * q ^ r) * h1 - q ^ (2 * m) * hε +
      q ^ (2 * r) * hs
  exact hr (by have := hq.pow_injective h2; omega)

/-- On a generalized weight vector of weight `ε q^m` killed by `E`, the power `F^(r+1)` loses no
information beyond `F^r` unless `r = m`. -/
private theorem f_pow_smul_eq_zero_of_f_pow_succ_smul_eq_zero (hq : IsGenericQuantumParameter q)
    {r : ℕ} (hr : r ≠ m) {w : V} (hw : w ∈ genWeightSpace q V (ε * q ^ m)) (he : e q • w = 0)
    (hf : f q ^ (r + 1) • w = 0) : f q ^ r • w = 0 := by
  -- `F^r w` has generalized weight `(q⁻²)^r ε q^m`, while `K` acts on it by `q^(-r)`.
  have hp := f_pow_smul_mem_genWeightSpace hw r
  have hkp := k_smul_eq_of_k_sq_smul_eq
    (by simpa using mul_inv_pow_ne_of_ne hq hr (s := -1) (by norm_num)) hp
    (k_sq_smul_f_pow_smul hq he hf)
  exact eq_zero_of_mem_weightSpace_of_mem_genWeightSpace
    (by simpa using mul_inv_pow_ne_of_ne hq hr (s := 1) (by norm_num))
    (mem_weightSpace_iff.mpr hkp) hp

variable (hq : IsGenericQuantumParameter q)
include hq

/-- A generalized weight vector of weight `ε q^m` killed by `E` and by `F^r` for some `r ≤ m`
is zero: `F^r` is injective on such vectors. -/
theorem eq_zero_of_f_pow_smul_eq_zero {r : ℕ} (hr : r ≤ m) {w : V}
    (hw : w ∈ genWeightSpace q V (ε * q ^ m)) (he : e q • w = 0) (hf : f q ^ r • w = 0) :
    w = 0 := by
  induction r with
  | zero => simpa using hf
  | succ r ih =>
    exact ih (by omega) (f_pow_smul_eq_zero_of_f_pow_succ_smul_eq_zero hq (by omega) hw he hf)

variable [FiniteDimensional ℂ V]

/-- At a generic parameter, in a finite-dimensional module, a generalized weight vector of weight
`ε q^m` killed by `E` is killed by `F^(m+1)`. -/
theorem f_pow_smul_eq_zero_of_e_smul_eq_zero {w : V}
    (hw : w ∈ genWeightSpace q V (ε * q ^ m)) (he : e q • w = 0) : f q ^ (m + 1) • w = 0 := by
  -- Some power `F^(m+1+n)` kills `w`; the exponent can be lowered one step at a time.
  obtain ⟨n, hn⟩ := exists_f_pow_smul_eq_zero hq w
  have hn' : f q ^ (m + 1 + n) • w = 0 := by
    rw [pow_add, mul_smul, hn, smul_zero]
  clear hn
  induction n with
  | zero => simpa using hn'
  | succ n ih =>
    exact ih (f_pow_smul_eq_zero_of_f_pow_succ_smul_eq_zero hq (by omega) hw he
      (by simpa [add_assoc] using hn'))

/-- In a finite-dimensional module at a generic parameter, the lowering string of a
highest-weight vector of weight `ε q^m` vanishes after `m + 1` steps. -/
theorem f_pow_succ_smul_eq_zero_of_highest_weight_vector {v : V}
    (hv : v ∈ weightSpace q V (ε * q ^ m)) (hev : e q • v = 0) : f q ^ (m + 1) • v = 0 :=
  f_pow_smul_eq_zero_of_e_smul_eq_zero hq (weightSpace_le_genWeightSpace _ hv) hev

/-- At a generic parameter, in a finite-dimensional module, a generalized weight vector of weight
`ε q^m` killed by `E` is an honest weight vector: `K` acts on it by the scalar `ε q^m`. -/
theorem mem_weightSpace_of_e_smul_eq_zero {w : V} (hw : w ∈ genWeightSpace q V (ε * q ^ m))
    (he : e q • w = 0) : w ∈ weightSpace q V (ε * q ^ m) := by
  have hq0 := hq.ne_zero
  -- `X = q^(-m) K w - q^m K⁻¹ w` lies in the generalized weight space, is killed by `E` since
  -- `E` commutes with `K` and `K⁻¹` up to scalars, and is killed by `F^m`.
  have hX : q⁻¹ ^ m • k q • w - q ^ m • kInv q • w ∈ genWeightSpace q V (ε * q ^ m) :=
    sub_mem (Submodule.smul_mem _ _ (k_smul_mem_genWeightSpace hw))
      (Submodule.smul_mem _ _ (kInv_smul_mem_genWeightSpace hw))
  have heX : e q • (q⁻¹ ^ m • k q • w - q ^ m • kInv q • w) = 0 := by
    simp only [smul_sub, smul_comm (e q), ← mul_smul (e q), e_mul_k, e_mul_kInv, smul_assoc,
      mul_smul, he, smul_zero, sub_zero]
  have hX0 := eq_zero_of_f_pow_smul_eq_zero hq le_rfl hX heX
    (f_pow_smul_k_smul_sub_kInv_smul hq he (f_pow_smul_eq_zero_of_e_smul_eq_zero hq hw he))
  -- Applying `K` to `X = 0` gives `K² w = q^(2m) w = (ε q^m)² w`.
  have hk2 : k q ^ 2 • w = ((ε : ℂ) * q ^ m) ^ 2 • w := by
    have h := congrArg (fun x => q ^ m • k q • x) hX0
    simp only [smul_sub, smul_comm (k q) (q⁻¹ ^ m), smul_comm (k q) (q ^ m), ← mul_smul (k q),
      k_mul_kInv, one_smul, smul_smul, smul_zero, sub_eq_zero] at h
    have hqm : q ^ m * q⁻¹ ^ m = 1 := by simp [hq0]
    rw [hqm, one_smul] at h
    rw [sq (k q), h, mul_pow, Int.cast_units_sq, one_mul, sq]
  have hne : -((ε : ℂ) * q ^ m) ≠ ε * q ^ m := fun h =>
    mul_ne_zero (Int.cast_ne_zero.mpr ε.ne_zero) (pow_ne_zero _ hq0) (by linear_combination -h / 2)
  exact mem_weightSpace_iff.mpr (k_smul_eq_of_k_sq_smul_eq hne hw hk2)

end Top

end TauCeti.UqSl2
