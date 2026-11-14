/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Nilpotent.Log

/-!
# Roots of unipotent units

Let `A` be an associative, possibly noncommutative, rational algebra. A unit `u` of `A` is
*unipotent* if `u - 1` is nilpotent. This file proves:

* `Units.log_conj`: conjugation by a unit commutes with the finite logarithm,
  `log (v * a * v⁻¹) = v * log a * v⁻¹`;
* `Units.log_zpow`: `log (u ^ n) = n • log u` for every integer `n`;
* `Units.zpow_exp_inv_smul_log`: for a nonzero integer `m`, the unipotent unit
  `exp (m⁻¹ • log u)` is an `m`-th root of `u`;
* `Units.eq_exp_inv_smul_log_of_zpow_eq` and `Units.existsUnique_isNilpotent_zpow_eq`: it is
  the only unipotent `m`-th root of `u`.

Uniqueness holds among unipotent units only: in `ℚ` the unit `-1` is a second square root
of `1`. For `m = 0` it fails as soon as `A` has a unipotent unit other than `1`, since every
unit has zeroth power `1`.
-/

public section

namespace Units

open IsNilpotent TauCeti

variable {A : Type*} [Ring A] [Algebra ℚ A]

/-- Conjugation by a unit commutes with the finite logarithm. When `a - 1` is not nilpotent,
both sides are the junk value `0`. -/
theorem log_conj (v : Aˣ) (a : A) :
    log ((v : A) * a * (v⁻¹ : Aˣ)) = v * log a * (v⁻¹ : Aˣ) := by
  have hsub : (v : A) * a * (v⁻¹ : Aˣ) - 1 = v * (a - 1) * (v⁻¹ : Aˣ) := by
    simp [mul_sub, sub_mul, mul_assoc]
  have hpow (i : ℕ) : ((v : A) * (a - 1) * (v⁻¹ : Aˣ)) ^ i = v * (a - 1) ^ i * (v⁻¹ : Aˣ) := by
    induction i with
    | zero => simp
    | succ i ih => rw [_root_.pow_succ, ih, _root_.pow_succ]; simp [mul_assoc]
  have hclass : nilpotencyClass ((v : A) * a * (v⁻¹ : Aˣ) - 1) = nilpotencyClass (a - 1) := by
    simp only [nilpotencyClass, hsub, hpow]
    congr 1
    ext k
    simp [mul_assoc]
  rw [log_def, log_def, hclass, hsub]
  simp only [hpow, Finset.mul_sum, Finset.sum_mul, mul_smul_comm,
    smul_mul_assoc]

/-- The finite logarithm of an integral power of a unipotent unit is the corresponding integral
multiple of its logarithm. -/
theorem log_zpow (u : Aˣ) (hu : IsNilpotent ((u : A) - 1)) (n : ℤ) :
    log ((u ^ n : Aˣ) : A) = n • log (u : A) := by
  rw [← exp_zsmul_log u hu n, log_exp ((isNilpotent_log hu).smul n)]

/-- For a nonzero integer `m`, the unipotent unit `exp (m⁻¹ • log u)` is an `m`-th root of the
unipotent unit `u`. -/
theorem zpow_exp_inv_smul_log (u : Aˣ) (hu : IsNilpotent ((u : A) - 1)) {m : ℤ} (hm : m ≠ 0) :
    nilpotentExpUnit ((isNilpotent_log hu).smul ((m : ℚ)⁻¹)) ^ m = u := by
  set w := nilpotentExpUnit ((isNilpotent_log hu).smul ((m : ℚ)⁻¹))
  have hw : IsNilpotent ((w : A) - 1) := by
    simpa [w] using isNilpotent_exp_sub_one ((isNilpotent_log hu).smul ((m : ℚ)⁻¹))
  apply Units.ext
  rw [← exp_zsmul_log w hw m, coe_nilpotentExpUnit,
    log_exp ((isNilpotent_log hu).smul ((m : ℚ)⁻¹)), ← Int.cast_smul_eq_zsmul ℚ, smul_smul,
    mul_inv_cancel₀ (Int.cast_ne_zero.mpr hm), one_smul, exp_log hu]

/-- A unipotent `m`-th root of a unit `u`, for a nonzero integer `m`, is `exp (m⁻¹ • log u)`. -/
theorem eq_exp_inv_smul_log_of_zpow_eq {u w : Aˣ} (hw : IsNilpotent ((w : A) - 1)) {m : ℤ}
    (hm : m ≠ 0) (h : w ^ m = u) : (w : A) = exp ((m : ℚ)⁻¹ • log (u : A)) := by
  rw [← h, log_zpow w hw m, ← Int.cast_smul_eq_zsmul ℚ, smul_smul,
    inv_mul_cancel₀ (Int.cast_ne_zero.mpr hm), one_smul, exp_log hw]

/-- **Unipotent roots.** For a nonzero integer `m`, a unipotent unit has exactly one unipotent
`m`-th root. -/
theorem existsUnique_isNilpotent_zpow_eq (u : Aˣ) (hu : IsNilpotent ((u : A) - 1)) {m : ℤ}
    (hm : m ≠ 0) : ∃! w : Aˣ, IsNilpotent ((w : A) - 1) ∧ w ^ m = u := by
  refine ⟨nilpotentExpUnit ((isNilpotent_log hu).smul ((m : ℚ)⁻¹)),
    ⟨by simpa using isNilpotent_exp_sub_one ((isNilpotent_log hu).smul ((m : ℚ)⁻¹)),
      zpow_exp_inv_smul_log u hu hm⟩, fun w ⟨hw, h⟩ ↦ Units.ext ?_⟩
  rw [eq_exp_inv_smul_log_of_zpow_eq hw hm h, coe_nilpotentExpUnit]

end Units
