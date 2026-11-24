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
*unipotent* if `u - 1` is nilpotent. The finite exponential and logarithm are mutually inverse
bijections between nilpotent and unipotent elements, and `log (u ^ n) = n • log u`
(`Units.log_zpow`). Taking an `m`-th root of a unipotent unit therefore amounts to dividing its
logarithm by `m`, which gives unipotent units canonical roots of every nonzero integral order.

For a unipotent unit `u` and a nonzero integer `m`, this file proves:

* `Units.nilpotentExpUnit_inv_smul_log_zpow`: the unipotent unit `exp (m⁻¹ • log u)` is an
  `m`-th root of `u`;
* `Units.eq_exp_inv_smul_log_of_zpow_eq`: every unipotent `m`-th root of a unit `u` is
  `exp (m⁻¹ • log u)`; here only the root, not `u`, is assumed unipotent;
* `Units.existsUnique_isNilpotent_sub_one_and_zpow_eq`: `u` has exactly one unipotent `m`-th
  root.

Uniqueness holds among unipotent units only: in `ℚ` the unit `-1` is a second square root
of `1`. For `m = 0` it fails as soon as `A` has a unipotent unit other than `1`, since every
unit has zeroth power `1`.

Compare `TauCeti.RingTheory.Nilpotent.Sqrt`, which constructs a square root of `1 + x` for
nilpotent `x` as a polynomial in `x` over any commutative ring in which `2` is a unit, without
uniqueness, and `TauCeti.RingTheory.Nilpotent.BinomialPow`, which defines powers `u ^ t` with
exponents `t` in a binomial ring. Here the algebra is rational, the order `m` is any nonzero
integer, and the root is unique among unipotent units.
-/

public section

namespace Units

open IsNilpotent TauCeti

variable {A : Type*} [Ring A] [Algebra ℚ A]

/-- For a nonzero integer `m`, the unipotent unit `exp (m⁻¹ • log u)` is an `m`-th root of the
unipotent unit `u`. -/
theorem nilpotentExpUnit_inv_smul_log_zpow (u : Aˣ) (hu : IsNilpotent ((u : A) - 1)) {m : ℤ}
    (hm : m ≠ 0) : nilpotentExpUnit ((isNilpotent_log hu).smul ((m : ℚ)⁻¹)) ^ m = u := by
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
theorem existsUnique_isNilpotent_sub_one_and_zpow_eq (u : Aˣ) (hu : IsNilpotent ((u : A) - 1))
    {m : ℤ} (hm : m ≠ 0) : ∃! w : Aˣ, IsNilpotent ((w : A) - 1) ∧ w ^ m = u := by
  refine ⟨nilpotentExpUnit ((isNilpotent_log hu).smul ((m : ℚ)⁻¹)),
    ⟨by simpa using isNilpotent_exp_sub_one ((isNilpotent_log hu).smul ((m : ℚ)⁻¹)),
      nilpotentExpUnit_inv_smul_log_zpow u hu hm⟩, fun w ⟨hw, h⟩ ↦ Units.ext ?_⟩
  rw [eq_exp_inv_smul_log_of_zpow_eq hw hm h, coe_nilpotentExpUnit]

end Units
