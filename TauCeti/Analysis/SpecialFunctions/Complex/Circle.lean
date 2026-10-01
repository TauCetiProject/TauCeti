/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.CharacterModule
public import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# The character `e^{2πi·}` of `ℚ/ℤ`

Mathlib's `AddCircle.toCircle` is the character `x ↦ e^{2πi x / T}` of the real circle
`AddCircle (T : ℝ)`. Discriminant forms, finite quadratic modules and character modules take their
values in the rational circle `ℚ/ℤ = AddCircle (1 : ℚ)` instead, and this file names the standard
character of that group,

```text
expCircle : ℚ/ℤ → ℂ,   r mod ℤ ↦ e^{2πi r},
```

as a Mathlib `AddChar`. It is faithful, so composing it with a `ℚ/ℤ`-valued character of a finite
abelian group gives a complex character that is trivial exactly when the original one is; the
orthogonality relation for such characters is the basic input of Gauss sums of finite quadratic
modules.

## Main declarations

* `TauCeti.expCircle`: the additive character `r mod ℤ ↦ e^{2πi r}` of `AddCircle (1 : ℚ)`.
* `TauCeti.expCircle_coe`: its value on the class of a rational number.
* `TauCeti.expCircle_eq_one_iff`: it is faithful.
* `TauCeti.expCircle_neg`: its value at `-x` is the complex conjugate of its value at `x`.
* `TauCeti.expCircle_half`, `TauCeti.expCircle_quarter`, `TauCeti.expCircle_eighth`: its values
  `-1`, `i` and `(1 + i) / √2` at `1/2`, `1/4` and `1/8`.
* `CharacterModule.sum_expCircle`: the orthogonality relation
  `∑ m, e^{2πi χ(m)} = if χ = 0 then #M else 0` for a `ℚ/ℤ`-valued character `χ` of a finite
  abelian group `M`.
-/

public section

open Complex ComplexConjugate
open scoped Real

namespace TauCeti

/-- The exponential `r ↦ e^{2πi r}` on `ℚ` has period `1`. -/
private theorem periodic_exp_two_pi_mul_I_ratCast :
    Function.Periodic (fun r : ℚ ↦ exp (2 * π * I * r)) 1 := fun r ↦ by
  simp only [Rat.cast_add, Rat.cast_one, mul_add, mul_one, exp_add, exp_two_pi_mul_I]

/-- **The standard character `e^{2πi·}` of `ℚ/ℤ`.** The class of a rational number `r` is sent to
`e^{2πi r}`; this is well defined because `e^{2πi}` is `1`. It is the analogue for the rational
circle `AddCircle (1 : ℚ)` of Mathlib's `AddCircle.toCircle` on a real circle. -/
noncomputable def expCircle : AddChar (AddCircle (1 : ℚ)) ℂ where
  toFun := periodic_exp_two_pi_mul_I_ratCast.lift
  map_zero_eq_one' := by
    rw [← QuotientAddGroup.mk_zero, Function.Periodic.lift_coe, Rat.cast_zero, mul_zero, exp_zero]
  map_add_eq_mul' x y := by
    induction x using QuotientAddGroup.induction_on with | H r =>
    induction y using QuotientAddGroup.induction_on with | H s =>
    rw [← QuotientAddGroup.mk_add, Function.Periodic.lift_coe, Function.Periodic.lift_coe,
      Function.Periodic.lift_coe, Rat.cast_add, mul_add, exp_add]

/-- The value of `expCircle` on the class of a rational number `r` is `e^{2πi r}`. -/
@[simp]
theorem expCircle_coe (r : ℚ) :
    expCircle (r : AddCircle (1 : ℚ)) = exp (2 * π * I * r) :=
  periodic_exp_two_pi_mul_I_ratCast.lift_coe r

/-- `expCircle` is faithful: its value is `1` only at `0`. -/
@[simp]
theorem expCircle_eq_one_iff {x : AddCircle (1 : ℚ)} : expCircle x = 1 ↔ x = 0 := by
  induction x using QuotientAddGroup.induction_on with | H r =>
  rw [expCircle_coe, exp_eq_one_iff, AddCircle.coe_eq_zero_iff]
  refine ⟨fun ⟨n, hn⟩ ↦ ⟨n, ?_⟩, fun ⟨n, hn⟩ ↦ ⟨n, ?_⟩⟩
  · have h2πI : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
    have hr : ((n : ℚ) : ℂ) = (r : ℂ) := by
      rw [Rat.cast_intCast]
      exact (mul_right_cancel₀ h2πI (by rw [← hn]; ring)).symm
    rw [zsmul_eq_mul, mul_one]
    exact_mod_cast hr
  · rw [← hn, zsmul_eq_mul, mul_one, Rat.cast_intCast]
    ring

/-- `expCircle` takes values on the unit circle: its value at `-x` is the complex conjugate of its
value at `x`. -/
@[simp]
theorem expCircle_neg (x : AddCircle (1 : ℚ)) : expCircle (-x) = conj (expCircle x) := by
  induction x using QuotientAddGroup.induction_on with | H r =>
  rw [← QuotientAddGroup.mk_neg, expCircle_coe, expCircle_coe, ← exp_conj]
  simp [map_ofNat]

/-- The value of `expCircle` at `1/2` is `e^{πi} = -1`. -/
theorem expCircle_half : expCircle ((1 / 2 : ℚ) : AddCircle (1 : ℚ)) = -1 := by
  rw [expCircle_coe]
  push_cast
  rw [show 2 * (π : ℂ) * I * (1 / 2) = π * I by ring, exp_pi_mul_I]

/-- The value of `expCircle` at `1/4` is `e^{πi/2} = i`. -/
theorem expCircle_quarter : expCircle ((1 / 4 : ℚ) : AddCircle (1 : ℚ)) = I := by
  rw [expCircle_coe]
  push_cast
  rw [show 2 * (π : ℂ) * I * (1 / 4) = π / 2 * I by ring, exp_pi_div_two_mul_I]

/-- The value of `expCircle` at `1/8` is `e^{πi/4} = (1 + i) / √2`. -/
theorem expCircle_eighth : expCircle ((1 / 8 : ℚ) : AddCircle (1 : ℚ)) = (1 + I) / √2 := by
  have h2 : (√2 : ℂ) ≠ 0 := ofReal_ne_zero.2 (Real.sqrt_ne_zero'.2 zero_lt_two)
  have hsq : (√2 : ℂ) * √2 = 2 := by
    rw [← ofReal_mul, Real.mul_self_sqrt zero_le_two, ofReal_ofNat]
  rw [expCircle_coe, eq_div_iff h2]
  push_cast
  rw [show 2 * (π : ℂ) * I * (1 / 8) = ((π / 4 : ℝ) : ℂ) * I by push_cast; ring, exp_mul_I,
    ← ofReal_cos, ← ofReal_sin, Real.cos_pi_div_four, Real.sin_pi_div_four]
  push_cast
  linear_combination (1 / 2 + 1 / 2 * I) * hsq

end TauCeti

namespace CharacterModule

open TauCeti

/-- **Orthogonality for a `ℚ/ℤ`-valued character.** Summing `e^{2πi χ(m)}` over a finite abelian
group gives its order when the character `χ` is trivial and `0` otherwise. -/
theorem sum_expCircle {M : Type*} [AddCommGroup M] [Fintype M] (χ : CharacterModule M)
    [Decidable (χ = 0)] :
    ∑ m, expCircle (χ m) = if χ = 0 then (Fintype.card M : ℂ) else 0 := by
  let ψ : AddChar M ℂ := expCircle.compAddMonoidHom χ
  have hψ : ψ = 0 ↔ χ = 0 := by
    rw [AddChar.eq_zero_iff, CharacterModule.ext_iff]
    exact forall_congr' fun _ ↦ expCircle_eq_one_iff
  classical
  calc ∑ m, expCircle (χ m) = ∑ m, ψ m := rfl
    _ = if ψ = 0 then (Fintype.card M : ℂ) else 0 := AddChar.sum_eq_ite ψ
    _ = _ := if_congr hψ rfl rfl

end CharacterModule
