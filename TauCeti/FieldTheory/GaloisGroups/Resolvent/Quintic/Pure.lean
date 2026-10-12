/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Separable
public import TauCeti.FieldTheory.GaloisGroups.Resolvent.Quintic.Basic

import TauCeti.FieldTheory.GaloisGroups.Resolvent.Quintic.Trinomial

/-!
# The resolvent sextic of a pure quintic

For every integer `a`, the resolvent sextic of the pure quintic `X⁵ - a` is `X⁶ - 3125a⁴X`. This
is Dummit's closed formula for the resolvent sextic of the trinomial `X⁵ + aX + b`
(`TauCeti.resolventSextic_X_pow_five_add_C_mul_X_add_C`) read at `X⁵ + 0·X + (-a)`, and it
exhibits `0` as an integral root.

For `a ≠ 0` the sextic is separable over `ℚ`, being the product of `X` and the binomial
`X⁵ - 3125a⁴`, and its root `0` is therefore separation evidence for the pure quintic.

## Main results

* `TauCeti.resolventSextic_X_pow_five_sub_C`: the resolvent sextic of `X⁵ - a` is
  `X⁶ - 3125a⁴X`; `TauCeti.resolventSextic_X_pow_five_sub_intCast` is its simp normal form.
* `TauCeti.separable_map_resolventSextic_X_pow_five_sub_C`: for `a ≠ 0`, that sextic is
  separable over `ℚ`.

## References

* D. S. Dummit, *Solving solvable quintics*, Mathematics of Computation **57** (1991), §1,
  formula (2′).
-/

public section

open Polynomial

namespace TauCeti

/-- **The resolvent sextic of a pure quintic.** For every integer `a`,
`resolventSextic (X⁵ - a) = X⁶ - 3125a⁴X`. This is Dummit's closed formula for the resolvent
sextic of `X⁵ + aX + b` in the case `a = 0`, and it exhibits `0` as an integral root. -/
-- Not `@[simp]`: over `ℤ`, simp rewrites `C a` to `↑a` first (`eq_intCast`), so this left-hand
-- side is not in simp normal form; `resolventSextic_X_pow_five_sub_intCast` is the simp form.
theorem resolventSextic_X_pow_five_sub_C (a : ℤ) :
    resolventSextic (X ^ 5 - C a) = X ^ 6 - C (3125 * a ^ 4) * X := by
  have hf : (X ^ 5 - C a : ℤ[X]) = X ^ 5 + C 0 * X + C (-a) := by
    rw [C_0, zero_mul, add_zero, map_neg, sub_eq_add_neg]
  rw [hf, resolventSextic_X_pow_five_add_C_mul_X_add_C]
  simp only [map_mul, map_pow, map_sub, map_neg, map_ofNat, C_0]
  ring

/-- The resolvent sextic of a pure quintic in simp normal form: over `ℤ`, the constant `C a` is
the cast `↑a`, and `resolventSextic (X⁵ - a) = X⁶ - 3125a⁴X`. -/
@[simp] theorem resolventSextic_X_pow_five_sub_intCast (a : ℤ) :
    resolventSextic (X ^ 5 - (a : ℤ[X])) = X ^ 6 - 3125 * (a : ℤ[X]) ^ 4 * X := by
  simpa using resolventSextic_X_pow_five_sub_C a

/-- Over `ℚ`, the resolvent sextic `X⁶ - 3125a⁴X` of a pure quintic `X⁵ - a` with `a ≠ 0` is
separable, so its root `0` is separation evidence for the quintic certificate. -/
theorem separable_map_resolventSextic_X_pow_five_sub_C {a : ℤ} (ha : a ≠ 0) :
    ((resolventSextic (X ^ 5 - C a)).map (Int.castRingHom ℚ)).Separable := by
  rw [resolventSextic_X_pow_five_sub_C]
  set c : ℚ := Int.castRingHom ℚ (3125 * a ^ 4) with hc_def
  have hc : c ≠ 0 := by
    simp only [hc_def, eq_intCast, Int.cast_mul, Int.cast_pow, Int.cast_ofNat]
    positivity
  have hmap : (X ^ 6 - C (3125 * a ^ 4) * X : ℤ[X]).map (Int.castRingHom ℚ) =
      X * (X ^ 5 - C c) := by
    simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_C]
    ring
  rw [hmap]
  refine separable_X.mul (separable_X_pow_sub_C _ (by norm_num) hc)
    ⟨C c⁻¹ * X ^ 4, -C c⁻¹, ?_⟩
  have hinv : (C c⁻¹ : ℚ[X]) * C c = 1 := by
    rw [← C_mul, inv_mul_cancel₀ hc, C_1]
  linear_combination hinv

end TauCeti
