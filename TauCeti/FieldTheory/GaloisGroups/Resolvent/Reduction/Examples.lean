/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.GaloisGroups.Resolvent.Reduction.Basic
public import TauCeti.FieldTheory.GaloisGroups.Certificate.Dihedral

import TauCeti.FieldTheory.GaloisGroups.Resolvent.Quintic.Pure
import TauCeti.FieldTheory.GaloisGroups.Resolvent.Quintic.Trinomial
import Mathlib.Tactic.ReduceModChar

/-!
# Good and bad reductions of quintic resolvents

The prime `3` is good for both `X⁵ - 2` and its sextic resolvent. In contrast, it is good for
`X⁵ - 5X - 12` but bad for that polynomial's sextic resolvent: the latter reduces to
`(X - 1)⁴ (X² + 1)`. The sextic is separable over `ℚ`, so the collision is introduced by
reduction, rather than being inherited from characteristic zero.

These examples show why avoiding the discriminant of the original polynomial does not
suffice to apply a resolvent subgroup test over the residue field.

## References

* D. S. Dummit, *Solving solvable quintics*, Mathematics of Computation **57** (1991),
  equations (2) and (2′), for the sextics used here.
-/

public section

open Polynomial

namespace TauCeti

/-- The prime `3` preserves separability of the pure quintic `X⁵ - 2` and its sextic resolvent. -/
theorem isGoodPrime_quinticF20Spec_X_pow_five_sub_two_three :
    quinticF20Spec.IsGoodPrime (X ^ 5 - 2) 3 := by
  have hf : (X ^ 5 - 2 : ℤ[X]).Monic := by monicity!
  rw [ResolventSpec.isGoodPrime_iff_separable _ hf]
  constructor
  · simpa only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_ofNat, C_ofNat] using
      separable_X_pow_sub_C (n := 5) (2 : ZMod 3) (by decide) (by decide)
  · rw [← ResolventSpec.specialize_map, ← resolventSextic_def]
    have hformula : resolventSextic (X ^ 5 - 2 : ℤ[X]) = X ^ 6 - 50000 * X := by
      convert resolventSextic_X_pow_five_sub_intCast 2 using 1
      norm_num
    rw [hformula]
    norm_num only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_mul, Polynomial.map_ofNat]
    reduce_mod_char
    -- In characteristic three the derivative of this sextic is the constant one.
    rw [separable_def]
    have hder : derivative (X ^ 6 + X : (ZMod 3)[X]) = 1 := by
      simp only [derivative_add, derivative_X_pow, derivative_X]
      reduce_mod_char
      simp
    rw [hder]
    exact isCoprime_one_right

/-- Modulo `3`, the sextic of `X⁵ - 5X - 12` develops a quadruple root at `1`. -/
theorem map_resolventSextic_X_pow_five_sub_five_mul_X_sub_twelve_three :
    (resolventSextic (X ^ 5 - 5 * X - 12)).map (Int.castRingHom (ZMod 3)) =
      (X - 1) ^ 4 * (X ^ 2 + 1) := by
  rw [resolventSextic_X_pow_five_sub_five_mul_X_sub_twelve]
  norm_num only [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_pow,
    Polynomial.map_mul, Polynomial.map_X, Polynomial.map_ofNat]
  ring_nf
  reduce_mod_char

/-- Although `3` avoids the quintic discriminant, it does not avoid the sextic discriminant.
The resolvent over `ℚ` is separable, but its reduction is not. -/
theorem isGoodPrime_and_not_isGoodPrime_quinticF20Spec_X_pow_five_sub_five_mul_X_sub_twelve :
    IsGoodPrime (X ^ 5 - 5 * X - 12) 3 ∧
      ¬ quinticF20Spec.IsGoodPrime (X ^ 5 - 5 * X - 12) 3 := by
  constructor
  · rw [isGoodPrime_iff, discr_X_pow_five_sub_five_mul_X_sub_twelve]
    norm_num
  · intro h
    have hsep := h.separable_specialize
    rw [← ResolventSpec.specialize_map, ← resolventSextic_def,
      map_resolventSextic_X_pow_five_sub_five_mul_X_sub_twelve_three] at hsep
    have hpow := hsep.of_mul_left.of_pow (not_isUnit_X_sub_C (1 : ZMod 3)) (by decide)
    norm_num at hpow

end TauCeti
