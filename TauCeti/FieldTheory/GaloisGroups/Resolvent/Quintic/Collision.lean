/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Separable
public import TauCeti.FieldTheory.GaloisGroups.Resolvent.Quintic.Trinomial
public import TauCeti.RingTheory.Polynomial.Resultant.Discriminant
import Mathlib.Basic.Complex.Basic
import TauCeti.Algebra.BigOperators.Finset.Pairs

/-!
# A collision in the quintic resolvent

The quintic `X⁵ - X` is separable (with discriminant `-256`), while Dummit's sextic resolvent
is `(X - 2)⁴ (X² + 16)` and is inseparable with rational root `2`. These computations supply
the arithmetic part of the collision example for the resolvent converse.

## Main results

* `TauCeti.discr_X_pow_five_sub_X`: the discriminant is `-256`.
* `TauCeti.separable_X_pow_five_sub_X`: the quintic is separable over `ℚ`.
* `TauCeti.resolventSextic_X_pow_five_sub_X`: the sextic is `(X - 2)⁴ (X² + 16)`.
* `TauCeti.isRoot_resolventSextic_X_pow_five_sub_X`: `2` is an integral root.
* `TauCeti.not_separable_map_resolventSextic_X_pow_five_sub_X`: the sextic is inseparable over `ℚ`.
-/

public section

open Polynomial

namespace TauCeti

/-- The polynomial `X⁵ - X` is monic over `ℤ`. -/
theorem monic_X_pow_five_sub_X : (X ^ 5 - X : ℤ[X]).Monic := by monicity!

/-- The discriminant of `X⁵ - X` is `-256`. Its nonzero value proves separability over `ℚ`. -/
theorem discr_X_pow_five_sub_X : (X ^ 5 - X : ℤ[X]).discr = -256 := by
  have h := monic_X_pow_five_sub_X.discr_map (Int.castRingHom ℂ)
  simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X] at h
  rw [prod_X_sub_C_rootsXPowFiveSubX, discr_prod_X_sub_C] at h
  have hcalc : (∏ i : Fin 5, ∏ j ∈ Finset.Ioi i,
      (rootsXPowFiveSubX i - rootsXPowFiveSubX j) ^ 2) = (-256 : ℂ) := by
    rw [prod_prod_Ioi_eq_of_two (m := 3), prod_prod_Ioi_eq_of_two (m := 1)]
    norm_num [Fin.prod_univ_three, Fin.prod_univ_one, Fin.prod_Ioi_zero,
      Fin.prod_univ_zero, rootsXPowFiveSubX_def]
    linear_combination (16 * Complex.I ^ 8 - 80 * Complex.I ^ 6 +
      176 * Complex.I ^ 4 - 240 * Complex.I ^ 2 + 256) * Complex.I_sq
  rw [hcalc] at h
  apply Int.cast_injective (α := ℂ)
  simpa using h.symm

/-- The quintic `X⁵ - X` is separable over `ℚ`. -/
theorem separable_X_pow_five_sub_X : (X ^ 5 - X : ℚ[X]).Separable := by
  have hsep := (monic_X_pow_five_sub_X.discr_ne_zero_iff_separable_map ℚ).mp (by
    rw [discr_X_pow_five_sub_X]
    norm_num)
  simpa using hsep

/-- Dummit's sextic of `X⁵ - X` has a quadruple root at `2` and two nonreal roots. -/
theorem resolventSextic_X_pow_five_sub_X :
    resolventSextic (X ^ 5 - X : ℤ[X]) = (X - 2) ^ 4 * (X ^ 2 + 16) := by
  have hf : (X ^ 5 - X : ℤ[X]) = X ^ 5 + C (-1) * X + C 0 := by simp [sub_eq_add_neg]
  rw [hf, resolventSextic_X_pow_five_add_C_mul_X_add_C]
  norm_num
  ring

/-- The quintic `X⁵ - X` has `2` as an integral root of its sextic resolvent. -/
theorem isRoot_resolventSextic_X_pow_five_sub_X :
    (resolventSextic (X ^ 5 - X : ℤ[X])).IsRoot 2 := by
  rw [resolventSextic_X_pow_five_sub_X]
  simp

/-- The specialized sextic of `X⁵ - X` over `ℚ` is inseparable, despite the quintic having
distinct roots. -/
theorem not_separable_map_resolventSextic_X_pow_five_sub_X :
    ¬ (Polynomial.Separable
      ((resolventSextic (X ^ 5 - X : ℤ[X])).map (Int.castRingHom ℚ))) := by
  intro hsep
  have hformula : (resolventSextic (X ^ 5 - X : ℤ[X])).map (Int.castRingHom ℚ) =
      (X - 2) ^ 4 * (X ^ 2 + 16 : ℚ[X]) := by
    rw [resolventSextic_X_pow_five_sub_X]
    simp
  rw [hformula] at hsep
  exact absurd (hsep.of_mul_left.of_pow (not_isUnit_X_sub_C (2 : ℚ)) (by decide)).2
    (by norm_num)

end TauCeti
