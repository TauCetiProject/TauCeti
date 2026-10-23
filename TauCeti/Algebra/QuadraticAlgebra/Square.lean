/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.Algebra.Order.Field.Basic
public import TauCeti.Algebra.Order.Ring.Square
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # Square roots in quadratic complexifications

Every element of `QuadraticAlgebra R (-1) 0` is a square when `R` is an ordered field whose
nonnegative elements are squares. The algebraic formula uses two nonnegative square roots
in `R`, without completeness or an Archimedean assumption.
-/

public section

namespace QuadraticAlgebra

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- Every element of `R[i]` is a square if every nonnegative element of `R` is a square. -/
theorem isSquare_of_forall_nonneg_isSquare (z : QuadraticAlgebra R (-1) 0)
    (hsq : ∀ {a : R}, 0 ≤ a → IsSquare a) : IsSquare z := by
  by_cases him : z.im = 0
  · rcases le_total 0 z.re with hre | hre
    · obtain ⟨r, hr⟩ := hsq hre
      refine ⟨⟨r, 0⟩, ?_⟩
      ext <;> simp [him, hr]
    · obtain ⟨r, hr⟩ := hsq (neg_nonneg.mpr hre)
      refine ⟨⟨0, r⟩, ?_⟩
      apply QuadraticAlgebra.ext
      · simp only [QuadraticAlgebra.re_mul]
        linear_combination -hr
      · simp [him]
  · obtain ⟨m, hm0, hm⟩ :=
      (hsq (add_nonneg (sq_nonneg z.re) (sq_nonneg z.im))).exists_nonneg_sq
    have hpos : 0 < (m + z.re) / 2 := by
      have : 0 < z.im ^ 2 := sq_pos_of_ne_zero him
      have : -z.re < m := by nlinarith
      exact div_pos (by linarith) (by norm_num)
    obtain ⟨s, _, hs⟩ := (hsq hpos.le).exists_nonneg_sq
    have hsne : s ≠ 0 := fun h => hpos.ne' (by rw [← hs, h]; ring)
    have hs2 : 2 * s ^ 2 = m + z.re := by linarith
    let t := z.im / (2 * s)
    have ht : 2 * s * t = z.im := by
      dsimp only [t]
      field_simp
    -- Multiplying by `(2 * s) ^ 2` clears the denominator of `t`; then `hm` and `hs2`
    -- identify the real part of the square.
    have hprod : (2 * s) ^ 2 * (s ^ 2 - t ^ 2 - z.re) = 0 := by
      linear_combination (2 * s ^ 2 + m - z.re) * hs2 + hm - (2 * s * t + z.im) * ht
    have hre : s ^ 2 - t ^ 2 = z.re := sub_eq_zero.mp
      ((mul_eq_zero.mp hprod).resolve_left (pow_ne_zero _ (mul_ne_zero two_ne_zero hsne)))
    refine ⟨⟨s, t⟩, ?_⟩
    apply QuadraticAlgebra.ext
    · simp only [QuadraticAlgebra.re_mul]
      linear_combination -hre
    · simp only [QuadraticAlgebra.im_mul]
      linear_combination -ht

end QuadraticAlgebra
