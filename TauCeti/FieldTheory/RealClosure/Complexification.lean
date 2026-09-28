/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.FieldTheory.IsRealClosed.Basic
public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.Algebra.Order.Field.Basic
import TauCeti.Algebra.Order.Ring.Ordering.Semireal
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # Square roots in the complexification of a real closed field

The usual algebraic square-root formula uses only square roots of nonnegative
elements of the base field. No completeness or Archimedean property is used.

Use `open scoped TauCeti.RealClosure` to synthesize the field instance on
`QuadraticAlgebra R (-1) 0` outside this namespace. The scope supplies
`Fact (¬ IsSquare (-1 : R))` from `IsSemireal R`, which activates Mathlib's
quadratic-algebra field instance.
-/

public section

namespace TauCeti.RealClosure

/-- In a formally real ring, `-1` is not a square. This supplies the square obstruction
used by the quadratic-algebra field instance. -/
scoped instance {R : Type*} [Ring R] [IsSemireal R] : Fact (¬ IsSquare (-1 : R)) :=
  ⟨fun h => IsSemireal.not_isSumSq_neg_one R h.isSumSq⟩

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-- Every nonnegative element of an ordered real closed field has a nonnegative square root. -/
theorem exists_nonneg_sq {a : R} (ha : 0 ≤ a) : ∃ r : R, 0 ≤ r ∧ r ^ 2 = a := by
  obtain ⟨r, hr⟩ := IsRealClosed.exists_eq_pow_of_nonneg ha (n := 2) (by decide)
  exact ⟨|r|, abs_nonneg r, by simpa using hr.symm⟩

/-- Every element of `R[i]` is a square when `R` is real closed. -/
private theorem complex_isSquare_aux (z : QuadraticAlgebra R (-1) 0) : IsSquare z := by
  by_cases him : z.im = 0
  · rcases IsRealClosed.isSquare_or_isSquare_neg z.re with ⟨r, hr⟩ | ⟨r, hr⟩
    · refine ⟨⟨r, 0⟩, ?_⟩
      ext <;> simp [him, hr]
    · refine ⟨⟨0, r⟩, ?_⟩
      apply QuadraticAlgebra.ext
      · simp only [QuadraticAlgebra.re_mul]
        linear_combination -hr
      · simp [him]
  · obtain ⟨m, hm0, hm⟩ := exists_nonneg_sq
      (add_nonneg (sq_nonneg z.re) (sq_nonneg z.im))
    have hpos : 0 < (m + z.re) / 2 := by
      have : 0 < z.im ^ 2 := sq_pos_of_ne_zero him
      have : -z.re < m := by nlinarith
      exact div_pos (by linarith) (by norm_num)
    obtain ⟨s, _, hs⟩ := exists_nonneg_sq hpos.le
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

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- Every element of `R[i]` is a square when `R` is real closed, without choosing an order. -/
theorem _root_.QuadraticAlgebra.isSquare (z : QuadraticAlgebra R (-1) 0) : IsSquare z := by
  obtain ⟨o, ho⟩ := IsSemireal.exists_linearOrder (K := R)
  let := o
  have := ho
  exact complex_isSquare_aux z

end TauCeti.RealClosure
