/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import TauCeti.Algebra.Polynomial.QuadraticDiscriminant

/-!
# Double roots of quadratics modulo the maximal ideal

Let `R` be a local ring with perfect residue field. If the discriminant `a² + 4 b` of the monic
quadratic `T² + a T − b` lies in the maximal ideal, then the reduction of the quadratic has a double
root in the residue field
(`Polynomial.exists_quadratic_eq_zero_and_two_mul_add_eq_zero_of_discrim_eq_zero`), and any lift
`s ∈ R` of it is a root of the quadratic and of its derivative modulo the maximal ideal. In
characteristic two the double root is a square root, which is where perfectness is needed.

This is the completing-the-square step of Tate's algorithm (Step 6), where it is applied twice to
the coefficients of a Weierstrass equation over a discrete valuation ring.

## Main results

* `TauCeti.IsLocalRing.exists_add_two_mul_mem_maximalIdeal_and_sub_mul_sub_sq_mem_maximalIdeal`:
  if `a² + 4 b ∈ 𝔪`, some `s` has `a + 2 s ∈ 𝔪` and `b − s a − s² ∈ 𝔪`.
-/

public section

namespace TauCeti.IsLocalRing

open _root_.IsLocalRing Polynomial

variable {R : Type*} [CommRing R] [IsLocalRing R] [PerfectField (ResidueField R)]

/-- A double root of `T² + a T − b` modulo the maximal ideal, lifted from the perfect residue
field: if the discriminant `a² + 4 b` lies in the maximal ideal, some `s ∈ R` has
`a + 2 s ∈ 𝔪` and `b − s a − s² ∈ 𝔪`. -/
theorem exists_add_two_mul_mem_maximalIdeal_and_sub_mul_sub_sq_mem_maximalIdeal {a b : R}
    (h : a ^ 2 + 4 * b ∈ maximalIdeal R) :
    ∃ s : R, a + 2 * s ∈ maximalIdeal R ∧ b - s * a - s ^ 2 ∈ maximalIdeal R := by
  have hd : discrim 1 (residue R a) (-residue R b) = 0 := by
    rw [discrim, ← (residue_eq_zero_iff _).2 h]
    simp only [map_add, map_pow, map_mul, map_ofNat]
    ring
  obtain ⟨x, hx, hx'⟩ :=
    exists_quadratic_eq_zero_and_two_mul_add_eq_zero_of_discrim_eq_zero one_ne_zero hd
  obtain ⟨s, rfl⟩ := residue_surjective x
  refine ⟨s, (residue_eq_zero_iff _).1 ?_, (residue_eq_zero_iff _).1 ?_⟩
  · simp only [map_add, map_mul, map_ofNat]
    linear_combination hx'
  · simp only [map_sub, map_mul, map_pow]
    linear_combination -hx

end TauCeti.IsLocalRing
