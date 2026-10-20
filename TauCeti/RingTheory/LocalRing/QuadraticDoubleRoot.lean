/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import TauCeti.Algebra.Polynomial.QuadraticDiscriminant

/-!
# Double and simple roots of quadratics modulo the maximal ideal

Let `R` be a local ring with perfect residue field. If the discriminant `a² + 4 b` of the monic
quadratic `T² + a T − b` lies in the maximal ideal, then the reduction of the quadratic has a double
root in the residue field
(`Polynomial.exists_quadratic_eq_zero_and_two_mul_add_eq_zero_of_discrim_eq_zero`), and any lift
`s ∈ R` of it is a root of the quadratic and of its derivative modulo the maximal ideal. In
characteristic two the double root is a square root, which is where perfectness is needed.

This is the completing-the-square step of Tate's algorithm (Step 6), where it is applied twice to
the coefficients of a Weierstrass equation over a discrete valuation ring.

Conversely, over any local ring, if the discriminant `a² + 4 b` is a unit then every root `t` of
`T² + a T − b` modulo the maximal ideal is simple: the derivative `2 t + a` is a unit, since
`(2 t + a)² = 4 (t² + a t − b) + (a² + 4 b)`.

## Main results

* `TauCeti.IsLocalRing.exists_add_two_mul_mem_maximalIdeal_and_sub_mul_sub_sq_mem_maximalIdeal`:
  if `a² + 4 b ∈ 𝔪`, some `s` has `a + 2 s ∈ 𝔪` and `b − s a − s² ∈ 𝔪`.
* `TauCeti.IsLocalRing.isUnit_two_mul_add_of_isUnit_sq_add_four_mul`: if `a² + 4 b` is a unit and
  `t² + a t − b ∈ 𝔪`, then `2 t + a` is a unit.
* `TauCeti.HenselianLocalRing.exists_quadratic_root_of_isUnit_discriminant`: in a Henselian local
  ring,
  a root modulo the maximal ideal of a monic quadratic with unit discriminant lifts to a root
  with unit derivative.
-/

public section

namespace TauCeti.IsLocalRing

open _root_.IsLocalRing Polynomial

variable {R : Type*} [CommRing R] [IsLocalRing R]

/-- A root of `T² + a T − b` modulo the maximal ideal is simple when the discriminant `a² + 4 b` is
a unit: if `t² + a t − b ∈ 𝔪`, then `2 t + a` is a unit, since
`(2 t + a)² = 4 (t² + a t − b) + (a² + 4 b)`. -/
theorem isUnit_two_mul_add_of_isUnit_sq_add_four_mul {a b t : R} (hd : IsUnit (a ^ 2 + 4 * b))
    (ht : t ^ 2 + a * t - b ∈ maximalIdeal R) : IsUnit (2 * t + a) := by
  by_contra h
  rw [← mem_nonunits_iff, ← mem_maximalIdeal] at h
  refine (mem_maximalIdeal _).1 ?_ hd
  rw [show a ^ 2 + 4 * b = (2 * t + a) ^ 2 - 4 * (t ^ 2 + a * t - b) by ring]
  exact sub_mem (Ideal.pow_mem_of_mem _ h 2 two_pos) (Ideal.mul_mem_left _ 4 ht)

variable [PerfectField (ResidueField R)]

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

namespace TauCeti.HenselianLocalRing

open _root_.IsLocalRing Polynomial

variable {R : Type*} [CommRing R] [HenselianLocalRing R]

/-- A root of `T² + a T − b` modulo the maximal ideal of a Henselian local ring lifts to a root
in the same residue class with unit derivative when `a² + 4 b` is a unit. -/
theorem exists_quadratic_root_of_isUnit_discriminant {a b t : R}
    (hd : IsUnit (a ^ 2 + 4 * b)) (ht : t ^ 2 + a * t - b ∈ maximalIdeal R) :
    ∃ s : R, s ^ 2 + a * s - b = 0 ∧ s - t ∈ maximalIdeal R ∧ IsUnit (2 * s + a) := by
  let f : R[X] := X ^ 2 + C a * X - C b
  have hmon : f.Monic := by
    dsimp [f]
    monicity!
  have hf₀ : f.eval t ∈ maximalIdeal R := by simpa [f] using ht
  have hf₁ : IsUnit (f.derivative.eval t) := by
    simpa [f, one_add_one_eq_two] using
      TauCeti.IsLocalRing.isUnit_two_mul_add_of_isUnit_sq_add_four_mul hd ht
  obtain ⟨s, hs, hst⟩ := _root_.HenselianLocalRing.is_henselian f hmon t hf₀ hf₁
  have heq : s ^ 2 + a * s - b = 0 := by simpa [f] using hs.eq_zero
  exact ⟨s, heq, hst, TauCeti.IsLocalRing.isUnit_two_mul_add_of_isUnit_sq_add_four_mul hd
    (by rw [heq]; exact zero_mem _)⟩

end TauCeti.HenselianLocalRing
