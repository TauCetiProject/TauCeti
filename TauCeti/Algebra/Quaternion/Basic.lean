/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Quaternion
import Mathlib.Tactic.LinearCombination

/-!
# Basic facts about the Hamilton quaternions

This file collects elementary facts about the Hamilton quaternions `ℍ[R]`, and more generally the
quaternion algebras `ℍ[R,c₁,c₂,c₃]`, over a commutative ring `R` that depend on nothing beyond
Mathlib's `Mathlib.Algebra.Quaternion`.

## Main results

* `QuaternionAlgebra.instStarModule`: scalars from a ring with trivial star commute with the
  quaternion conjugation, so for example `ℍ` is a real star module.
* `Quaternion.isLeftRegular_two`: if `ℍ[R]` has no zero divisors then `2` is left regular in `R`,
  because the quaternion `r + r i` squares to `2 r² i`.
* `Quaternion.normSq_mk_div`: the norm of `(a + b i + c j + d k) / e` is
  `(a² + b² + c² + d²) / e²`.
* `Quaternion.normSq_mk_div_two`: the norm of `(a + b i + c j + d k) / 2` is
  `(a² + b² + c² + d²) / 4`, as used for quaternions with half-integer coordinates.
* `Quaternion.mk_div_mul_mk_div` and `Quaternion.exists_mk_div_mul_mk_div`: multiplying
  quaternions with coordinates scaled by `r` and `s` gives the product with coordinates scaled by
  `r * s`.
* `Quaternion.exists_mk_div_two_mul_eq`: an integer quaternion with even coordinates divided by
  `2 * r` has integer coordinates divided by `r`.
* `Quaternion.exists_mk_div_mul_mk_div_of_even_coords`: multiplying quaternions with
  `ℤ`-coordinates scaled by `r` and `s` with `r * s = 2 * e` gives `ℤ`-coordinates scaled by `e`
  when the integer product has even coordinates.
-/

public section

open scoped Quaternion

namespace QuaternionAlgebra

variable {R : Type*} [CommRing R] [Star R] [TrivialStar R] {c₁ c₂ c₃ : R}

/-- Quaternion conjugation commutes with scalars from a ring with trivial star. -/
instance : StarModule R ℍ[R,c₁,c₂,c₃] where
  star_smul r a := by rw [QuaternionAlgebra.star_smul, star_trivial r]

end QuaternionAlgebra

namespace Quaternion

variable {R : Type*} [CommRing R]

/-- If `ℍ[R]` has no zero divisors then `2` is left regular in `R`: for `2 * r = 0` the quaternion
`r + r i` squares to `2 r² i = 0`. -/
theorem isLeftRegular_two [NoZeroDivisors ℍ[R]] : IsLeftRegular (2 : R) := by
  intro a b (h : 2 * a = 2 * b)
  have hsq : (⟨a - b, a - b, 0, 0⟩ : ℍ[R]) * ⟨a - b, a - b, 0, 0⟩ = 0 := by
    ext <;> simp only [re_mul, imI_mul, imJ_mul, imK_mul, re_zero, imI_zero, imJ_zero, imK_zero]
    · ring
    · linear_combination (a - b) * h
    all_goals ring
  exact sub_eq_zero.mp (congrArg QuaternionAlgebra.re (mul_self_eq_zero.mp hsq))

/-- The norm of the quaternion `(a + b i + c j + d k) / e` is `(a² + b² + c² + d²) / e²`. -/
theorem normSq_mk_div {K : Type*} [Field K] (a b c d e : K) :
    normSq (⟨a / e, b / e, c / e, d / e⟩ : ℍ[K]) = (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) / e ^ 2 := by
  simp only [normSq_def', div_pow, add_div]

/-- The norm of the quaternion `(a + b i + c j + d k) / 2` is `(a² + b² + c² + d²) / 4`. -/
theorem normSq_mk_div_two {K : Type*} [Field K] (a b c d : K) :
    normSq (⟨a / 2, b / 2, c / 2, d / 2⟩ : ℍ[K]) = (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) / 4 := by
  rw [normSq_mk_div]
  norm_num

/-- Multiplying two quaternions with coordinates scaled by `r` and `s` gives their product with
coordinates scaled by `r * s`. -/
theorem mk_div_mul_mk_div {K : Type*} [Field K] (p q : ℍ[K]) (r s : K) :
    (⟨p.re / r, p.imI / r, p.imJ / r, p.imK / r⟩ : ℍ[K]) *
        ⟨q.re / s, q.imI / s, q.imJ / s, q.imK / s⟩ =
      ⟨(p * q).re / (r * s), (p * q).imI / (r * s),
        (p * q).imJ / (r * s), (p * q).imK / (r * s)⟩ := by
  ext <;> simp only [re_mul, imI_mul, imJ_mul, imK_mul, div_mul_div_comm] <;> ring

/-- The product of two quaternions with `ℤ`-coordinates scaled by `r` and `s` has `ℤ`-coordinates
scaled by `e` whenever `r * s = e`. -/
theorem exists_mk_div_mul_mk_div {K : Type*} [Field K] {r s e : K} (hrs : r * s = e)
    (v w : Fin 4 → ℤ) :
    ∃ u : Fin 4 → ℤ, (⟨v 0 / r, v 1 / r, v 2 / r, v 3 / r⟩ : ℍ[K]) *
        ⟨w 0 / s, w 1 / s, w 2 / s, w 3 / s⟩ =
      ⟨u 0 / e, u 1 / e, u 2 / e, u 3 / e⟩ := by
  set x : ℍ[ℤ] := ⟨v 0, v 1, v 2, v 3⟩ * ⟨w 0, w 1, w 2, w 3⟩
  refine ⟨![x.re, x.imI, x.imJ, x.imK], ?_⟩
  rw [mk_div_mul_mk_div (⟨v 0, v 1, v 2, v 3⟩ : ℍ[K]) (⟨w 0, w 1, w 2, w 3⟩ : ℍ[K]) r s, hrs]
  ext <;> simp [x]

/-- An integer quaternion `x` with even coordinates gives a quaternion `x / (2 * r)` with
coordinates in `ℤ / r`. -/
theorem exists_mk_div_two_mul_eq {K : Type*} [Field K] [NeZero (2 : K)] (r : K) {x : ℍ[ℤ]}
    (hx : Even x.re ∧ Even x.imI ∧ Even x.imJ ∧ Even x.imK) :
    ∃ u : Fin 4 → ℤ, (⟨x.re / (2 * r), x.imI / (2 * r), x.imJ / (2 * r), x.imK / (2 * r)⟩ :
      ℍ[K]) = ⟨u 0 / r, u 1 / r, u 2 / r, u 3 / r⟩ := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩, ⟨d, hd⟩⟩ := hx
  refine ⟨![a, b, c, d], ?_⟩
  ext <;>
    simp only [ha, hb, hc, hd, Matrix.cons_val, ← two_mul, Int.cast_mul, Int.cast_ofNat] <;>
    by_cases hr : r = 0 <;>
    simp [hr, mul_div_mul_left _ _ (NeZero.ne (2 : K))]

/-- If the integer quaternion product of `v` and `w` has even coordinates, then the product of the
corresponding quaternions scaled by `r` and `s` has `ℤ`-coordinates scaled by `e` whenever
`r * s = 2 * e`. -/
theorem exists_mk_div_mul_mk_div_of_even_coords {K : Type*} [Field K] [NeZero (2 : K)]
    {r s e : K} (hrs : r * s = 2 * e) {v w : Fin 4 → ℤ}
    (hx : let x : ℍ[ℤ] := ⟨v 0, v 1, v 2, v 3⟩ * ⟨w 0, w 1, w 2, w 3⟩
      Even x.re ∧ Even x.imI ∧ Even x.imJ ∧ Even x.imK) :
    ∃ u : Fin 4 → ℤ, (⟨v 0 / r, v 1 / r, v 2 / r, v 3 / r⟩ : ℍ[K]) *
        ⟨w 0 / s, w 1 / s, w 2 / s, w 3 / s⟩ =
      ⟨u 0 / e, u 1 / e, u 2 / e, u 3 / e⟩ := by
  obtain ⟨u, hu⟩ := exists_mk_div_two_mul_eq e hx
  refine ⟨u, ?_⟩
  rw [mk_div_mul_mk_div (⟨v 0, v 1, v 2, v 3⟩ : ℍ[K]) (⟨w 0, w 1, w 2, w 3⟩ : ℍ[K]) r s, hrs,
    ← hu]
  ext <;> simp

end Quaternion
