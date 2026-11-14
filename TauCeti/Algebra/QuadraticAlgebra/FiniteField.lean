/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.FieldTheory.Finite.Basic
import TauCeti.FieldTheory.Finite.Card
import TauCeti.FieldTheory.Finite.EulerCriterion

/-!
# Frobenius on a quadratic algebra over a finite field

Let `F` be a finite field with `Q = Nat.card F` elements and let `r ∈ F`. On
`A = QuadraticAlgebra F r 0` the `Q`-th power map is Mathlib's Frobenius `F`-algebra endomorphism
`FiniteField.frobeniusAlgHom F A`, so it is determined by its value at the generator `ω`. For odd
`Q` this value is `ω ^ Q = r ^ (Q / 2) • ω` (`QuadraticAlgebra.omega_pow_of_odd`), and Euler's
criterion (`FiniteField.isSquare_iff`, `TauCeti.FiniteField.pow_card_div_two_eq_neg_one`)
evaluates `r ^ (Q / 2)` as `-1` or `1` according as `r` is a nonsquare or a nonzero square.
This gives the three Frobenius identities:

* `QuadraticAlgebra.pow_card_eq_star`: if `r` is not a square, then `A` is a quadratic field
  extension of `F` and `z ^ Q = star z`; in particular `ω ^ Q = -ω`
  (`QuadraticAlgebra.omega_pow_card_eq_neg`). A nonsquare forces `Q` odd, since in
  characteristic two every element is a square.
* `QuadraticAlgebra.pow_card_eq_self_of_square`: if `Q` is odd and `r` is a nonzero square, then
  `z ^ Q = z`. Oddness is needed: over `𝔽₂` with `r = 1` the element `ω + 1` is a nonzero
  nilpotent, so the `Q`-th power map is not the identity.
* `QuadraticAlgebra.pow_card_eq_algebraMap_re`: if `r = 0`, then `z ^ Q = z.re`, for every `Q`.

Conversely, if `r` is a square then `ω ^ Q ≠ star ω` (`QuadraticAlgebra.omega_pow_card_ne_star`),
so `z ^ Q = star z` holds for every `z` exactly when `r` is not a square
(`QuadraticAlgebra.forall_pow_card_eq_star_iff`).

In the inert case the identity `z ^ Q = star z` turns Mathlib's `algebraMap_trace_eq_add_star`
and `algebraMap_norm_eq_mul_star` into `trace z = z + z ^ Q` and `norm z = z * z ^ Q`; the fixed
points of the `Q`-th power map are exactly the elements of `F`, and the map is an involution.
Since an `F`-algebra endomorphism of the quadratic field `F(√r)` is the identity or conjugation
(`QuadraticAlgebra.algHom_eq_id_or_eq_starAlgEquiv`, in `TauCeti.Algebra.QuadraticAlgebra.Star`),
the `Q`-th power map is the unique nontrivial one.

## References

* J. S. Milne, *Algebraic Number Theory*, Example 7.54: the Frobenius generates the Galois group
  of a finite extension of a finite field.
-/

public section

namespace QuadraticAlgebra

open TauCeti.FiniteField

/-- For odd `n`, the `n`-th power of the generator of `R[√r]` is `r ^ (n / 2) • ω`. -/
theorem omega_pow_of_odd {R : Type*} [CommSemiring R] {r : R} {n : ℕ} (hn : Odd n) :
    (ω : QuadraticAlgebra R r 0) ^ n = r ^ (n / 2) • ω := by
  conv_lhs => rw [← Nat.two_mul_div_two_add_one_of_odd hn]
  rw [pow_succ, pow_mul, sq, omega_mul_omega_eq_algebraMap, map_zero, zero_mul, add_zero,
    ← map_pow, ← Algebra.smul_def]

variable {F : Type*} [Field F] [Finite F]

/-- The `Q`-th power map fixes the coordinates, since it is an `F`-algebra endomorphism
(`FiniteField.frobeniusAlgHom`): `(x + yω) ^ Q = x + y ω ^ Q`. -/
theorem pow_card_eq_re_smul_add_im_smul {a b : F} (z : QuadraticAlgebra F a b) :
    z ^ Nat.card F = z.re • 1 + z.im • ω ^ Nat.card F := by
  have := Fintype.ofFinite F
  have hf (w : QuadraticAlgebra F a b) :
      w ^ Nat.card F = FiniteField.frobeniusAlgHom F (QuadraticAlgebra F a b) w := by
    simp [Nat.card_eq_fintype_card]
  rw [hf, hf ω]
  conv_lhs => rw [← re_smul_add_im_smul z]
  rw [map_add, map_smul, map_smul, map_one]

variable {r : F}

/-- For odd `Q = Nat.card F`, the `Q`-th power map fixes the first coordinate and multiplies the
second by `r ^ (Q / 2)`. -/
theorem pow_card_eq_mk (hodd : Odd (Nat.card F)) (z : QuadraticAlgebra F r 0) :
    z ^ Nat.card F = ⟨z.re, r ^ (Nat.card F / 2) * z.im⟩ := by
  rw [pow_card_eq_re_smul_add_im_smul, omega_pow_of_odd hodd]
  ext <;> simp [mul_comm]

/-- **Frobenius at the generator in the inert case.** For a nonsquare `r`, `ω ^ Q = -ω`. -/
theorem omega_pow_card_eq_neg (hr : ¬IsSquare r) :
    (ω : QuadraticAlgebra F r 0) ^ Nat.card F = -ω := by
  rw [omega_pow_of_odd (odd_card_of_not_isSquare hr), pow_card_div_two_eq_neg_one hr,
    neg_one_smul]

/-- **Frobenius is conjugation in the inert case.** Over a finite field `F` with `Q` elements and
a nonsquare `r`, every element of the quadratic field `F(√r)` satisfies `z ^ Q = star z`. -/
theorem pow_card_eq_star (hr : ¬IsSquare r) (z : QuadraticAlgebra F r 0) :
    z ^ Nat.card F = star z := by
  rw [pow_card_eq_mk (odd_card_of_not_isSquare hr), pow_card_div_two_eq_neg_one hr]
  ext <;> simp

/-- **Frobenius is the identity in the split case.** Over a finite field of odd cardinality `Q`
and for a nonzero square `r`, the algebra `QuadraticAlgebra F r 0` is `F × F`
(`QuadraticAlgebra.algEquivProdOfSq`) and every element satisfies `z ^ Q = z`. -/
@[simp] theorem pow_card_eq_self_of_square (hodd : Odd (Nat.card F)) (hr : IsSquare r) (hr0 : r ≠ 0)
    (z : QuadraticAlgebra F r 0) : z ^ Nat.card F = z := by
  have := Fintype.ofFinite F
  have h : r ^ (Nat.card F / 2) = 1 := by
    rw [Nat.card_eq_fintype_card]
    exact (FiniteField.isSquare_iff (ringChar_ne_two_of_odd_card hodd) hr0).mp hr
  rw [pow_card_eq_mk hodd, h, one_mul]

/-- **Frobenius in the repeated-root case.** In `QuadraticAlgebra F 0 0`, where `ω ^ 2 = 0`,
every element satisfies `z ^ Q = z.re`, for every finite field `F`. -/
@[simp] theorem pow_card_eq_algebraMap_re (z : QuadraticAlgebra F 0 0) :
    z ^ Nat.card F = algebraMap F _ z.re := by
  have := Fintype.ofFinite F
  have hω : (ω : QuadraticAlgebra F 0 0) ^ Nat.card F = 0 := by
    rw [← Nat.sub_add_cancel Finite.one_lt_card, pow_add, sq, omega_mul_omega_eq_algebraMap]
    simp
  rw [pow_card_eq_re_smul_add_im_smul, hω, smul_zero, add_zero, Algebra.algebraMap_eq_smul_one]

/-- **Frobenius is not conjugation outside the inert case.** If `r` is a square in `F`, then
`ω ^ Q ≠ star ω`: the power `ω ^ Q` is the scalar `0` when `r = 0`, the scalar `r ^ (Q / 2)` when
`Q` is even, and `ω` when `Q` is odd and `r ≠ 0`, while `star ω = -ω` has second coordinate
`-1 ≠ 1`. -/
theorem omega_pow_card_ne_star (hr : IsSquare r) :
    (ω : QuadraticAlgebra F r 0) ^ Nat.card F ≠ star ω := by
  intro h
  have him := congrArg im h
  rw [im_star, im_omega] at him
  by_cases hr0 : r = 0
  · subst hr0
    rw [pow_card_eq_algebraMap_re] at him
    simp at him
  rcases Nat.even_or_odd (Nat.card F) with heven | hodd
  · -- `ω ^ Q = (ω ^ 2) ^ (Q / 2)` is the scalar `r ^ (Q / 2)`, whose second coordinate is `0`.
    rw [← Nat.two_mul_div_two_of_even heven, pow_mul] at him
    simp [sq, omega_mul_omega_eq_algebraMap, ← map_pow] at him
  · rw [pow_card_eq_self_of_square hodd hr hr0, im_omega] at him
    exact Ring.two_ne_zero (ringChar_ne_two_of_odd_card hodd) (by linear_combination him)

/-- **Frobenius is conjugation exactly in the inert case.** Over a finite field `F` with `Q`
elements, every `z ∈ QuadraticAlgebra F r 0` satisfies `z ^ Q = star z` exactly when `r` is not a
square. -/
theorem forall_pow_card_eq_star_iff :
    (∀ z : QuadraticAlgebra F r 0, z ^ Nat.card F = star z) ↔ ¬IsSquare r :=
  ⟨fun h hr ↦ omega_pow_card_ne_star hr (h ω), pow_card_eq_star⟩

/-- In the inert case the Frobenius algebra endomorphism is conjugation. -/
theorem frobeniusAlgHom_eq_starAlgEquiv [Fintype F] (hr : ¬IsSquare r) :
    FiniteField.frobeniusAlgHom F (QuadraticAlgebra F r 0) =
      (starAlgEquiv : QuadraticAlgebra F r 0 ≃ₐ[F] _).toAlgHom := by
  ext1
  simp [← Nat.card_eq_fintype_card, pow_card_eq_star hr]

/-- In the inert case the trace is `z + z ^ Q`. -/
theorem algebraMap_trace_eq_add_pow_card (hr : ¬IsSquare r) (z : QuadraticAlgebra F r 0) :
    algebraMap F _ (trace z) = z + z ^ Nat.card F := by
  rw [pow_card_eq_star hr, algebraMap_trace_eq_add_star]

/-- In the inert case the norm is `z * z ^ Q`. -/
theorem algebraMap_norm_eq_mul_pow_card (hr : ¬IsSquare r) (z : QuadraticAlgebra F r 0) :
    algebraMap F _ (norm z) = z * z ^ Nat.card F := by
  rw [pow_card_eq_star hr, algebraMap_norm_eq_mul_star]

/-- In the inert case the `Q`-th power map is an involution. -/
@[simp] theorem pow_card_pow_card (hr : ¬IsSquare r) (z : QuadraticAlgebra F r 0) :
    (z ^ Nat.card F) ^ Nat.card F = z := by
  rw [pow_card_eq_star hr, pow_card_eq_star hr, star_star]

/-- In the inert case the fixed points of the `Q`-th power map are the elements with zero
second coordinate. -/
theorem pow_card_eq_self_iff_im_eq_zero (hr : ¬IsSquare r) {z : QuadraticAlgebra F r 0} :
    z ^ Nat.card F = z ↔ z.im = 0 := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero
    (ringChar_ne_two_of_odd_card (odd_card_of_not_isSquare hr))
  rw [pow_card_eq_star hr, QuadraticAlgebra.ext_iff]
  simp only [re_star, zero_mul, add_zero, im_star, true_and, neg_eq_iff_add_eq_zero, ← two_mul,
    mul_eq_zero, h2, false_or]

/-- In the inert case the fixed points of the `Q`-th power map are exactly the elements of `F`. -/
theorem pow_card_eq_self_iff_mem_range (hr : ¬IsSquare r) {z : QuadraticAlgebra F r 0} :
    z ^ Nat.card F = z ↔ z ∈ Set.range (algebraMap F (QuadraticAlgebra F r 0)) := by
  rw [pow_card_eq_self_iff_im_eq_zero hr]
  refine ⟨fun h ↦ ⟨z.re, by ext <;> simp [h]⟩, ?_⟩
  rintro ⟨x, rfl⟩
  simp

end QuadraticAlgebra
