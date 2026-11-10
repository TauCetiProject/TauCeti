/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Frobenius on a quadratic algebra over a finite field

Let `F` be a finite field with `Q = Nat.card F` elements and let `r ∈ F`. On
`A = QuadraticAlgebra F r 0` the `Q`-th power map is Mathlib's Frobenius `F`-algebra endomorphism
`FiniteField.frobeniusAlgHom F A`, so it is determined by its value at the generator `ω`. For odd
`Q` this value is `ω ^ Q = r ^ (Q / 2) • ω`, and Euler's criterion
(`FiniteField.isSquare_iff`) evaluates `r ^ (Q / 2)` as `-1` or `1` according as `r` is a
nonsquare or a nonzero square. This gives the three Frobenius identities:

* `QuadraticAlgebra.pow_card_eq_star`: if `r` is not a square, then `A` is a quadratic field
  extension of `F` and `z ^ Q = star z`; in particular `ω ^ Q = -ω`
  (`QuadraticAlgebra.omega_pow_card_eq_neg`). A nonsquare forces `Q` odd, since in
  characteristic two every element is a square.
* `QuadraticAlgebra.pow_card_eq_self_of_square`: if `Q` is odd and `r` is a nonzero square, then
  `z ^ Q = z`. Oddness is needed: over `𝔽₂` with `r = 1` the element `ω + 1` is a nonzero
  nilpotent, so the `Q`-th power map is not the identity.
* `QuadraticAlgebra.pow_card_eq_algebraMap_re`: if `r = 0`, then `z ^ Q = z.re`, for every `Q`.

In the inert case the identity `z ^ Q = star z` turns Mathlib's `algebraMap_trace_eq_add_star`
and `algebraMap_norm_eq_mul_star` into `trace z = z + z ^ Q` and `norm z = z * z ^ Q`; the fixed
points of the `Q`-th power map are exactly the elements of `F`, and the map is an involution.
Over any field, an `F`-algebra endomorphism of the quadratic field `F(√r)` is the identity or
conjugation (`QuadraticAlgebra.algHom_eq_id_or_eq_starAlgEquiv`), so the `Q`-th power map is
the unique nontrivial one.

## References

* J. S. Milne, *Algebraic Number Theory*, Example 7.54: the Frobenius generates the Galois group
  of a finite extension of a finite field.
-/

public section

namespace QuadraticAlgebra

section AlgHom

variable {K : Type*} [Field K] {r : K}

/-- Over a field, an algebra endomorphism of the quadratic field `K(√r)`, for `r` not a square,
is the identity or conjugation: it sends `ω` to a square root of `r`, hence to `ω` or `-ω`. -/
theorem algHom_eq_id_or_eq_starAlgEquiv [Fact (¬IsSquare r)]
    (f : QuadraticAlgebra K r 0 →ₐ[K] QuadraticAlgebra K r 0) :
    f = AlgHom.id K _ ∨ f = (starAlgEquiv : QuadraticAlgebra K r 0 ≃ₐ[K] _).toAlgHom := by
  have hω : (ω : QuadraticAlgebra K r 0) * ω = algebraMap K _ r := by
    simp [omega_mul_omega_eq_algebraMap]
  have hf : f ω * f ω = algebraMap K _ r := by rw [← map_mul, hω, AlgHom.commutes]
  have h : (f ω - ω) * (f ω + ω) = 0 := by linear_combination hf - hω
  rcases mul_eq_zero.mp h with h | h
  · exact .inl (algHom_ext (by simpa [sub_eq_zero] using h))
  · refine .inr (algHom_ext ?_)
    rw [eq_neg_of_add_eq_zero_left h]
    ext <;> simp

end AlgHom

variable {F : Type*} [Field F] [Finite F] {r : F}

/-- The cardinality of a finite field in which some element is not a square is odd. -/
theorem _root_.FiniteField.odd_card_of_not_isSquare (hr : ¬IsSquare r) : Odd (Nat.card F) := by
  have := Fintype.ofFinite F
  rw [Nat.card_eq_fintype_card, Nat.odd_iff]
  exact FiniteField.odd_card_of_char_ne_two fun h ↦ hr (FiniteField.isSquare_of_char_two h r)

/-- In a finite field of odd cardinality the characteristic is not `2`. -/
theorem _root_.FiniteField.ringChar_ne_two_of_odd_card (hodd : Odd (Nat.card F)) :
    ringChar F ≠ 2 := by
  have := Fintype.ofFinite F
  rw [Nat.card_eq_fintype_card, Nat.odd_iff] at hodd
  intro h
  simp [FiniteField.even_card_of_char_two h] at hodd

/-- The `Q`-th power map fixes the coordinates, since it is an `F`-algebra endomorphism
(`FiniteField.frobeniusAlgHom`): `(x + yω) ^ Q = x + y ω ^ Q`. -/
theorem pow_card_eq_re_smul_add_im_smul (z : QuadraticAlgebra F r 0) :
    z ^ Nat.card F = z.re • 1 + z.im • ω ^ Nat.card F := by
  have := Fintype.ofFinite F
  have hf (w : QuadraticAlgebra F r 0) :
      w ^ Nat.card F = FiniteField.frobeniusAlgHom F (QuadraticAlgebra F r 0) w := by
    simp [Nat.card_eq_fintype_card]
  rw [hf, hf ω]
  conv_lhs => rw [← re_smul_add_im_smul z]
  rw [map_add, map_smul, map_smul, map_one]

omit [Finite F] in
/-- For odd `Q = Nat.card F`, the Frobenius sends the generator to `r ^ (Q / 2) • ω`. -/
theorem omega_pow_card (hodd : Odd (Nat.card F)) :
    (ω : QuadraticAlgebra F r 0) ^ Nat.card F = r ^ (Nat.card F / 2) • ω := by
  conv_lhs => rw [← Nat.two_mul_div_two_add_one_of_odd hodd]
  rw [pow_succ, pow_mul, sq, omega_mul_omega_eq_algebraMap, map_zero, zero_mul, add_zero,
    ← map_pow, ← Algebra.smul_def]

/-- For odd `Q = Nat.card F`, the `Q`-th power map fixes the first coordinate and multiplies the
second by `r ^ (Q / 2)`. -/
theorem pow_card_eq_mk (hodd : Odd (Nat.card F)) (z : QuadraticAlgebra F r 0) :
    z ^ Nat.card F = ⟨z.re, r ^ (Nat.card F / 2) * z.im⟩ := by
  rw [pow_card_eq_re_smul_add_im_smul, omega_pow_card hodd]
  ext <;> simp [mul_comm]

/-- Euler's criterion: a nonsquare `r` satisfies `r ^ (Nat.card F / 2) = -1`. -/
theorem pow_card_div_two_eq_neg_one (hr : ¬IsSquare r) : r ^ (Nat.card F / 2) = -1 := by
  have := Fintype.ofFinite F
  have hF := FiniteField.ringChar_ne_two_of_odd_card (FiniteField.odd_card_of_not_isSquare hr)
  have hr0 : r ≠ 0 := by rintro rfl; exact hr .zero
  rw [Nat.card_eq_fintype_card]
  exact (FiniteField.pow_dichotomy hF hr0).resolve_left
    fun h ↦ hr ((FiniteField.isSquare_iff hF hr0).mpr h)

/-- **Frobenius at the generator in the inert case.** For a nonsquare `r`, `ω ^ Q = -ω`. -/
theorem omega_pow_card_eq_neg (hr : ¬IsSquare r) :
    (ω : QuadraticAlgebra F r 0) ^ Nat.card F = -ω := by
  rw [omega_pow_card (FiniteField.odd_card_of_not_isSquare hr), pow_card_div_two_eq_neg_one hr,
    neg_one_smul]

/-- **Frobenius is conjugation in the inert case.** Over a finite field `F` with `Q` elements and
a nonsquare `r`, every element of the quadratic field `F(√r)` satisfies `z ^ Q = star z`. -/
theorem pow_card_eq_star (hr : ¬IsSquare r) (z : QuadraticAlgebra F r 0) :
    z ^ Nat.card F = star z := by
  rw [pow_card_eq_mk (FiniteField.odd_card_of_not_isSquare hr), pow_card_div_two_eq_neg_one hr]
  ext <;> simp

/-- **Frobenius is the identity in the split case.** Over a finite field of odd cardinality `Q`
and for a nonzero square `r`, the algebra `QuadraticAlgebra F r 0` is `F × F`
(`QuadraticAlgebra.algEquivProdOfSq`) and every element satisfies `z ^ Q = z`. -/
theorem pow_card_eq_self_of_square (hodd : Odd (Nat.card F)) (hr : IsSquare r) (hr0 : r ≠ 0)
    (z : QuadraticAlgebra F r 0) : z ^ Nat.card F = z := by
  have := Fintype.ofFinite F
  have h : r ^ (Nat.card F / 2) = 1 := by
    rw [Nat.card_eq_fintype_card]
    exact (FiniteField.isSquare_iff (FiniteField.ringChar_ne_two_of_odd_card hodd) hr0).mp hr
  rw [pow_card_eq_mk hodd, h, one_mul]

/-- **Frobenius in the repeated-root case.** In `QuadraticAlgebra F 0 0`, where `ω ^ 2 = 0`,
every element satisfies `z ^ Q = z.re`, for every finite field `F`. -/
theorem pow_card_eq_algebraMap_re (z : QuadraticAlgebra F 0 0) :
    z ^ Nat.card F = algebraMap F _ z.re := by
  have := Fintype.ofFinite F
  have hω : (ω : QuadraticAlgebra F 0 0) ^ Nat.card F = 0 := by
    rw [← Nat.sub_add_cancel Finite.one_lt_card, pow_add, sq, omega_mul_omega_eq_algebraMap]
    simp
  rw [pow_card_eq_re_smul_add_im_smul, hω, smul_zero, add_zero, Algebra.algebraMap_eq_smul_one]

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
theorem pow_card_pow_card (hr : ¬IsSquare r) (z : QuadraticAlgebra F r 0) :
    (z ^ Nat.card F) ^ Nat.card F = z := by
  rw [pow_card_eq_star hr, pow_card_eq_star hr, star_star]

/-- In the inert case the fixed points of the `Q`-th power map are the elements with zero
second coordinate. -/
theorem pow_card_eq_self_iff_im_eq_zero (hr : ¬IsSquare r) {z : QuadraticAlgebra F r 0} :
    z ^ Nat.card F = z ↔ z.im = 0 := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero
    (FiniteField.ringChar_ne_two_of_odd_card (FiniteField.odd_card_of_not_isSquare hr))
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
