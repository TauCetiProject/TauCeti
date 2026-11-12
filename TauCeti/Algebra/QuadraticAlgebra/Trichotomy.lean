/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Finite.Basic
public import TauCeti.Algebra.QuadraticAlgebra.DualNumber
public import TauCeti.Algebra.QuadraticAlgebra.Split
import Mathlib.RingTheory.Nilpotent.Basic

/-!
# The trichotomy for quadratic algebras over a field

Let `K` be a field and `r ∈ K`. The algebra `A = QuadraticAlgebra K r 0 = K[X]/(X² - r)` has
one of three shapes, according as `X² - r` has two distinct roots, none, or a double root:

* if `r` is a nonzero square and `2 ≠ 0`, then `A ≃ₐ[K] K × K` (`algEquivProdOfSq`);
* if `r` is not a square, then `A` is a field (Mathlib's `Field` instance under
  `Fact (¬ IsSquare r)`);
* if `r = 0`, then `A ≃ₐ[K] K[ε]` (`algEquivDualNumber`), which is not reduced.

When `2 ≠ 0` these shapes are exhaustive (`trichotomy`), and this file characterizes each of
them by a condition on `r` (`nonempty_algEquiv_prod_iff`, `isField_iff_not_isSquare` and
`nonempty_algEquiv_dualNumber_iff`). Since these conditions are mutually exclusive, so are the
shapes. The invariants separating them are being a field and being reduced.

In characteristic two, if `r = u²` is a square then the change of generator `ω ↦ ω - u`
exhibits `A` as the dual numbers, and `A` is never a product of two copies of `K`. Over a
finite field every element is a square in characteristic two, which gives the finite-field
versions. Finally, `A` has `(Nat.card K)²` elements.
-/

public section

open DualNumber

namespace QuadraticAlgebra

/-- A quadratic algebra has `(Nat.card R)²` elements, through its coordinates. -/
theorem natCard_eq {R : Type*} (a b : R) :
    Nat.card (QuadraticAlgebra R a b) = Nat.card R ^ 2 := by
  rw [Nat.card_congr (equivProd a b), Nat.card_prod, sq]

variable {K : Type*} [Field K] {r : K}

/-- `K[X]/(X² - r)` is a field exactly when `r` is not a square in `K`. Unlike the
discriminant criterion `isField_iff_not_isSquare_discr`, this needs no assumption on the
characteristic. -/
theorem isField_iff_not_isSquare : IsField (QuadraticAlgebra K r 0) ↔ ¬IsSquare r := by
  refine ⟨fun hfield ⟨u, hu⟩ ↦ ?_, fun h ↦ ?_⟩
  · have := hfield.isDomain
    have hmul : (ω - algebraMap K _ u) * (ω + algebraMap K _ u) =
        (0 : QuadraticAlgebra K r 0) := by
      ext <;> simp [hu]
    rcases mul_eq_zero.mp hmul with h | h <;> simpa using congr(im $h)
  · have : Fact (¬IsSquare r) := ⟨h⟩
    exact Field.toIsField _

/-- Over a field with `2 ≠ 0`, `K[X]/(X² - r)` splits as `K × K` exactly when `r` is a
nonzero square. -/
theorem nonempty_algEquiv_prod_iff [NeZero (2 : K)] :
    Nonempty (QuadraticAlgebra K r 0 ≃ₐ[K] K × K) ↔ IsSquare r ∧ r ≠ 0 := by
  refine ⟨fun ⟨e⟩ ↦ ⟨by_contra fun h ↦ ?_, fun hr ↦ ?_⟩, fun ⟨⟨u, hu⟩, _⟩ ↦ ?_⟩
  · have := (e.symm.toMulEquiv.isField (isField_iff_not_isSquare.mpr h)).isDomain
    exact false_of_nontrivial_of_product_domain K K
  · subst hr
    exact not_isReduced_of_double_root 0 (by simp) (by simp) (isReduced_of_injective e e.injective)
  · have hu0 : u ≠ 0 := by rintro rfl; simp_all
    let : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
    exact ⟨algEquivProdOfSq (Units.mk0 u hu0) (by simp [hu, sq])⟩

/-- Over a field with `2 ≠ 0`, `K[X]/(X² - r)` is the ring of dual numbers exactly when
`r = 0`. -/
theorem nonempty_algEquiv_dualNumber_iff [NeZero (2 : K)] :
    Nonempty (QuadraticAlgebra K r 0 ≃ₐ[K] K[ε]) ↔ r = 0 := by
  refine ⟨fun ⟨e⟩ ↦ by_contra fun hr ↦ ?_, fun hr ↦ by subst hr; exact ⟨algEquivDualNumber⟩⟩
  by_cases h : IsSquare r
  · obtain ⟨e'⟩ := nonempty_algEquiv_prod_iff.mpr ⟨h, hr⟩
    exact DualNumber.not_isReduced <|
      isReduced_of_injective (e.symm.trans e') (AlgEquiv.injective _)
  · exact DualNumber.not_isField <|
      e.symm.toMulEquiv.isField (isField_iff_not_isSquare.mpr h)

/-- Over a field with `2 ≠ 0`, `K[X]/(X² - r)` is a product of two copies of `K`, a field, or
the ring of dual numbers. By `nonempty_algEquiv_prod_iff`, `isField_iff_not_isSquare` and
`nonempty_algEquiv_dualNumber_iff`, exactly one case occurs. -/
theorem trichotomy [NeZero (2 : K)] (r : K) :
    Nonempty (QuadraticAlgebra K r 0 ≃ₐ[K] K × K) ∨ IsField (QuadraticAlgebra K r 0) ∨
      Nonempty (QuadraticAlgebra K r 0 ≃ₐ[K] K[ε]) := by
  rw [nonempty_algEquiv_prod_iff, isField_iff_not_isSquare, nonempty_algEquiv_dualNumber_iff]
  tauto

/-- In characteristic two, if `r = u²` is a square then `K[X]/(X² - r)` is the ring of dual
numbers: `X² - r = (X - u)²` and `ω - u` squares to zero. -/
theorem nonempty_algEquiv_dualNumber_of_isSquare_of_char_two [CharP K 2] (hr : IsSquare r) :
    Nonempty (QuadraticAlgebra K r 0 ≃ₐ[K] K[ε]) := by
  obtain ⟨u, hu⟩ := hr
  exact ⟨algEquivDualNumberOfDoubleRoot u
    (by rw [hu, CharTwo.neg_eq, sq]) (by rw [CharTwo.two_eq_zero, zero_mul])⟩

/-- In characteristic two, `K[X]/(X² - r)` is never `K × K`: it is the ring of dual numbers,
which is not reduced, when `r` is a square, and a field otherwise. -/
theorem isEmpty_algEquiv_prod_of_char_two [CharP K 2] (r : K) :
    IsEmpty (QuadraticAlgebra K r 0 ≃ₐ[K] K × K) := by
  refine ⟨fun e ↦ ?_⟩
  by_cases h : IsSquare r
  · obtain ⟨e'⟩ := nonempty_algEquiv_dualNumber_of_isSquare_of_char_two h
    exact DualNumber.not_isReduced <|
      isReduced_of_injective (e'.symm.trans e) (AlgEquiv.injective _)
  · have := (e.symm.toMulEquiv.isField (isField_iff_not_isSquare.mpr h)).isDomain
    exact false_of_nontrivial_of_product_domain K K

end QuadraticAlgebra

namespace FiniteField

open QuadraticAlgebra

variable {F : Type*} [Field F] [Finite F]

/-- Over a finite field of odd cardinality, `F[X]/(X² - r)` is a product of two copies of
`F`, a field, or the ring of dual numbers; see `QuadraticAlgebra.trichotomy`. -/
theorem quadraticAlgebra_trichotomy (hodd : Odd (Nat.card F)) (r : F) :
    Nonempty (QuadraticAlgebra F r 0 ≃ₐ[F] F × F) ∨ IsField (QuadraticAlgebra F r 0) ∨
      Nonempty (QuadraticAlgebra F r 0 ≃ₐ[F] F[ε]) := by
  have := Fintype.ofFinite F
  rw [Nat.card_eq_fintype_card] at hodd
  have : NeZero (2 : F) := ⟨Ring.two_ne_zero fun h ↦
    Nat.not_even_iff_odd.mpr hodd (Nat.even_iff.mpr (even_card_iff_char_two.mp h))⟩
  exact trichotomy r

/-- Over a finite field of even cardinality, `F[X]/(X² - r)` is always the ring of dual
numbers, since every element of `F` is a square. -/
theorem nonempty_quadraticAlgebra_algEquiv_dualNumber_of_even_card
    (heven : Even (Nat.card F)) (r : F) :
    Nonempty (QuadraticAlgebra F r 0 ≃ₐ[F] F[ε]) := by
  have := Fintype.ofFinite F
  have hchar : ringChar F = 2 := even_card_iff_char_two.mpr <| by
    simpa [Nat.card_eq_fintype_card, Nat.even_iff] using heven
  have : CharP F 2 := ringChar.eq_iff.mp hchar
  exact nonempty_algEquiv_dualNumber_of_isSquare_of_char_two (isSquare_of_char_two hchar r)

/-- Over a finite field of even cardinality, `F[X]/(X² - r)` is never `F × F`: the oddness
hypothesis of the split case cannot be dropped. -/
theorem isEmpty_quadraticAlgebra_algEquiv_prod_of_even_card
    (heven : Even (Nat.card F)) (r : F) :
    IsEmpty (QuadraticAlgebra F r 0 ≃ₐ[F] F × F) := by
  have := Fintype.ofFinite F
  have : CharP F 2 := ringChar.eq_iff.mp <| even_card_iff_char_two.mpr <| by
    simpa [Nat.card_eq_fintype_card, Nat.even_iff] using heven
  exact isEmpty_algEquiv_prod_of_char_two r

end FiniteField
