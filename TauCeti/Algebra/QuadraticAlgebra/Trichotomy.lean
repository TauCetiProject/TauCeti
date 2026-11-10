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

When `2 ≠ 0` these shapes are mutually exclusive, and this file characterizes each of them by
a condition on `r`. The invariants separating them are being a field and being reduced.

Over a finite field `F` of odd cardinality the three cases are exhaustive
(`FiniteField.quadraticAlgebra_trichotomy`). In characteristic two every element of `F` is a
square, `r = u²`, and the change of generator `ω ↦ ω - u` exhibits `A` as the repeated-root
algebra; in particular it is never a product of two copies of `F`. Finally, `A` has
`(Nat.card F)²` elements.
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

private theorem not_isField_prod : ¬IsField (K × K) := fun h ↦ by
  have := h.isDomain
  simpa using mul_eq_zero.mp (show ((1, 0) : K × K) * (0, 1) = 0 by simp)

private theorem eps_ne_zero : (ε : K[ε]) ≠ 0 := fun h ↦
  one_ne_zero (α := K) (by simpa using congr(TrivSqZeroExt.snd $h))

private theorem not_isField_dualNumber : ¬IsField K[ε] := fun h ↦ by
  have := h.isDomain
  simpa [eps_ne_zero] using mul_eq_zero.mp (eps_mul_eps (R := K))

private theorem not_isReduced_dualNumber : ¬IsReduced K[ε] := fun _ ↦
  eps_ne_zero (IsNilpotent.eq_zero (x := (ε : K[ε])) ⟨2, eps_pow_two⟩)

/-- Over a field with `2 ≠ 0`, `K[X]/(X² - r)` splits as `K × K` exactly when `r` is a
nonzero square. -/
theorem nonempty_algEquiv_prod_iff [NeZero (2 : K)] :
    Nonempty (QuadraticAlgebra K r 0 ≃ₐ[K] K × K) ↔ IsSquare r ∧ r ≠ 0 := by
  refine ⟨fun ⟨e⟩ ↦ ⟨by_contra fun h ↦ ?_, fun hr ↦ ?_⟩, fun ⟨⟨u, hu⟩, hr⟩ ↦ ?_⟩
  · exact not_isField_prod <|
      e.symm.toMulEquiv.isField (isField_iff_not_isSquare.mpr h)
  · subst hr
    exact not_isReduced_dualNumber <|
      isReduced_of_injective ((e.symm.trans algEquivDualNumber).symm) (AlgEquiv.injective _)
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
    exact not_isReduced_dualNumber <|
      isReduced_of_injective (e.symm.trans e') (AlgEquiv.injective _)
  · exact not_isField_dualNumber <|
      e.symm.toMulEquiv.isField (isField_iff_not_isSquare.mpr h)

end QuadraticAlgebra

namespace FiniteField

open QuadraticAlgebra

variable {F : Type*} [Field F] [Finite F]

/-- Over a finite field of odd cardinality, `F[X]/(X² - r)` is a product of two copies of
`F`, a field, or the ring of dual numbers. By `nonempty_algEquiv_prod_iff`,
`isField_iff_not_isSquare` and `nonempty_algEquiv_dualNumber_iff`, exactly one case occurs. -/
theorem quadraticAlgebra_trichotomy (hodd : Odd (Nat.card F)) (r : F) :
    Nonempty (QuadraticAlgebra F r 0 ≃ₐ[F] F × F) ∨ IsField (QuadraticAlgebra F r 0) ∨
      Nonempty (QuadraticAlgebra F r 0 ≃ₐ[F] F[ε]) := by
  have := Fintype.ofFinite F
  rw [Nat.card_eq_fintype_card] at hodd
  have : NeZero (2 : F) := ⟨Ring.two_ne_zero fun h ↦
    Nat.not_even_iff_odd.mpr hodd (Nat.even_iff.mpr (even_card_iff_char_two.mp h))⟩
  rw [nonempty_algEquiv_prod_iff, isField_iff_not_isSquare, nonempty_algEquiv_dualNumber_iff]
  tauto

/-- Over a finite field of even cardinality, `F[X]/(X² - r)` is always the ring of dual
numbers: `r = u²` and `ω - u` squares to zero. -/
theorem nonempty_quadraticAlgebra_algEquiv_dualNumber_of_even_card
    (heven : Even (Nat.card F)) (r : F) :
    Nonempty (QuadraticAlgebra F r 0 ≃ₐ[F] F[ε]) := by
  have := Fintype.ofFinite F
  have hchar : ringChar F = 2 := even_card_iff_char_two.mpr <| by
    simpa [Nat.card_eq_fintype_card, Nat.even_iff] using heven
  have : CharP F 2 := ringChar.eq_iff.mp hchar
  obtain ⟨u, hu⟩ := isSquare_of_char_two hchar r
  exact ⟨algEquivDualNumberOfDoubleRoot u
    (by rw [hu, CharTwo.neg_eq, sq]) (by rw [CharTwo.two_eq_zero, zero_mul])⟩

/-- Over a finite field of even cardinality, `F[X]/(X² - r)` is never `F × F`: the oddness
hypothesis of the split case cannot be dropped. -/
theorem isEmpty_quadraticAlgebra_algEquiv_prod_of_even_card
    (heven : Even (Nat.card F)) (r : F) :
    IsEmpty (QuadraticAlgebra F r 0 ≃ₐ[F] F × F) := by
  obtain ⟨e⟩ := nonempty_quadraticAlgebra_algEquiv_dualNumber_of_even_card heven r
  exact ⟨fun e' ↦ not_isReduced (R := F) <|
    isReduced_of_injective ((algEquivDualNumber.trans e.symm).trans e') (AlgEquiv.injective _)⟩

end FiniteField
