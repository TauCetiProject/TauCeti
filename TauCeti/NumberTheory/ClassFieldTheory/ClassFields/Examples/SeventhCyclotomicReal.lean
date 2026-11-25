/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.ClassFields.RingClass.Field
public import TauCeti.NumberTheory.NumberField.Cyclotomic.SeventhCyclotomic.MaximalRealSubfield
public import TauCeti.NumberTheory.NumberField.Global.Orders.Discriminant
public import TauCeti.NumberTheory.NumberField.Global.Orders.Maximal

/-!
# The ring class field of the cubic field `ℚ(ζ₇)⁺`

Let `L` be a seventh cyclotomic field over `ℚ` and let `K = L⁺` be its maximal real subfield,
classically `ℚ(ζ₇ + ζ₇⁻¹)`, a cubic field of discriminant `49`. Because `ringClassField` and
`ringClassArtinEquiv` carry no quadratic hypothesis on the base field, they apply directly to
`maximalNumberFieldOrder (maximalRealSubfield L)`. Since `𝓞 (maximalRealSubfield L)` is a principal
ideal domain of class number one, the Picard group of its maximal order is trivial, so
`Gal(ringClassField O / L⁺)` is trivial and `ringClassField O = hilbertClassField L⁺ = ⊥`.

## Main results

In namespace `TauCeti.ClassFieldTheory`:

* `discr_maximalNumberFieldOrder_maximalRealSubfield_seven`,
  `card_pic_maximalNumberFieldOrder_maximalRealSubfield_seven`,
  `subsingleton_pic_maximalNumberFieldOrder_maximalRealSubfield_seven`: the maximal order of
  `ℚ(ζ₇)⁺` has discriminant `49` and trivial Picard group.
* `subsingleton_gal_ringClassField_maximalNumberFieldOrder_maximalRealSubfield_seven`,
  `ringClassField_maximalNumberFieldOrder_maximalRealSubfield_seven`,
  `hilbertClassField_maximalRealSubfield_seven`,
  `finrank_ringClassField_maximalNumberFieldOrder_maximalRealSubfield_seven`:
  `Gal(ringClassField O / L⁺)` is trivial and `ringClassField O = hilbertClassField L⁺ = ⊥`.

## References

* G. S. Kopp and J. C. Lagarias, *Ray class groups and ray class fields for orders of number
  fields*, Ess. Number Th. 4 (2025), arXiv:2212.09177v3, Theorem 1.1.
* L. C. Washington, *Introduction to Cyclotomic Fields*, Proposition 2.16 and Chapter 11 §1.
-/

public noncomputable section

open NumberField TauCeti.GlobalNumberFields TauCeti.GlobalNumberFields.NumberFieldOrder
  TauCeti.NumberField

namespace TauCeti.ClassFieldTheory

section MaximalRealSevenOrder

variable (L : Type*) [Field L] [NumberField L] [IsCyclotomicExtension {7} ℚ L]

/-- The maximal order of `ℚ(ζ₇)⁺ = ℚ(ζ₇ + ζ₇⁻¹)` has discriminant `49`. -/
theorem discr_maximalNumberFieldOrder_maximalRealSubfield_seven :
    (maximalNumberFieldOrder (maximalRealSubfield L)).discr = 49 := by
  rw [discr_maximal, discr_maximalRealSubfield_seven L]

/-- **The Picard group of the maximal order of `ℚ(ζ₇ + ζ₇⁻¹)` has order `1`.** -/
theorem card_pic_maximalNumberFieldOrder_maximalRealSubfield_seven :
    Nat.card (Pic (maximalNumberFieldOrder (maximalRealSubfield L))) = 1 := by
  rw [card_pic_maximalNumberFieldOrder, classNumber_maximalRealSubfield_seven L]

/-- **The maximal order of `ℚ(ζ₇)⁺` has trivial Picard group.** -/
theorem subsingleton_pic_maximalNumberFieldOrder_maximalRealSubfield_seven :
    Subsingleton (Pic (maximalNumberFieldOrder (maximalRealSubfield L))) :=
  have := isPrincipalIdealRing_maximalRealSubfield_seven L
  subsingleton_pic_maximalNumberFieldOrder (maximalRealSubfield L)

end MaximalRealSevenOrder

section MaximalRealSevenField

variable (L : Type) [Field L] [NumberField L] [IsCyclotomicExtension {7} ℚ L]

/-- **The Galois group `Gal(ringClassField (𝓞 L⁺) / L⁺)` is trivial** for the cubic field
`L⁺ = ℚ(ζ₇ + ζ₇⁻¹)`. -/
theorem subsingleton_gal_ringClassField_maximalNumberFieldOrder_maximalRealSubfield_seven :
    Subsingleton Gal(ringClassField (maximalNumberFieldOrder (maximalRealSubfield L))/
      maximalRealSubfield L) :=
  have := subsingleton_pic_maximalNumberFieldOrder_maximalRealSubfield_seven L
  subsingleton_gal_ringClassField (maximalNumberFieldOrder (maximalRealSubfield L))

/-- **The ring class field of the maximal order of `ℚ(ζ₇)⁺` is trivial (`⊥`).** -/
theorem ringClassField_maximalNumberFieldOrder_maximalRealSubfield_seven :
    ringClassField (maximalNumberFieldOrder (maximalRealSubfield L)) = ⊥ :=
  have := subsingleton_pic_maximalNumberFieldOrder_maximalRealSubfield_seven L
  ringClassField_eq_bot (maximalNumberFieldOrder (maximalRealSubfield L))

/-- **The Hilbert class field of `ℚ(ζ₇ + ζ₇⁻¹)` is `⊥`.** -/
@[simp]
theorem hilbertClassField_maximalRealSubfield_seven :
    hilbertClassField (maximalRealSubfield L) = ⊥ :=
  have := isPrincipalIdealRing_maximalRealSubfield_seven L
  hilbertClassField_eq_bot (maximalRealSubfield L)

/-- **The ring class field of the maximal order of `ℚ(ζ₇ + ζ₇⁻¹)` has degree `1` over
`ℚ(ζ₇ + ζ₇⁻¹)`.** -/
theorem finrank_ringClassField_maximalNumberFieldOrder_maximalRealSubfield_seven :
    Module.finrank (maximalRealSubfield L)
      (ringClassField (maximalNumberFieldOrder (maximalRealSubfield L))) = 1 := by
  rw [finrank_ringClassField, card_pic_maximalNumberFieldOrder_maximalRealSubfield_seven L]

end MaximalRealSevenField

end TauCeti.ClassFieldTheory
