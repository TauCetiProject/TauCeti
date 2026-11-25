/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.ClassFields.RingClass.Field
public import TauCeti.NumberTheory.NumberField.Cyclotomic.SeventhCyclotomic.MaximalRealSubfield

/-!
# The ring class field of the cubic field `ℚ(ζ₇)⁺`

Let `L` be a seventh cyclotomic field over `ℚ` and let `K = L⁺` be its maximal real subfield,
classically `ℚ(ζ₇ + ζ₇⁻¹)`, a cubic field of discriminant `49`. It has class number one
(`TauCeti.NumberField.classNumber_maximalRealSubfield_seven`), so the ring class field of its
maximal order, which is the Hilbert class field, is `K` itself, and the Picard group of the maximal
order is trivial.

The ring class field `ringClassField O` is defined for an order `O` in a number field of any
degree, and this is an example in degree three.

## Main results

* `TauCeti.ClassFieldTheory.ringClassField_maximalNumberFieldOrder_maximalRealSubfield_seven`:
  the ring class field of the maximal order of `ℚ(ζ₇)⁺` is `ℚ(ζ₇)⁺`.
* `TauCeti.ClassFieldTheory.subsingleton_pic_maximalNumberFieldOrder_maximalRealSubfield_seven`:
  the Picard group of that order is trivial.

## References

* G. S. Kopp and J. C. Lagarias, *Class Field Theory for Orders of Number Fields*, Theorem 1.1.
* L. C. Washington, *Introduction to Cyclotomic Fields*, Chapter 11 §1.
-/

public section

open NumberField TauCeti.GlobalNumberFields TauCeti.GlobalNumberFields.NumberFieldOrder

namespace TauCeti.ClassFieldTheory

variable (L : Type) [Field L] [NumberField L] [IsCyclotomicExtension {7} ℚ L]

/-- **The ring class field of the maximal order of `ℚ(ζ₇)⁺` is trivial.** The maximal real
subfield of a seventh cyclotomic field has class number one, so its ring class field at the
maximal order is the field itself. -/
theorem ringClassField_maximalNumberFieldOrder_maximalRealSubfield_seven :
    ringClassField (maximalNumberFieldOrder (maximalRealSubfield L)) = ⊥ := by
  rw [ringClassField_maximalNumberFieldOrder, hilbertClassField_eq_bot_iff]
  exact TauCeti.NumberField.classNumber_maximalRealSubfield_seven L

/-- **The maximal order of `ℚ(ζ₇)⁺` has trivial Picard group**, read through ring-class
reciprocity `Pic O ≃* Gal(ringClassField O / K)`. -/
theorem subsingleton_pic_maximalNumberFieldOrder_maximalRealSubfield_seven :
    Subsingleton (Pic (maximalNumberFieldOrder (maximalRealSubfield L))) :=
  (ringClassField_eq_bot_iff _).1
    (ringClassField_maximalNumberFieldOrder_maximalRealSubfield_seven L)

end TauCeti.ClassFieldTheory
