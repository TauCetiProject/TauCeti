/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.CMField
public import TauCeti.NumberTheory.NumberField.ComplexConjugation.Basic

/-!
# Complex conjugation on a CM field is place-independent

`TauCeti/NumberTheory/NumberField/ComplexConjugation/Basic.lean` attaches a conjugation
`complexConjugationAt K w hw` to a complex place `w` of `L` lying above a real place of `K`. The
place is genuinely part of the input: in a general Galois extension the elements attached to
different ramified places are conjugate (`complexConjugationAt_smul`), and conjugate elements
can differ.

A CM field is a case where that dependence disappears. If `K` is CM, with maximal real
subfield `K⁺`, then `K / K⁺` is a totally complex quadratic extension, so

* every infinite place of `K` is ramified over `K⁺` — the hypothesis `hw` is automatic
  (`isRamified_maximalRealSubfield`), and
* the conjugation attached to any place is Mathlib's `IsCMField.complexConj`
  (`complexConj_eq_complexConjugationAt`),

hence any two places give the same element
(`complexConjugationAt_eq_complexConjugationAt`). This is what lets a CM field carry a
place-free complex conjugation, and Mathlib's `IsCMField.complexConj` is the element it names:
on a CM field the place index may simply be dropped, and any statement about
`complexConjugationAt` there transfers to `complexConj`.

## Main results

* `TauCeti.NumberField.isRamified_maximalRealSubfield`: on a CM field every infinite place is
  ramified over the maximal real subfield.
* `TauCeti.NumberField.complexConj_eq_complexConjugationAt`: the conjugation at any place is
  `IsCMField.complexConj`.
* `TauCeti.NumberField.complexConjugationAt_eq_complexConjugationAt`: consequently it does not
  depend on the place.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter I, §12.
-/

public section

open NumberField NumberField.InfinitePlace

namespace TauCeti.NumberField

variable (K : Type*) [Field K] [NumberField K] [NumberField.IsCMField K]

local notation3 "K⁺" => NumberField.maximalRealSubfield K

/-- **On a CM field every infinite place is ramified over the maximal real subfield**, so the
ramification hypothesis of `complexConjugationAt` is automatic there. -/
theorem isRamified_maximalRealSubfield (w : InfinitePlace K) : w.IsRamified K⁺ := by
  rw [isRamified_iff]
  exact ⟨IsTotallyComplex.isComplex w, IsTotallyReal.isReal _⟩

/-- **On a CM field the conjugation at any place is `IsCMField.complexConj`.** The simp normal
form is the canonical `complexConj`, so the place-dependent `complexConjugationAt` rewrites to
it. -/
@[simp ←]
theorem complexConj_eq_complexConjugationAt (w : InfinitePlace K) :
    NumberField.IsCMField.complexConj K =
      complexConjugationAt K⁺ w (isRamified_maximalRealSubfield K w) :=
  eq_complexConjugationAt _ _ (NumberField.IsCMField.isConj_complexConj K w.embedding)

/-- **On a CM field the conjugation does not depend on the place.** In general two ramified
places give conjugate elements, which need not be equal. -/
theorem complexConjugationAt_eq_complexConjugationAt (w w' : InfinitePlace K) :
    complexConjugationAt K⁺ w (isRamified_maximalRealSubfield K w) =
      complexConjugationAt K⁺ w' (isRamified_maximalRealSubfield K w') := by
  rw [← complexConj_eq_complexConjugationAt, ← complexConj_eq_complexConjugationAt]

end TauCeti.NumberField

end
