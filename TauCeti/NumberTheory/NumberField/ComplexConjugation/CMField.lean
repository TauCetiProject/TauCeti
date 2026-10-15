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

An algebraic CM field is a case where that dependence disappears. If `K` is CM and algebraic over
`ℚ`, with maximal real subfield `K⁺`, then `K / K⁺` is a totally complex quadratic extension, so

* every infinite place of `K` is ramified over `K⁺` — the hypothesis `hw` is automatic
  (`NumberField.InfinitePlace.isRamified_maximalRealSubfield_iff`), and
* the conjugation attached to any place is Mathlib's `IsCMField.complexConj`
  (`complexConjugationAt_eq_complexConj`),

hence any two places give the same element
(`complexConjugationAt_eq_complexConjugationAt`). This is what lets a CM field carry a
place-free complex conjugation, and Mathlib's `IsCMField.complexConj` is the element it names:
on a CM field the place index may simply be dropped, and any statement about
`complexConjugationAt` there transfers to `complexConj`. The extension over `ℚ` need not be finite.

## Main results

* `TauCeti.NumberField.complexConjugationAt_eq_complexConj`: the conjugation at any place is
  `IsCMField.complexConj`.
* `TauCeti.NumberField.complexConjugationAt_eq_complexConjugationAt`: consequently it does not
  depend on the place.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter I, §12.
-/

public section

open NumberField NumberField.InfinitePlace

namespace TauCeti.NumberField

variable (K : Type*) [Field K] [CharZero K] [Algebra.IsIntegral ℚ K] [NumberField.IsCMField K]

local notation3 "K⁺" => NumberField.maximalRealSubfield K

/-- **On a CM field the conjugation at any place is `IsCMField.complexConj`.** The simp normal
form is the canonical `complexConj`, so the place-dependent `complexConjugationAt` rewrites to
it. -/
@[simp]
theorem complexConjugationAt_eq_complexConj (w : InfinitePlace K) (hw : w.IsRamified K⁺) :
    complexConjugationAt K⁺ w hw = NumberField.IsCMField.complexConj K :=
  (eq_complexConjugationAt _ _ (NumberField.IsCMField.isConj_complexConj K w.embedding)).symm

/-- **On a CM field the conjugation does not depend on the place.** In general two ramified
places give conjugate elements, which need not be equal. -/
theorem complexConjugationAt_eq_complexConjugationAt (w w' : InfinitePlace K)
    (hw : w.IsRamified K⁺) (hw' : w'.IsRamified K⁺) :
    complexConjugationAt K⁺ w hw = complexConjugationAt K⁺ w' hw' := by
  simp

end TauCeti.NumberField

end
