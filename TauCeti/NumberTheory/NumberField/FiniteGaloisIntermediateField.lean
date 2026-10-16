/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.GaloisClosure
public import Mathlib.NumberTheory.NumberField.Basic

/-!
# Finite Galois subextensions of a number field are number fields

A finite Galois subextension `E` of an extension `L / K` of a number field `K` is a finite
extension of `K`, hence a number field. This is what lets the arithmetic of number fields (rings of
integers, adeles, ideles) be applied levelwise to the finite Galois subextensions of an infinite
extension such as a separable closure of `K`.

## Main results

* `FiniteGaloisIntermediateField.instNumberField`: a finite Galois subextension of an extension
  of a number field is a number field.
-/

public section

namespace FiniteGaloisIntermediateField

/-- **A finite Galois subextension of a number field is a number field.** -/
instance instNumberField {K L : Type*} [Field K] [NumberField K] [Field L] [Algebra K L]
    (E : FiniteGaloisIntermediateField K L) : NumberField E :=
  .of_module_finite K E

end FiniteGaloisIntermediateField
