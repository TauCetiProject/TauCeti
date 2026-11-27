/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.SingleObj
public import TauCeti.CategoryTheory.VonNeumannRegular.Basic
public import TauCeti.RingTheory.VonNeumannRegular.Basic

/-!
# Von Neumann regularity for one-object categories

The one-object category of a monoid is von Neumann regular exactly when the monoid is.
-/

public section

namespace TauCeti

open CategoryTheory

/-- The one-object category of a monoid is von Neumann regular exactly when the monoid is. -/
@[simp]
theorem isVonNeumannRegularCategory_singleObj_iff (R : Type*) [Monoid R] :
    IsVonNeumannRegularCategory (SingleObj R) ↔ IsVonNeumannRegularRing R := by
  constructor
  · intro h
    constructor
    intro a
    obtain ⟨b, hb⟩ := h.exists_comp_comp_eq_self
      (X := SingleObj.star R) (Y := SingleObj.star R) a
    exact ⟨b, by simpa only [SingleObj.comp_as_mul, mul_assoc] using hb⟩
  · intro h
    constructor
    intro X Y f
    obtain ⟨g, hg⟩ := h.exists_mul_mul_eq_self f
    exact ⟨g, by simpa only [SingleObj.comp_as_mul, mul_assoc] using hg⟩

/-- The one-object category of a von Neumann regular monoid is von Neumann regular. -/
instance (R : Type*) [Monoid R] [IsVonNeumannRegularRing R] :
    IsVonNeumannRegularCategory (SingleObj R) :=
  (isVonNeumannRegularCategory_singleObj_iff R).mpr inferInstance

end TauCeti
