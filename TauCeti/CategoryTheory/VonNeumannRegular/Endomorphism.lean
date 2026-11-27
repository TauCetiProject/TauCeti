/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Endomorphism
public import TauCeti.CategoryTheory.VonNeumannRegular.Basic
public import TauCeti.RingTheory.VonNeumannRegular.Basic

/-!
# Endomorphisms in von Neumann regular categories

The endomorphism monoid of any object in a von Neumann regular category is von Neumann regular.
-/

public section

namespace TauCeti.IsVonNeumannRegularCategory

open CategoryTheory

variable {C : Type*} [Category* C]

/-- Endomorphism monoids in a von Neumann regular category are von Neumann regular. -/
instance [IsVonNeumannRegularCategory C] (X : C) : IsVonNeumannRegularRing (End X) where
  exists_mul_mul_eq_self f := by
    obtain ⟨g, hg⟩ := exists_comp_comp_eq_self f.asHom
    exact ⟨End.of g, End.ext (by simpa only [End.mul_asHom, Category.assoc] using hg)⟩

end TauCeti.IsVonNeumannRegularCategory
