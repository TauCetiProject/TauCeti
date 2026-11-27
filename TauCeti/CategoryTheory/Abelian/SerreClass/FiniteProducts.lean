/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.SerreClass.Basic
public import TauCeti.CategoryTheory.ObjectProperty.FiniteProducts

/-!
# Finite products in a Serre class

A Serre class is closed under finite products because binary biproducts are split extensions
and the empty product is a zero object.
-/

public section

namespace CategoryTheory.ObjectProperty

/-- A Serre class in an abelian category is closed under finite products. -/
instance IsSerreClass.isClosedUnderFiniteProducts {C : Type*} [Category* C] [Abelian C]
    (P : ObjectProperty C) [P.IsSerreClass] : P.IsClosedUnderFiniteProducts := by
  have : P.IsClosedUnderBinaryProducts :=
    P.isClosedUnderBinaryProducts_of_prop_biprod fun _ _ hX hY ↦ P.prop_biprod hX hY
  exact .mk'

end CategoryTheory.ObjectProperty
