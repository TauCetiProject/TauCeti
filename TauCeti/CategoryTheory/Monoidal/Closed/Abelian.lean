/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-!
# Exactness of tensoring in a closed abelian monoidal category

In a closed monoidal category, tensoring on the left with a fixed object `M` is a left adjoint,
so it preserves cokernels and binary biproducts, hence is additive. In an abelian category, such
a functor preserves homology as soon as it preserves monomorphisms (Mathlib's
`Functor.preservesHomology_of_preservesMonos_and_cokernels`), hence preserves finite limits.
So `M` is flat, in the sense that `M ⊗ -` is exact, as soon as `M ⊗ -` preserves monomorphisms.

This applies to categories such as sheaves of modules, whose tensor product is right exact but
not exact in general.
-/

public section

open CategoryTheory Limits MonoidalCategory

namespace TauCeti

/-- In a closed abelian monoidal category, if tensoring on the left with `M` preserves
monomorphisms then it preserves finite limits: tensoring is right exact, having a right adjoint,
so preserving monomorphisms makes it exact. -/
lemma preservesFiniteLimits_tensorLeft_of_preservesMonomorphisms {C : Type*} [Category* C]
    [Abelian C] [MonoidalCategory C] [MonoidalClosed C] (M : C)
    [(tensorLeft M).PreservesMonomorphisms] : PreservesFiniteLimits (tensorLeft M) := by
  -- As a left adjoint, `tensorLeft M` preserves binary biproducts, so it is additive.
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (tensorLeft M)
  have := Functor.additive_of_preservesBinaryBiproducts (tensorLeft M)
  have := Functor.preservesHomology_of_preservesMonos_and_cokernels (tensorLeft M)
  exact Functor.preservesFiniteLimits_of_preservesHomology _

end TauCeti
