/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Module.FinitePresentation
public import TauCeti.CategoryTheory.Exact.Abelian
public import TauCeti.CategoryTheory.Exact.Stable.Basic

/-!
# Finitely presented modules modulo projectives

The finitely presented modules form a full subcategory of the projective stable category of
`ModuleCat A`, whose morphisms are module maps modulo those factoring through a projective module.

## Main definitions

* `TauCeti.FinitelyPresentedStableModule`: finitely presented modules in the projective stable
  quotient.
-/

public section

namespace TauCeti

open CategoryTheory

universe u v

variable (A : Type u) [Ring A]

/-- Finitely presented modules, with morphisms taken modulo maps through projective modules.
This is a full subcategory of the projective stable quotient of `ModuleCat`. -/
abbrev FinitelyPresentedStableModule :=
  ObjectProperty.FullSubcategory
    (fun M : (ExactStructure.abelian (ModuleCat.{v} A)).ProjectiveStableCategory ↦
      Module.FinitePresentation A M.as)

end TauCeti
