/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.RingTheory.Finiteness.Defs
public import TauCeti.CategoryTheory.Exact.Abelian
public import TauCeti.CategoryTheory.Exact.Stable.Injective

/-!
# Finitely generated modules modulo injectives

The finitely generated modules form a full subcategory of the injective stable category of
`ModuleCat A`, whose morphisms are module maps modulo those factoring through an injective module.

## Main definitions

* `TauCeti.FinitelyGeneratedInjectiveStableModule`: finitely generated modules in the injective
  stable quotient.
-/

public section

namespace TauCeti

open CategoryTheory

universe u v

variable (A : Type u) [Ring A]

/-- Finitely generated modules, with morphisms taken modulo maps through injective modules. This
is a full subcategory of the injective stable quotient of `ModuleCat`. -/
abbrev FinitelyGeneratedInjectiveStableModule :=
  ObjectProperty.FullSubcategory
    (fun M : (ExactStructure.abelian (ModuleCat.{v} A)).InjectiveStableCategory ↦
      Module.Finite A M.as)

end TauCeti
