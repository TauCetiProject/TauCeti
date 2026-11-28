/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Abelian.GlobalDimension
public import TauCeti.CategoryTheory.Preadditive.ModCat.SingleObj

/-!
# Global dimension for one-object categories

The global dimension of a category of modules over a preadditive category recovers the usual
left global dimension when the source is the one-object category of an opposite ring.
-/

public section

open CategoryTheory

namespace TauCeti

universe u v

/-- The left global dimension of a ring agrees with the global dimension of modules over the
corresponding one-object preadditive category, in the same module universe. -/
theorem globalDimension_moduleCat_eq_singleObj (A : Type u) [Ring A] :
    Abelian.globalDimension (ModuleCat.{v} A) =
      Abelian.globalDimension (ModCat.{v} (SingleObj Aᵐᵒᵖ)) :=
  (moduleCatEquivModCat.{v} A).globalDimension_eq

end TauCeti
