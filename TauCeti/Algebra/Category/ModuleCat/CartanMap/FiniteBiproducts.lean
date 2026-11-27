/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.CartanMap.Basic

/-!
# Finite biproducts of finitely generated projective modules

The full subcategory `TauCeti.finiteProjectiveModules R` of finitely generated projective
`R`-modules contains zero and is closed under binary products, so it has finite products. It is
preadditive, so these are finite biproducts.

## Main declarations

* `TauCeti.hasFiniteBiproducts_finiteProjectiveModules`: the instance
  `HasFiniteBiproducts (finiteProjectiveModules R).FullSubcategory`.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe u

variable (R : Type u) [Ring R]

/-- The finitely generated projective `R`-modules have finite biproducts, since they contain zero
and are closed under binary products. -/
instance hasFiniteBiproducts_finiteProjectiveModules :
    HasFiniteBiproducts (finiteProjectiveModules R).FullSubcategory :=
  have := hasFiniteProducts_of_has_binary_and_terminal
    (C := (finiteProjectiveModules R).FullSubcategory)
  .of_hasFiniteProducts

end TauCeti
