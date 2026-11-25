/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Preadditive.Projective.Basic

/-!
# Finite products of projective objects

In a category with zero morphisms and finite biproducts, the projective objects are closed under
finite products (`CategoryTheory.isClosedUnderFiniteProducts_isProjective`). This combines the
closure of `CategoryTheory.isProjective C` under isomorphisms, zero objects and binary products,
since a finite product is built from binary products and a terminal object.
-/

public section

open CategoryTheory Limits

namespace CategoryTheory

variable {C : Type*} [Category* C]

/-- In a category with zero morphisms and finite biproducts, a finite product of projective
objects is projective, since it is a biproduct. The empty biproduct is a zero object. -/
instance isClosedUnderFiniteProducts_isProjective [HasZeroMorphisms C] [HasFiniteBiproducts C] :
    (isProjective C).IsClosedUnderFiniteProducts :=
  have : HasBinaryBiproducts C := hasBinaryBiproducts_of_finite_biproducts C
  have : HasZeroObject C := hasZeroObject_of_hasTerminal_object
  .mk'

end CategoryTheory
