/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.ObjectProperty
public import TauCeti.CategoryTheory.Preadditive.Projective.Basic

/-!
# Closure of projective objects under retracts and finite biproducts

The object property `CategoryTheory.isProjective C` of being a projective object is stable under
retracts in any category, holds for a zero object when one exists, and is closed under binary and
finite products in any category with zero morphisms and binary or finite biproducts.

## Main declarations

* `CategoryTheory.isStableUnderRetracts_isProjective`: projective objects are stable under retracts.
* `CategoryTheory.containsZero_isProjective`: a zero object is projective, as `ContainsZero`.
* `CategoryTheory.isClosedUnderBinaryProducts_isProjective` and
  `CategoryTheory.isClosedUnderFiniteProducts_isProjective`: projective objects are closed under
  binary and finite products in the presence of binary or finite biproducts.
-/

public section

open CategoryTheory Limits

namespace CategoryTheory

variable {C : Type*} [Category* C]

/-- Projective objects are stable under retracts. -/
instance isStableUnderRetracts_isProjective : (isProjective C).IsStableUnderRetracts where
  of_retract h _ := h.projective

open scoped ZeroObject in
/-- `isProjective C` contains zero whenever `C` has a zero object. -/
instance containsZero_isProjective [HasZeroObject C] : (isProjective C).ContainsZero where
  exists_zero := ⟨0, isZero_zero C, inferInstance⟩

/-- In a category with zero morphisms and binary biproducts, projective objects are closed under
binary products. -/
instance isClosedUnderBinaryProducts_isProjective [HasZeroMorphisms C] [HasBinaryBiproducts C] :
    (isProjective C).IsClosedUnderBinaryProducts :=
  ObjectProperty.isClosedUnderBinaryProducts_of_prop_biprod _ fun _ _ _ _ ↦ inferInstance

section FiniteBiproducts

attribute [local instance] hasBinaryBiproducts_of_finite_biproducts
  hasFiniteProducts_of_hasFiniteBiproducts

/-- In a category with zero morphisms and finite biproducts, projective objects are closed under
finite products. -/
instance isClosedUnderFiniteProducts_isProjective [HasZeroMorphisms C] [HasFiniteBiproducts C] :
    (isProjective C).IsClosedUnderFiniteProducts :=
  .mk'

end FiniteBiproducts

end CategoryTheory
