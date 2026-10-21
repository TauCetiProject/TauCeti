/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.CategoryTheory.Preadditive.LeftExact

/-!
# Exactness of the inclusion of a full subcategory closed under kernels

Let `C` be a preadditive category with a zero object and finite products, and let
`P : ObjectProperty C` contain zero and be closed under finite products. If `P` is closed under
kernels (and `C` has them), the inclusion `P.ι : P.FullSubcategory ⥤ C` preserves finite limits;
dually, if `P` is closed under cokernels, `P.ι` preserves finite colimits. Thus finite limits and
colimits in the full subcategory are computed in `C`. In particular, when `C` is abelian and `P` is
closed under kernels, cokernels and finite products, `P.ι` is exact for Mathlib's inherited abelian
structure on `P.FullSubcategory` (`Mathlib.CategoryTheory.Abelian.Subcategory`).

These combine Mathlib's preservation of kernels and cokernels by `P.ι`
(`ObjectProperty.preservesKernels_ι`, `ObjectProperty.preservesCokernels_ι`) with the fact that an
additive functor preserving kernels (cokernels) preserves finite limits (colimits),
`Functor.preservesFiniteLimits_of_preservesKernels`.
-/

public section

namespace CategoryTheory.ObjectProperty

open Limits

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [HasFiniteProducts C]
  (P : ObjectProperty C) [P.ContainsZero] [P.IsClosedUnderFiniteProducts]

/-- The inclusion of a full subcategory containing zero and closed under finite products and
kernels preserves finite limits. -/
instance preservesFiniteLimits_ι [HasKernels C] [P.IsClosedUnderKernels] :
    PreservesFiniteLimits P.ι :=
  have := P.preservesKernels_ι
  -- The source category inherits biproducts and equalizers from its products and kernels.
  have : HasBinaryBiproducts P.FullSubcategory := .of_hasBinaryProducts
  have := Preadditive.hasEqualizers_of_hasKernels (C := P.FullSubcategory)
  Functor.preservesFiniteLimits_of_preservesKernels P.ι

/-- The inclusion of a full subcategory containing zero and closed under finite products and
cokernels preserves finite colimits. -/
instance preservesFiniteColimits_ι [HasCokernels C] [P.IsClosedUnderCokernels] :
    PreservesFiniteColimits P.ι :=
  have := P.preservesCokernels_ι
  -- The source category inherits finite coproducts (as biproducts) and coequalizers from its
  -- products and cokernels.
  have : HasBinaryBiproducts P.FullSubcategory := .of_hasBinaryProducts
  have : HasFiniteBiproducts P.FullSubcategory := .of_hasFiniteProducts
  have := Preadditive.hasCoequalizers_of_hasCokernels (C := P.FullSubcategory)
  Functor.preservesFiniteColimits_of_preservesCokernels P.ι

end CategoryTheory.ObjectProperty
