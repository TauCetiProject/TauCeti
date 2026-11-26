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
# Full subcategories closed under kernels or cokernels

Let `C` be a category with zero morphisms, and let `P : ObjectProperty C` be nonempty. If `P` is
closed under kernels (or under cokernels), then `P` is closed under isomorphisms
(`CategoryTheory.ObjectProperty.isClosedUnderIsomorphisms_of_isClosedUnderKernels`,
`CategoryTheory.ObjectProperty.isClosedUnderIsomorphisms_of_isClosedUnderCokernels`), since any
isomorphic object is a kernel (resp. cokernel) of a zero morphism.

When `C` is preadditive with a zero object and finite products and `P` contains zero and is closed
under finite products, closure under kernels implies that `P.ι : P.FullSubcategory ⥤ C` preserves
finite limits; dually, closure under cokernels implies that `P.ι` preserves finite colimits. Thus
finite limits and colimits in the full subcategory are computed in `C`. In particular, when `C` is
abelian and `P` is closed under kernels, cokernels and finite products, `P.ι` is exact for
Mathlib's inherited abelian structure on `P.FullSubcategory`
(`Mathlib.CategoryTheory.Abelian.Subcategory`).

These combine Mathlib's preservation of kernels and cokernels by `P.ι`
(`ObjectProperty.preservesKernels_ι`, `ObjectProperty.preservesCokernels_ι`) with the fact that an
additive functor preserving kernels (cokernels) preserves finite limits (colimits),
`Functor.preservesFiniteLimits_of_preservesKernels`.
-/

public section

namespace CategoryTheory.ObjectProperty

open Limits

section IsClosedUnderIsomorphisms

variable {C : Type*} [Category* C] [HasZeroMorphisms C] (P : ObjectProperty C)

/-- A nonempty property of objects closed under kernels is closed under isomorphisms: if `Z` lies
in `P` and `e : X ≅ Y`, then `Y` is a kernel of the zero morphism `X ⟶ Z` via `e.inv`. -/
instance (priority := 100) isClosedUnderIsomorphisms_of_isClosedUnderKernels [P.Nonempty]
    [P.IsClosedUnderKernels] : P.IsClosedUnderIsomorphisms where
  of_iso {X Y} e hX := by
    obtain ⟨Z, hZ⟩ := P.exists_prop_of_nonempty
    have hk : IsLimit (KernelFork.ofι e.inv (comp_zero : e.inv ≫ (0 : X ⟶ Z) = 0)) :=
      KernelFork.IsLimit.ofι _ _ (fun k _ ↦ k ≫ e.hom) (fun _ _ ↦ by simp)
        (fun _ _ m hm ↦ by
          rw [← cancel_mono e.inv, hm, Category.assoc, e.hom_inv_id, Category.comp_id])
    exact P.prop_of_isLimit_kernelFork hk hX hZ

/-- A nonempty property of objects closed under cokernels is closed under isomorphisms: if `Z` lies
in `P` and `e : X ≅ Y`, then `Y` is a cokernel of the zero morphism `Z ⟶ X` via `e.hom`. -/
instance (priority := 100) isClosedUnderIsomorphisms_of_isClosedUnderCokernels [P.Nonempty]
    [P.IsClosedUnderCokernels] : P.IsClosedUnderIsomorphisms where
  of_iso {X Y} e hX := by
    obtain ⟨Z, hZ⟩ := P.exists_prop_of_nonempty
    have hk : IsColimit (CokernelCofork.ofπ e.hom (zero_comp : (0 : Z ⟶ X) ≫ e.hom = 0)) :=
      CokernelCofork.IsColimit.ofπ _ _ (fun k _ ↦ e.inv ≫ k) (fun _ _ ↦ by simp)
        (fun _ _ m hm ↦ by rw [← cancel_epi e.hom, hm, Iso.hom_inv_id_assoc])
    exact P.prop_of_isColimit_cokernelCofork hk hZ hX

end IsClosedUnderIsomorphisms

section ExactInclusion

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

end ExactInclusion

end CategoryTheory.ObjectProperty
