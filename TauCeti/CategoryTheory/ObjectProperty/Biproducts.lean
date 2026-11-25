/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.EssentialImage
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
public import TauCeti.CategoryTheory.ObjectProperty.FiniteProducts

/-!
# Essential images closed under zero objects and biproducts

The essential image of a functor preserving zero morphisms contains a zero object as soon as the
source has one (`CategoryTheory.Functor.essImage_containsZero`), and the essential image of a
functor preserving binary biproducts is closed under binary products
(`CategoryTheory.Functor.essImage_isClosedUnderBinaryProducts`), hence under finite products when
both hold (`CategoryTheory.Functor.essImage_isClosedUnderFiniteProducts`). No fullness is needed,
unlike for Mathlib's closure of the essential image under the limits a fully faithful functor
preserves.

## Main results

* `CategoryTheory.Functor.essImage_containsZero`: the essential image contains a zero object.
* `CategoryTheory.Functor.essImage_isClosedUnderBinaryProducts`: the essential image is closed
  under binary products.
* `CategoryTheory.Functor.essImage_isClosedUnderFiniteProducts`: the essential image is closed
  under finite products.
-/

public section

namespace CategoryTheory.Functor

open Limits

variable {C D : Type*} [Category* C] [Category* D] [HasZeroMorphisms C] [HasZeroMorphisms D]
  (F : C ⥤ D) [F.PreservesZeroMorphisms]

/-- The essential image of a functor preserving zero morphisms contains a zero object, the image
of a zero object of the source. -/
instance essImage_containsZero [HasZeroObject C] : F.essImage.ContainsZero where
  exists_zero := ⟨_, F.map_isZero (isZero_zero C), F.obj_mem_essImage _⟩

/-- The essential image of a functor preserving binary biproducts is closed under binary
products: if `F.obj X₁ ≅ Y₁` and `F.obj X₂ ≅ Y₂`, then `F.obj (X₁ ⊞ X₂) ≅ Y₁ ⊞ Y₂`. -/
instance essImage_isClosedUnderBinaryProducts [HasBinaryBiproducts C] [HasBinaryBiproducts D]
    [PreservesBinaryBiproducts F] : F.essImage.IsClosedUnderBinaryProducts :=
  ObjectProperty.isClosedUnderBinaryProducts_of_prop_biprod _
    fun _ _ ⟨X₁, ⟨e₁⟩⟩ ⟨X₂, ⟨e₂⟩⟩ ↦ ⟨X₁ ⊞ X₂, ⟨F.mapBiprod X₁ X₂ ≪≫ biprod.mapIso e₁ e₂⟩⟩

/-- The essential image of a functor preserving binary biproducts, out of a category with a zero
object, is closed under finite products. -/
instance essImage_isClosedUnderFiniteProducts [HasZeroObject C] [HasBinaryBiproducts C]
    [HasBinaryBiproducts D] [HasFiniteProducts D] [PreservesBinaryBiproducts F] :
    F.essImage.IsClosedUnderFiniteProducts :=
  ObjectProperty.IsClosedUnderFiniteProducts.mk'

end CategoryTheory.Functor
