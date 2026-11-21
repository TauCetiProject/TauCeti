/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Triangulated.Subcategory

/-!
# Extension-closed properties of objects are closed under finite products

Let `P` be a property of objects of a pretriangulated category `C` which is closed under
extensions: whenever `X₁ ⟶ X₂ ⟶ X₃ ⟶ X₁⟦1⟧` is distinguished and `P X₁`, `P X₃` hold, so does
`P X₂` (`ObjectProperty.IsTriangulatedClosed₂`). Since `X ⨯ Y` is the middle vertex of the split
distinguished triangle `X ⟶ X ⨯ Y ⟶ Y ⟶ X⟦1⟧`, such a property is closed under binary products,
and under finite products once it also contains a zero object.

Mathlib records these facts for triangulated subcategories (`ObjectProperty.IsTriangulated`);
here no stability under shifts is assumed. This applies, for instance, to the aisles and coaisles
of a `t`-structure and to its heart.

## Main results

* `CategoryTheory.ObjectProperty.isClosedUnderBinaryProducts_of_isTriangulatedClosed₂`
* `CategoryTheory.ObjectProperty.isClosedUnderFiniteProducts_of_isTriangulatedClosed₂`
-/

public section

namespace CategoryTheory.ObjectProperty

open Limits Pretriangulated

variable {C : Type*} [Category* C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] (P : ObjectProperty C)

/-- A property of objects closed under extensions and isomorphisms is closed under binary
products. -/
instance (priority := 100) isClosedUnderBinaryProducts_of_isTriangulatedClosed₂
    [P.IsTriangulatedClosed₂] [P.IsClosedUnderIsomorphisms] :
    P.IsClosedUnderBinaryProducts where
  limitsOfShape_le := by
    rintro X ⟨p⟩
    refine P.prop_of_iso ?_ (P.ext_of_isTriangulatedClosed₂ _
      (binaryProductTriangle_distinguished _ _)
      (p.prop_diag_obj (.mk .left)) (p.prop_diag_obj (.mk .right)))
    exact IsLimit.conePointUniqueUpToIso (prodIsProd _ _)
      ((IsLimit.postcomposeHomEquiv (diagramIsoPair p.diag) _).invFun p.isLimit)

/-- A property of objects closed under extensions and isomorphisms which contains a zero object
is closed under finite products. -/
instance (priority := 100) isClosedUnderFiniteProducts_of_isTriangulatedClosed₂
    [P.IsTriangulatedClosed₂] [P.IsClosedUnderIsomorphisms] [P.ContainsZero] :
    P.IsClosedUnderFiniteProducts :=
  .mk'

end CategoryTheory.ObjectProperty
