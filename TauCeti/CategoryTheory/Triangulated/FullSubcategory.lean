/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Triangulated.Subcategory
import TauCeti.CategoryTheory.Triangulated.Biproduct

/-!
# Distinguished triangles of triangulated subcategories

Let `P` be a triangulated subcategory of a pretriangulated category `C`. A distinguished triangle
of `C` whose first two vertices lie in `P` is, up to isomorphism, the image of a distinguished
triangle of the full subcategory `P.FullSubcategory`: complete the first morphism to a
distinguished triangle of the subcategory, and compare its image with the given triangle along the
identities of the first two vertices. In particular its third vertex is isomorphic to an object of
the subcategory, even though the given connecting morphism only exists in `C`.

## Main results

* `CategoryTheory.ObjectProperty.exists_distTriang_mapTriangle_iso`: an ambient distinguished
  triangle with its first two vertices in `P` is isomorphic to the image of a distinguished
  triangle of `P.FullSubcategory`.
* `CategoryTheory.ObjectProperty.prop_left_of_biprod` and
  `CategoryTheory.ObjectProperty.prop_right_of_biprod`: if a biproduct `X ⊞ Y` and one of its
  summands lie in a strictly full triangulated subcategory, so does the other summand.
* `CategoryTheory.ObjectProperty.prop_biprod_obj₂_of_distTriang`: for two distinguished triangles
  whose biproducts of first and third vertices lie in a strictly full extension-closed subcategory,
  the biproduct of their middle vertices also lies in the subcategory.
-/

public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe v u

namespace CategoryTheory.ObjectProperty

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] (P : ObjectProperty C)

/-- **Ambient triangles in a triangulated subcategory**: a distinguished triangle of `C` whose
first two vertices lie in `P` is isomorphic to the image of a distinguished triangle of
`P.FullSubcategory` under the inclusion. -/
theorem exists_distTriang_mapTriangle_iso [P.IsTriangulated] {T : Triangle C}
    (hT : T ∈ distTriang C) (h₁ : P T.obj₁) (h₂ : P T.obj₂) :
    ∃ T' ∈ distTriang P.FullSubcategory, Nonempty (P.ι.mapTriangle.obj T' ≅ T) := by
  obtain ⟨Z, g, h, hT'⟩ := distinguished_cocone_triangle
    (P.fullyFaithfulι.preimage T.mor₁ : (⟨T.obj₁, h₁⟩ : P.FullSubcategory) ⟶ ⟨T.obj₂, h₂⟩)
  exact ⟨_, hT', ⟨isoTriangleOfIso₁₂ _ _ (P.ι.map_distinguished _ hT') hT (Iso.refl _)
    (Iso.refl _) (by simp)⟩⟩

/-- **Left summand cancellation**: if `X ⊞ Y` and `Y` belong to a strictly full subcategory closed
under taking first vertices of distinguished triangles, then `X` belongs to it as well. -/
theorem prop_left_of_biprod [P.IsTriangulatedClosed₁] [P.IsClosedUnderIsomorphisms]
    {X Y : C} (hXY : P (X ⊞ Y)) (hY : P Y) : P X :=
  P.ext_of_isTriangulatedClosed₁ _ (binaryBiproductTriangle_distinguished X Y) hXY hY

/-- **Right summand cancellation**: if `X ⊞ Y` and `X` belong to a strictly full subcategory closed
under taking cones of distinguished triangles, then `Y` belongs to it as well. -/
theorem prop_right_of_biprod [P.IsTriangulatedClosed₃] [P.IsClosedUnderIsomorphisms]
    {X Y : C} (hXY : P (X ⊞ Y)) (hX : P X) : P Y :=
  P.ext_of_isTriangulatedClosed₃ _ (binaryBiproductTriangle_distinguished X Y) hX hXY

/-- **Biproduct of two distinguished triangles**: if `T₁` and `T₂` are distinguished triangles such
that `T₁.obj₁ ⊞ T₂.obj₁` and `T₁.obj₃ ⊞ T₂.obj₃` lie in a strictly full subcategory closed under
extensions, then `T₁.obj₂ ⊞ T₂.obj₂` also lies in it. -/
theorem prop_biprod_obj₂_of_distTriang [P.IsTriangulatedClosed₂] [P.IsClosedUnderIsomorphisms]
    {T₁ T₂ : Triangle C} (hT₁ : T₁ ∈ distTriang C) (hT₂ : T₂ ∈ distTriang C)
    (h₁ : P (T₁.obj₁ ⊞ T₂.obj₁)) (h₃ : P (T₁.obj₃ ⊞ T₂.obj₃)) :
    P (T₁.obj₂ ⊞ T₂.obj₂) := by
  obtain ⟨T, hT, ⟨e₁⟩, ⟨e₂⟩, ⟨e₃⟩⟩ := Pretriangulated.exists_distTriang_iso_biprod T₁ T₂ hT₁ hT₂
  exact P.prop_of_iso e₂ (P.ext_of_isTriangulatedClosed₂ _ hT
    (P.prop_of_iso e₁.symm h₁) (P.prop_of_iso e₃.symm h₃))

end CategoryTheory.ObjectProperty
