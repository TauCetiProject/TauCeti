/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Triangulated.Subcategory

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
-/

public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe v u

namespace CategoryTheory.ObjectProperty

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] (P : ObjectProperty C)
  [P.IsTriangulated]

/-- **Ambient triangles in a triangulated subcategory**: a distinguished triangle of `C` whose
first two vertices lie in `P` is isomorphic to the image of a distinguished triangle of
`P.FullSubcategory` under the inclusion. -/
theorem exists_distTriang_mapTriangle_iso {T : Triangle C} (hT : T ∈ distTriang C)
    (h₁ : P T.obj₁) (h₂ : P T.obj₂) :
    ∃ T' ∈ distTriang P.FullSubcategory, Nonempty (P.ι.mapTriangle.obj T' ≅ T) := by
  obtain ⟨Z, g, h, hT'⟩ := distinguished_cocone_triangle
    (P.fullyFaithfulι.preimage T.mor₁ : (⟨T.obj₁, h₁⟩ : P.FullSubcategory) ⟶ ⟨T.obj₂, h₂⟩)
  exact ⟨_, hT', ⟨isoTriangleOfIso₁₂ _ _ (P.ι.map_distinguished _ hT') hT (Iso.refl _)
    (Iso.refl _) (by simp)⟩⟩

end CategoryTheory.ObjectProperty
