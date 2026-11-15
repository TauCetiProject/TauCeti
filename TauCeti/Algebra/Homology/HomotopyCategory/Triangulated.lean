/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated

/-!
# Naturality of the mapping cone triangles of composable morphisms in the homotopy category

For composable morphisms `f : X₁ ⟶ X₂` and `g : X₂ ⟶ X₃` of cochain complexes, Mathlib's
`CochainComplex.mappingConeCompTriangleh f g` is the distinguished triangle
`mappingCone f ⟶ mappingCone (f ≫ g) ⟶ mappingCone g ⟶ (mappingCone f)⟦1⟧` in the homotopy
category, the image of `CochainComplex.mappingConeCompTriangle f g` under the quotient functor.
Mathlib's `CochainComplex.mappingConeCompTriangle_mor₃_naturality` states the naturality of the
third morphism of `mappingConeCompTriangle f g` at the level of cochain complexes; this file
records the corresponding naturality of the third morphism of `mappingConeCompTriangleh f g`.

## Main results

* `CochainComplex.mappingConeCompTriangleh_mor₃_naturality`: naturality in `(f, g)` of the third
  morphism of `mappingConeCompTriangleh f g`.
-/

public section

open CategoryTheory Limits ComposableArrows HomotopyCategory

namespace CochainComplex

variable {C : Type*} [Category* C] [Preadditive C] [HasBinaryBiproducts C]

/-- The third morphisms of the distinguished triangles `mappingConeCompTriangleh f g` of mapping
cones in the homotopy category are natural in the pair of composable morphisms `(f, g)`. -/
@[reassoc]
lemma mappingConeCompTriangleh_mor₃_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃ : CochainComplex C ℤ}
    (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃)
    (f' : Y₁ ⟶ Y₂) (g' : Y₂ ⟶ Y₃) (a : X₁ ⟶ Y₁) (b : X₂ ⟶ Y₂) (c : X₃ ⟶ Y₃)
    (h₁ : f ≫ b = a ≫ f') (h₂ : g ≫ c = b ≫ g') :
    (mappingConeCompTriangleh f g).mor₃ ≫
        ((quotient C (ComplexShape.up ℤ)).map (mappingCone.map f f' a b h₁))⟦(1 : ℤ)⟧' =
      (quotient C (ComplexShape.up ℤ)).map (mappingCone.map g g' b c h₂) ≫
        (mappingConeCompTriangleh f' g').mor₃ := by
  have h := mappingConeCompTriangle_mor₃_naturality f g f' g' (homMk₂ a b c h₁ h₂)
  dsimp [mappingConeCompTriangleh, mappingConeCompTriangle] at h ⊢
  simp only [Category.assoc, ← Functor.commShiftIso_hom_naturality, ← Functor.map_comp_assoc, ← h]

end CochainComplex
