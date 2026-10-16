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
`CochainComplex.mappingConeCompTriangle f g` is the triangle
`mappingCone f ⟶ mappingCone (f ≫ g) ⟶ mappingCone g ⟶ (mappingCone f)⟦1⟧`, which is
distinguished in the homotopy category, and `CochainComplex.mappingConeCompTriangle_mor₃_naturality`
states the naturality of its third morphism at the level of cochain complexes. This file records
the corresponding naturality after passing to the homotopy category, where the shift of the
quotient functor is identified through its `commShiftIso`.

## Main results

* `CochainComplex.quotient_mappingConeCompTriangle_mor₃_naturality`: naturality of the image in
  the homotopy category of the third morphism of `mappingConeCompTriangle f g` in `(f, g)`.
-/

public section

open CategoryTheory Limits ComposableArrows HomotopyCategory

namespace CochainComplex

variable {C : Type*} [Category* C] [Preadditive C] [HasBinaryBiproducts C]

/-- The third morphisms of the distinguished triangles of mapping cones in the homotopy category
are natural in the pair of composable morphisms. -/
lemma quotient_mappingConeCompTriangle_mor₃_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃ : CochainComplex C ℤ}
    (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃)
    (f' : Y₁ ⟶ Y₂) (g' : Y₂ ⟶ Y₃) (a : X₁ ⟶ Y₁) (b : X₂ ⟶ Y₂) (c : X₃ ⟶ Y₃)
    (h₁ : f ≫ b = a ≫ f') (h₂ : g ≫ c = b ≫ g') :
    ((quotient C (ComplexShape.up ℤ)).map (mappingConeCompTriangle f g).mor₃ ≫
        ((quotient C (ComplexShape.up ℤ)).commShiftIso (1 : ℤ)).hom.app (mappingCone f)) ≫
        ((quotient C (ComplexShape.up ℤ)).map (mappingCone.map f f' a b h₁))⟦(1 : ℤ)⟧' =
      (quotient C (ComplexShape.up ℤ)).map (mappingCone.map g g' b c h₂) ≫
        (quotient C (ComplexShape.up ℤ)).map (mappingConeCompTriangle f' g').mor₃ ≫
          ((quotient C (ComplexShape.up ℤ)).commShiftIso (1 : ℤ)).hom.app (mappingCone f') := by
  have eq := mappingConeCompTriangle_mor₃_naturality f g f' g' (homMk₂ a b c h₁ h₂)
  dsimp at eq
  let Q := quotient C (ComplexShape.up ℤ)
  exact (Category.assoc _ _ _).trans <|
    (congrArg (fun t => Q.map (mappingConeCompTriangle f g).mor₃ ≫ t)
      (Q.commShiftIso_hom_naturality (mappingCone.map f f' a b h₁) (1 : ℤ)).symm).trans <|
    (Q.map_comp_assoc _ _ _).symm.trans <|
    (congrArg (fun t => Q.map t ≫ (Q.commShiftIso (1 : ℤ)).hom.app (mappingCone f'))
      eq.symm).trans (Q.map_comp_assoc _ _ _)

end CochainComplex
