/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-!
# Transporting distinguished triangles along isomorphisms of vertices

In a pretriangulated category, the distinguished triangles are closed under isomorphisms of
triangles. This file records the two forms used to replace the vertices of a distinguished triangle
by isomorphic objects: conjugating all three morphisms along isomorphisms of the three vertices,
and replacing only the first vertex.

## Main results

* `CategoryTheory.Pretriangulated.distinguished_mk_of_iso`: a triangle transported along
  isomorphisms of its three vertices is distinguished.
* `CategoryTheory.Pretriangulated.distinguished_mk_of_iso₁`: a triangle transported along an
  isomorphism of its first vertex is distinguished.
-/

public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory.Pretriangulated

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- **Transport along vertex isomorphisms**: if `T` is distinguished and `eᵢ : T.objᵢ ≅ Aᵢ`, the
triangle on `A₁, A₂, A₃` with the conjugated morphisms is distinguished. -/
theorem distinguished_mk_of_iso {T : Triangle C} (hT : T ∈ distTriang C) {A₁ A₂ A₃ : C}
    (e₁ : T.obj₁ ≅ A₁) (e₂ : T.obj₂ ≅ A₂) (e₃ : T.obj₃ ≅ A₃) :
    Triangle.mk (e₁.inv ≫ T.mor₁ ≫ e₂.hom) (e₂.inv ≫ T.mor₂ ≫ e₃.hom)
      (e₃.inv ≫ T.mor₃ ≫ (shiftFunctor C (1 : ℤ)).map e₁.hom) ∈ distTriang C :=
  isomorphic_distinguished _ hT _ (Triangle.isoMk _ _ e₁.symm e₂.symm e₃.symm (by simp) (by simp)
    (by simp [← Functor.map_comp]))

/-- **Transport along an isomorphism of the first vertex**: if `T` is distinguished and
`e₁ : T.obj₁ ≅ A₁`, the triangle with first vertex `A₁` is distinguished. -/
theorem distinguished_mk_of_iso₁ {T : Triangle C} (hT : T ∈ distTriang C) {A₁ : C}
    (e₁ : T.obj₁ ≅ A₁) :
    Triangle.mk (e₁.inv ≫ T.mor₁) T.mor₂ (T.mor₃ ≫ (shiftFunctor C (1 : ℤ)).map e₁.hom) ∈
      distTriang C :=
  isomorphic_distinguished _ hT _ (Triangle.isoMk _ _ e₁.symm (Iso.refl _) (Iso.refl _) (by simp)
    (by simp) (by simp [← Functor.map_comp]))

end CategoryTheory.Pretriangulated
