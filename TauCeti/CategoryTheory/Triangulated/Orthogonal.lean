/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Triangulated.Orthogonal

/-!
# Right orthogonality of third vertices of triangles

Let `P` be a class of objects of a pretriangulated category, stable under shifts, and let
`T : X₁ ⟶ X₂ ⟶ X₃ ⟶ X₁⟦1⟧` be a distinguished triangle. If every morphism from an object of `P`
to `X₂` factors uniquely through `X₁ ⟶ X₂`, then `X₃` is right orthogonal to `P`. This is the
long exact sequence of `Hom(K, -)` for objects `K` of `P`: surjectivity at `K` kills the image of
`Hom(K, X₂)` in `Hom(K, X₃)`, and injectivity at `K⟦-1⟧` kills the connecting map to
`Hom(K, X₁⟦1⟧)`.

This is how one shows that an object built as a cone is orthogonal to a class of objects
satisfying a lifting property, as for curved modules with projective underlying graded module
and totalizations of short exact sequences.
-/

public section

namespace CategoryTheory.ObjectProperty

open Limits Pretriangulated

variable {C : Type*} [Category* C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  (P : ObjectProperty C) [P.IsStableUnderShift ℤ]

/-- Let `T` be a distinguished triangle such that, for every object `K` of a shift-stable class
`P`, composition with `T.mor₁` is a bijection from morphisms `K ⟶ T.obj₁` to morphisms
`K ⟶ T.obj₂`. Then `T.obj₃` is right orthogonal to `P`. -/
theorem rightOrthogonal_obj₃_of_bijective (T : Triangle C) (hT : T ∈ distTriang C)
    (H : ∀ K, P K → Function.Bijective fun f : K ⟶ T.obj₁ ↦ f ≫ T.mor₁) :
    P.rightOrthogonal T.obj₃ := by
  intro K φ hK
  -- The connecting morphism `φ ≫ T.mor₃` vanishes: its unshift by `-1` lands in `T.obj₁` and
  -- becomes zero after composing with `T.mor₁`, so it is zero by injectivity at `K⟦-1⟧`.
  have hφ : φ ≫ T.mor₃ = 0 := by
    let e := shiftFunctorCompIsoId C (1 : ℤ) (-1) (by omega)
    have h₀ : ((φ ≫ T.mor₃)⟦(-1 : ℤ)⟧' ≫ e.hom.app T.obj₁) ≫ T.mor₁ = 0 ≫ T.mor₁ := by
      have hn := e.hom.naturality T.mor₁
      dsimp only [Functor.comp_obj, Functor.comp_map, Functor.id_map] at hn
      rw [Category.assoc, ← hn, ← Category.assoc, ← Functor.map_comp, Category.assoc,
        comp_distTriang_mor_zero₃₁ T hT, comp_zero, Functor.map_zero, zero_comp, zero_comp]
    have h₁ := (H _ (P.le_shift (-1 : ℤ) K hK)).1 h₀
    rw [Preadditive.IsIso.comp_right_eq_zero] at h₁
    exact ((shiftFunctor C (-1 : ℤ)).map_eq_zero_iff).1 h₁
  obtain ⟨ψ, rfl⟩ := Triangle.coyoneda_exact₃ T hT φ hφ
  obtain ⟨χ, rfl⟩ := (H K hK).2 ψ
  rw [Category.assoc, comp_distTriang_mor_zero₁₂ T hT, comp_zero]

end CategoryTheory.ObjectProperty
