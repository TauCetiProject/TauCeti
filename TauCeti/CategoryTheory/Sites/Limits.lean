/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Types.Products
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering

/-!
# Limits and the functor induced on sheaves

If a functor `F : A ⥤ B` preserves limits of shape `K`, then so does the induced functor
`sheafCompose J F : Sheaf J A ⥤ Sheaf J B`
(`CategoryTheory.Sheaf.preservesLimitsOfShape_sheafCompose`), since limits of sheaves are computed
on the underlying presheaves (Mathlib's `CategoryTheory.Sites.Limits`).

For sheaves of types, the sections of a binary product `F ⨯ G` over `W` are pairs of sections:
any sections `a` of `F` and `b` of `G` over `W` are the projections of a section of `F ⨯ G`
(`CategoryTheory.Sheaf.exists_fst_eq_snd_eq`).
-/

public section

open CategoryTheory Limits Opposite

universe w

namespace CategoryTheory.Sheaf

variable {C : Type*} [Category* C] (J : GrothendieckTopology C)

/-- If `F` preserves limits of shape `K`, then so does the induced functor on sheaves, since limits
of sheaves are computed on the underlying presheaves. -/
instance preservesLimitsOfShape_sheafCompose {A B : Type*} [Category* A] [Category* B]
    (F : A ⥤ B) [J.HasSheafCompose F] (K : Type*) [Category* K] [HasLimitsOfShape K A]
    [PreservesLimitsOfShape K F] :
    PreservesLimitsOfShape K (sheafCompose J F) := by
  -- `sheafCompose J F` is defined as `ObjectProperty.lift` of the composite
  -- `sheafToPresheaf J A ⋙ (whiskeringRight _ _ _).obj F`, so composing it with
  -- `sheafToPresheaf J B` gives that composite definitionally, as in Mathlib's
  -- `CategoryTheory.Sites.Whiskering`.
  have : PreservesLimitsOfShape K (sheafCompose J F ⋙ sheafToPresheaf J B) :=
    inferInstanceAs
      (PreservesLimitsOfShape K (sheafToPresheaf J A ⋙ (Functor.whiskeringRight _ _ _).obj F))
  exact preservesLimitsOfShape_of_reflects_of_preserves _ (sheafToPresheaf J B)

variable {J} in
/-- Sections `a` of `F` and `b` of `G` over `W` are the projections of a section of `F ⨯ G`. -/
theorem exists_fst_eq_snd_eq {F G : Sheaf J (Type w)} {W : C} (a : F.obj.obj (op W))
    (b : G.obj.obj (op W)) : ∃ e : (F ⨯ G).obj.obj (op W),
      (prod.fst : F ⨯ G ⟶ F).hom.app (op W) e = a ∧
        (prod.snd : F ⨯ G ⟶ G).hom.app (op W) e = b := by
  let E := sheafToPresheaf J (Type w) ⋙ (evaluation Cᵒᵖ (Type w)).obj (op W)
  let e₀ := (Types.binaryProductIso _ _).inv (a, b)
  refine ⟨(PreservesLimitPair.iso E F G).inv e₀, ?_, ?_⟩
  · exact (ConcreteCategory.congr_hom (PreservesLimitPair.iso_inv_fst E F G) e₀).trans
      (Types.binaryProductIso_inv_comp_fst_apply _ _ _)
  · exact (ConcreteCategory.congr_hom (PreservesLimitPair.iso_inv_snd E F G) e₀).trans
      (Types.binaryProductIso_inv_comp_snd_apply _ _ _)

end CategoryTheory.Sheaf
