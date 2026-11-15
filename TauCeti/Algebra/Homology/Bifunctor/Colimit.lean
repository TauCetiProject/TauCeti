/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Bifunctor
public import Mathlib.Algebra.Homology.HomologicalComplexLimits

/-!
# Totalization of a bifunctor and colimits in the left variable

Let `F : C₁ ⥤ C₂ ⥤ D` be a bifunctor and `K₂` a homological complex in `C₂`. Totalizing `F`
against `K₂` gives a functor `K₁ ↦ mapBifunctor K₁ K₂ F c` on complexes in `C₁`. In degree `n`
its value is the coproduct of the objects `F(K₁ₚ, K₂_q)` over the pairs `(p, q)` lying over `n`.

If every functor `F(-, X₂)` preserves colimits of shape `S`, then so does this totalization
(`HomologicalComplex.preservesColimitsOfShape_map₂HomologicalComplex_flip_obj`): colimits of
complexes are computed degreewise, and a coproduct of colimit cocones is a colimit cocone.

For the tensor product of complexes this says that `- ⊗ L` commutes with every colimit that
`- ⊗ X` commutes with for the objects `X` of `C`. This is how colimits of K-flat complexes are
shown to be K-flat.
-/

public section

noncomputable section

open CategoryTheory Limits

namespace HomologicalComplex

variable {C₁ C₂ D I₁ I₂ J : Type*} [Category* C₁] [Category* C₂] [Category* D]
  {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
  [HasZeroMorphisms C₁] [HasZeroMorphisms C₂] [Preadditive D]
  (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms] [∀ X₁, (F.obj X₁).PreservesZeroMorphisms]
  (c : ComplexShape J) [DecidableEq J] [TotalComplexShape c₁ c₂ c]
  [∀ (K₁ : HomologicalComplex C₁ c₁) (K₂ : HomologicalComplex C₂ c₂), HasMapBifunctor K₁ K₂ F c]
  {S : Type*} [Category* S] [HasColimitsOfShape S C₁]
  [∀ X₂ : C₂, PreservesColimitsOfShape S (F.flip.obj X₂)]

/-- In a fixed degree `n`, totalization against `K₂` sends a colimit cocone of complexes to a
colimit cocone: on the summand `F(K₁ₚ, K₂_q)` the cocone is the image of the colimit cocone in
degree `p` under `F(-, K₂_q)`. -/
private def isColimitMapCoconeEval (K₂ : HomologicalComplex C₂ c₂)
    {G : S ⥤ HomologicalComplex C₁ c₁} {s : Cocone G} (hs : IsColimit s) (n : J) :
    IsColimit (((F.map₂HomologicalComplex c₁ c₂ c).flip.obj K₂ ⋙ eval D c n).mapCocone s) := by
  -- on the summands, maps in the left variable act through `F(-, K₂_q)`
  have hι {K L : HomologicalComplex C₁ c₁} (f : K ⟶ L) (p : I₁) (q : I₂)
      (hpq : ComplexShape.π c₁ c₂ c (p, q) = n) :
      ιMapBifunctor K K₂ F c p q n hpq ≫ (mapBifunctorMap f (𝟙 K₂) F c).f n =
        (F.map (f.f p)).app (K₂.X q) ≫ ιMapBifunctor L K₂ F c p q n hpq := by
    simp
  -- the colimit cocone of the summands `F(K₁ₚ, K₂_q)`
  let h (p : I₁) (q : I₂) : IsColimit ((eval C₁ c₁ p ⋙ F.flip.obj (K₂.X q)).mapCocone s) :=
    isColimitOfPreserves _ hs
  -- a compatible family of maps out of the degree `n` totalizations descends summand by summand
  let desc (T : D) (τ : ∀ j, (mapBifunctor (G.obj j) K₂ F c).X n ⟶ T)
      (hτ : ∀ ⦃j j' : S⦄ (f : j ⟶ j'), (mapBifunctorMap (G.map f) (𝟙 K₂) F c).f n ≫ τ j' = τ j) :
      (mapBifunctor s.pt K₂ F c).X n ⟶ T :=
    mapBifunctorDesc fun p q hpq ↦ (h p q).desc
      { pt := T
        ι :=
          { app j := ιMapBifunctor (G.obj j) K₂ F c p q n hpq ≫ τ j
            naturality j j' f := by
              dsimp
              rw [Category.comp_id, ← hτ f, reassoc_of% hι] } }
  have fac (T : D) (τ : ∀ j, (mapBifunctor (G.obj j) K₂ F c).X n ⟶ T)
      (hτ : ∀ ⦃j j' : S⦄ (f : j ⟶ j'), (mapBifunctorMap (G.map f) (𝟙 K₂) F c).f n ≫ τ j' = τ j)
      (j : S) : (mapBifunctorMap (s.ι.app j) (𝟙 K₂) F c).f n ≫ desc T τ hτ = τ j := by
    refine mapBifunctor.hom_ext fun p q hpq ↦ ?_
    rw [reassoc_of% hι, ι_mapBifunctorDesc]
    exact (h p q).fac _ j
  have uniq (T : D) (τ : ∀ j, (mapBifunctor (G.obj j) K₂ F c).X n ⟶ T)
      (hτ : ∀ ⦃j j' : S⦄ (f : j ⟶ j'), (mapBifunctorMap (G.map f) (𝟙 K₂) F c).f n ≫ τ j' = τ j)
      (m : (mapBifunctor s.pt K₂ F c).X n ⟶ T)
      (hm : ∀ j, (mapBifunctorMap (s.ι.app j) (𝟙 K₂) F c).f n ≫ m = τ j) :
      m = desc T τ hτ := by
    refine mapBifunctor.hom_ext fun p q hpq ↦ (h p q).hom_ext fun j ↦ ?_
    simp only [desc, ι_mapBifunctorDesc, (h p q).fac]
    dsimp
    rw [← hm j, reassoc_of% hι]
    -- the two sides differ only by the value `(Functor.const S).obj s.pt).obj j = s.pt` of the
    -- constant functor, which cannot be rewritten since the summand inclusion depends on it
    rfl
  exact
    { desc t := desc t.pt (fun j ↦ t.ι.app j) fun _ _ f ↦ t.w f
      fac t j := fac t.pt (fun j ↦ t.ι.app j) (fun _ _ f ↦ t.w f) j
      uniq t m hm := uniq t.pt (fun j ↦ t.ι.app j) (fun _ _ f ↦ t.w f) m hm }

/-- Totalizing a bifunctor `F` against a fixed right complex preserves the colimits of shape
`S` in the left variable, provided each functor `F(-, X₂)` does. -/
instance preservesColimitsOfShape_map₂HomologicalComplex_flip_obj
    (K₂ : HomologicalComplex C₂ c₂) :
    PreservesColimitsOfShape S ((F.map₂HomologicalComplex c₁ c₂ c).flip.obj K₂) :=
  preservesColimitsOfShape_of_eval _ fun n ↦
    ⟨fun {_} ↦ ⟨fun hs ↦ ⟨isColimitMapCoconeEval F c K₂ hs n⟩⟩⟩

end HomologicalComplex
