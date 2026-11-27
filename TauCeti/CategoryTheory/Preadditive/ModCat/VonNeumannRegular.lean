/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Preadditive.ModCat.Basic
public import TauCeti.CategoryTheory.Preadditive.VonNeumannRegular

/-!
# Principal submodules of representables over regular categories

A preadditive category is von Neumann regular if and only if each principal submodule of a
representable is a direct summand. A principal submodule here is the image of a morphism from
one representable to another. This is the principal case of Stenström's splitting criterion
in *Purity in functor categories*, §5, Theorem 4.
-/

public section

namespace TauCeti.ModCat

open CategoryTheory CategoryTheory.Limits

variable {C : Type*} [Category* C] [Preadditive C]

/-- The image of a map between representable modules is a direct summand precisely when the
representing morphism has an inner inverse. -/
theorem isSplitMono_image_ι_yoneda_map_iff {X Y : C} (f : X ⟶ Y) :
    IsSplitMono (image.ι ((yoneda C).map f)) ↔ ∃ g : Y ⟶ X, f ≫ g ≫ f = f := by
  let F := yoneda C
  let i := image.ι (F.map f)
  let p := factorThruImage (F.map f)
  have hp : p ≫ i = F.map f := image.fac _
  constructor
  · intro h
    obtain ⟨g, hg⟩ := F.map_surjective (Projective.factorThru (retraction i) p)
    have hgp : F.map g ≫ p = retraction i := hg ▸ Projective.factorThru_comp (retraction i) p
    refine ⟨g, F.map_injective ?_⟩
    simp only [Functor.map_comp]
    calc
      F.map f ≫ F.map g ≫ F.map f = p ≫ i ≫ (F.map g ≫ p) ≫ i := by
        simp only [← hp, Category.assoc]
      _ = F.map f := by simp [hgp, ← hp]
  · rintro ⟨g, hg⟩
    have hs : i ≫ (F.map g ≫ p) = 𝟙 _ := by
      apply (cancel_epi p).1
      apply (cancel_mono i).1
      calc
        (p ≫ i ≫ F.map g ≫ p) ≫ i = F.map f ≫ F.map g ≫ F.map f := by
          simp only [← hp, Category.assoc]
        _ = (p ≫ 𝟙 _) ≫ i := by
          simpa only [Functor.map_comp, Category.comp_id, hp] using congrArg (F.map) hg
    exact ⟨⟨F.map g ≫ p, hs⟩⟩

/-- Von Neumann regularity is equivalent to the splitting of all principal submodules of
representable modules. -/
theorem isVonNeumannRegularCategory_iff_isSplitMono_image_ι_yoneda_map :
    IsVonNeumannRegularCategory C ↔
      ∀ ⦃X Y : C⦄ (f : X ⟶ Y), IsSplitMono (image.ι ((yoneda C).map f)) :=
  ⟨fun h _ _ f ↦ (isSplitMono_image_ι_yoneda_map_iff f).mpr (h.exists_comp_comp_eq_self f),
    fun h ↦ by
      constructor
      intro X Y f
      exact (isSplitMono_image_ι_yoneda_map_iff f).mp (h f)⟩

end TauCeti.ModCat
