/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.Gluing
public import TauCeti.Geometry.RingedSpace.PresheafedSpace.GlueMorphisms

/-!
# Gluing morphisms out of a sheafy pre-adic space

Let `X` be a pre-adic space whose structure presheaf is a sheaf, and let `U i` be opens covering
`X`. Morphisms of pre-adic spaces `f i : X|_{U i} ⟶ Y` agreeing on the overlaps glue to a unique
morphism `X ⟶ Y`. The underlying morphisms of presheafed spaces glue
(`AlgebraicGeometry.PresheafedSpace.glueMorphisms`), and compatibility with the stalk valuations
can be checked on the cover (`TauCeti.PreAdicSpace.Hom.ofCover`).

As a consequence, factoring through a monomorphism of sheafy pre-adic spaces is local on the
source: if a morphism `f : X ⟶ Y` factors through `i : Z ⟶ Y` over each member of an open cover of
`X`, then it factors through `i`. The local factorisations agree on the overlaps because `i` is a
monomorphism, so they glue. For instance, this reduces factoring a morphism through a closed
immersion, which is a monomorphism of sheafy pre-adic spaces, to the case of affinoid sources.

## Main definitions

* `TauCeti.PreAdicSpace.glueMorphisms`: the morphism out of a sheafy pre-adic space glued from a
  family of morphisms out of the restrictions to an open cover, agreeing on the overlaps.

## Main results

* `TauCeti.PreAdicSpace.ofRestrict_glueMorphisms`: the glued morphism restricts to the given
  morphisms.
* `TauCeti.PreAdicSpace.hom_ext_of_ofRestrict`: morphisms out of a sheafy pre-adic space agreeing
  on every member of an open cover are equal.
* `TauCeti.SheafyPreAdicSpace.exists_comp_eq_of_iSup_eq_top`: factoring through a monomorphism of
  sheafy pre-adic spaces is local on the source.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, §8.1.
-/

public section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

namespace TauCeti

universe u w

namespace PreAdicSpace

variable {X Y : PreAdicSpace.{u}} (hX : isSheafy X) {ι : Type w} (U : ι → Opens X)
  (hU : ⨆ i, U i = ⊤) (f : ∀ i, X.restrict (U i).isOpenEmbedding ⟶ Y)
  (hf : ∀ i j, pullback.fst (X.ofRestrict (U i).isOpenEmbedding)
    (X.ofRestrict (U j).isOpenEmbedding) ≫ f i = pullback.snd _ _ ≫ f j)

include hf in
/-- The compatibility of the `f i` on the overlaps, for their underlying morphisms of presheafed
spaces: the forgetful functor preserves the pullbacks of open immersions. -/
private theorem toHom_pullback_condition (i j : ι) :
    pullback.fst (X.toPresheafedSpace.ofRestrict (U i).isOpenEmbedding)
      (X.toPresheafedSpace.ofRestrict (U j).isOpenEmbedding) ≫ (f i).toHom =
      pullback.snd _ _ ≫ (f j).toHom := by
  have (k : ι) : PresheafedSpace.IsOpenImmersion
      (forgetToPresheafedSpace.map (X.ofRestrict (U k).isOpenEmbedding)) :=
    inferInstanceAs (IsOpenImmersion (X.ofRestrict (U k).isOpenEmbedding))
  have := congrArg (fun k ↦ (PreservesPullback.iso forgetToPresheafedSpace
    (X.ofRestrict (U i).isOpenEmbedding) (X.ofRestrict (U j).isOpenEmbedding)).inv ≫
      forgetToPresheafedSpace.map k) (hf i j)
  simp only [Functor.map_comp, PreservesPullback.iso_inv_fst_assoc,
    PreservesPullback.iso_inv_snd_assoc] at this
  exact this

include hU in
private theorem exists_ofRestrict_base_eq (x : X) :
    ∃ (i : ι) (y : X.restrict (U i).isOpenEmbedding),
      (X.ofRestrict (U i).isOpenEmbedding).base y = x := by
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hU.symm ▸ trivial : x ∈ ⨆ i, U i)
  exact ⟨i, ⟨x, hi⟩, rfl⟩

/-- **Gluing morphisms out of a sheafy pre-adic space.** If `X` is sheafy, the opens `U i` cover
`X`, and the morphisms `f i : X|_{U i} ⟶ Y` agree on the overlaps, then they glue to a morphism
`X ⟶ Y` (`ofRestrict_glueMorphisms`), which is unique (`hom_ext_of_ofRestrict`). -/
noncomputable def glueMorphisms : X ⟶ Y :=
  Hom.ofCover (fun i ↦ X.ofRestrict (U i).isOpenEmbedding) (exists_ofRestrict_base_eq U hU)
    (PresheafedSpace.glueMorphisms hX U hU (fun i ↦ (f i).toHom)
      (toHom_pullback_condition U f hf))
    f fun i ↦ PresheafedSpace.ofRestrict_glueMorphisms hX U hU _ _ i

/-- The glued morphism restricts to `f i` on `U i`. -/
@[reassoc (attr := simp)]
theorem ofRestrict_glueMorphisms (i : ι) :
    X.ofRestrict (U i).isOpenEmbedding ≫ glueMorphisms hX U hU f hf = f i :=
  Hom.comp_ofCover _ _ _ _ _ i

include hX hU in
/-- **Morphisms out of a sheafy pre-adic space are determined locally.** Two morphisms `X ⟶ Y`
agreeing on every member of an open cover of `X` are equal. -/
theorem hom_ext_of_ofRestrict {g g' : X ⟶ Y}
    (h : ∀ i, X.ofRestrict (U i).isOpenEmbedding ≫ g = X.ofRestrict (U i).isOpenEmbedding ≫ g') :
    g = g' :=
  Hom.ext' (PresheafedSpace.hom_ext_of_ofRestrict hX U hU fun i ↦ congrArg Hom.toHom (h i))

end PreAdicSpace

namespace SheafyPreAdicSpace

/-- **Factoring through a monomorphism of sheafy pre-adic spaces is local on the source.** If
`i : Z ⟶ Y` is a monomorphism of sheafy pre-adic spaces and `f : X ⟶ Y` factors through `i` over
each member of an open cover of `X`, then `f` factors through `i`. -/
theorem exists_comp_eq_of_iSup_eq_top {X Y Z : SheafyPreAdicSpace.{u}} (i : Z ⟶ Y) [Mono i]
    (f : X ⟶ Y) {ι : Type w} (U : ι → Opens X.obj) (hU : ⨆ k, U k = ⊤)
    (g : ∀ k, X.obj.restrict (U k).isOpenEmbedding ⟶ Z.obj)
    (hg : ∀ k, g k ≫ i.hom = X.obj.ofRestrict (U k).isOpenEmbedding ≫ f.hom) :
    ∃ g' : X ⟶ Z, g' ≫ i = f := by
  -- the local factorisations agree on the overlaps, since `i` is a monomorphism
  have hcompat : ∀ k l, pullback.fst (X.obj.ofRestrict (U k).isOpenEmbedding)
      (X.obj.ofRestrict (U l).isOpenEmbedding) ≫ g k = pullback.snd _ _ ≫ g l := by
    intro k l
    let P : SheafyPreAdicSpace.{u} :=
      ⟨_, PreAdicSpace.isSheafy_of_isOpenImmersion X.property
        (pullback.fst (X.obj.ofRestrict (U k).isOpenEmbedding)
          (X.obj.ofRestrict (U l).isOpenEmbedding) ≫ X.obj.ofRestrict (U k).isOpenEmbedding)⟩
    have h : (ObjectProperty.homMk (pullback.fst _ _ ≫ g k) : P ⟶ Z) ≫ i =
        ObjectProperty.homMk (pullback.snd _ _ ≫ g l) ≫ i := by
      ext1
      simp only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom,
        Category.assoc, hg, pullback.condition_assoc]
    exact congrArg InducedCategory.Hom.hom ((cancel_mono i).mp h)
  refine ⟨ObjectProperty.homMk (PreAdicSpace.glueMorphisms X.property U hU g hcompat), ?_⟩
  ext1
  refine PreAdicSpace.hom_ext_of_ofRestrict X.property U hU fun k ↦ ?_
  simp [hg]

end SheafyPreAdicSpace

end TauCeti
