/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.VectorBundle.Free
public import TauCeti.AlgebraicGeometry.VectorBundle.TotalSpace

/-!
# Points of the total space of a free bundle, and matrices

For a finite type `I`, the points of the geometric total space `𝕍(𝒪_X^I) = Spec_X (Sym (𝒪_X^I)^∨)`
of the free bundle are coordinate vectors: for a scheme `q : T ⟶ X` over `X`, morphisms
`T ⟶ 𝕍(𝒪_X^I)` over `X` correspond to `I`-indexed families of global functions on `T`
(`totalSpaceFreeHomEquiv`). This is the section universal property `totalSpaceHomEquiv`, which
identifies points with global sections of `q^* 𝒪_X^I ≅ 𝒪_T^I`, followed by the coordinates
`FiniteLocallyFreeSheaf.unitHomFreeEquiv` of global sections of a free sheaf.

A morphism of free bundles `𝒪_X^I ⟶ 𝒪_X^J` with matrix `A` over `Γ(X, 𝒪_X)`
(`FiniteLocallyFreeSheaf.freeMatrixHom`) acts on these coordinate vectors over `T` by the matrix
obtained by pulling back every entry of `A` along `q` (`totalSpaceFreeHomEquiv_comp_map`).

## References

* The Stacks Project, [Tag 01M1](https://stacks.math.columbia.edu/tag/01M1).
* A. Grothendieck, J. Dieudonné, *Éléments de géométrie algébrique II*, 1.7.
-/

public section

open CategoryTheory Matrix

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry FiniteLocallyFreeSheaf

universe u

noncomputable section

variable {X : Scheme.{u}}

/-- **Points of the total space of a free bundle are coordinate vectors.** For a finite type `I`
and a scheme `q : T ⟶ X` over `X`, morphisms `T ⟶ 𝕍(𝒪_X^I)` over `X` correspond to `I`-indexed
families of global functions on `T`: the coordinates of the section of `q^* 𝒪_X^I ≅ 𝒪_T^I` given
by `totalSpaceHomEquiv`. -/
def totalSpaceFreeHomEquiv (I : Type u) [Fintype I] (T : Over X) :
    (T ⟶ (MorphismProperty.Over.forget _ _ X).obj ((totalSpaceScheme X).obj (free X I))) ≃
      (I → Γ(T.left, ⊤)) :=
  letI : (SheafOfModules.pushforward.{u} T.hom.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (Scheme.Modules.pushforward T.hom).IsRightAdjoint
  (totalSpaceHomEquiv (free X I) T).trans <|
    ((Iso.refl _).homCongr (SheafOfModules.pullbackObjFreeIso T.hom.toRingCatSheafHom I :
      (Scheme.Modules.pullback T.hom).obj (free X I).obj ≅ (free T.left I).obj)).trans
      (unitHomFreeEquiv T.left I).toEquiv

/-- The coordinates of a point `t : T ⟶ 𝕍(𝒪_X^I)` are those of its section of `q^* 𝒪_X^I`,
transported to `𝒪_T^I`. -/
lemma totalSpaceFreeHomEquiv_apply (I : Type u) [Fintype I] (T : Over X)
    (t : T ⟶ (MorphismProperty.Over.forget _ _ X).obj ((totalSpaceScheme X).obj (free X I))) :
    letI : (SheafOfModules.pushforward.{u} T.hom.toRingCatSheafHom).IsRightAdjoint :=
      inferInstanceAs (Scheme.Modules.pushforward T.hom).IsRightAdjoint
    totalSpaceFreeHomEquiv I T t =
      unitHomFreeEquiv T.left I (totalSpaceHomEquiv (free X I) T t ≫
        (SheafOfModules.pullbackObjFreeIso T.hom.toRingCatSheafHom I).hom) :=
  -- Unfolding `Iso.homCongr` along the identity of `𝒪_T` leaves a composite with `𝟙 𝒪_T`.
  congrArg (unitHomFreeEquiv T.left I) ((Iso.homCongr_apply _ _ _).trans (Category.id_comp _))

/-- The point of `𝕍(𝒪_X^I)` with coordinates `v` is the point whose section of `q^* 𝒪_X^I` is the
global section of `𝒪_T^I` with coordinates `v`, transported to `q^* 𝒪_X^I`. -/
lemma totalSpaceFreeHomEquiv_symm_apply (I : Type u) [Fintype I] (T : Over X)
    (v : I → Γ(T.left, ⊤)) :
    letI : (SheafOfModules.pushforward.{u} T.hom.toRingCatSheafHom).IsRightAdjoint :=
      inferInstanceAs (Scheme.Modules.pushforward T.hom).IsRightAdjoint
    (totalSpaceFreeHomEquiv I T).symm v =
      (totalSpaceHomEquiv (free X I) T).symm ((unitHomFreeEquiv T.left I).symm v ≫
        (SheafOfModules.pullbackObjFreeIso T.hom.toRingCatSheafHom I).inv) :=
  letI : (SheafOfModules.pushforward.{u} T.hom.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (Scheme.Modules.pushforward T.hom).IsRightAdjoint
  (Equiv.symm_apply_eq _).2 <| Eq.symm <| (totalSpaceFreeHomEquiv_apply I T _).trans <|
    (congrArg (unitHomFreeEquiv T.left I) ((congrArg (· ≫ _) (Equiv.apply_symm_apply _ _)).trans
      ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (Iso.inv_hom_id _)).trans
        (Category.comp_id _))))).trans (AddEquiv.apply_symm_apply _ _)

/-- **Free-bundle maps act on points by matrices.** For a matrix `A` over `Γ(X, 𝒪_X)` and a
scheme `q : T ⟶ X` over `X`, composing a point of `𝕍(𝒪_X^I)` with the map of total spaces induced
by the morphism `𝒪_X^I ⟶ 𝒪_X^J` of matrix `A` multiplies its coordinate vector by the matrix
obtained by pulling back every entry of `A` along `q`. -/
theorem totalSpaceFreeHomEquiv_comp_map {I J : Type u} [Fintype I] [Fintype J]
    (A : Matrix J I Γ(X, ⊤)) (T : Over X)
    (t : T ⟶ (MorphismProperty.Over.forget _ _ X).obj ((totalSpaceScheme X).obj (free X I))) :
    totalSpaceFreeHomEquiv J T (t ≫ (MorphismProperty.Over.forget _ _ X).map
        ((totalSpaceScheme X).map (freeMatrixHom A))) =
      A.map T.hom.appTop *ᵥ totalSpaceFreeHomEquiv I T t := by
  rw [totalSpaceFreeHomEquiv_apply, totalSpaceFreeHomEquiv_apply, totalSpaceHomEquiv_comp_map]
  -- Pulling back the matrix morphism along `q` gives the pulled-back matrix.
  exact (congrArg (unitHomFreeEquiv T.left J) ((Category.assoc _ _ _).trans
    ((congrArg (_ ≫ ·) (pullback_map_freeMatrixHom T.hom A)).trans
      (Category.assoc _ _ _).symm))).trans (unitHomFreeEquiv_comp_freeMatrixHom _ _)

end

end TauCeti.AlgebraicGeometry
