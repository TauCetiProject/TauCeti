/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.VectorBundle.Determinant.Pullback
public import TauCeti.AlgebraicGeometry.VectorBundle.TotalSpace

/-!
# Points of the determinant line bundle

For a finite locally free sheaf `E` of constant rank `r` on a scheme `X`, the determinant
`det E = ⋀ʳ E` is an invertible sheaf, and its geometric total space
`𝕍(det E) = Spec_X (Sym (det E)^∨)` is a geometric line bundle over `X`. This file identifies its
points: for a scheme `q : T ⟶ X` over `X`, morphisms `T ⟶ 𝕍(det E)` over `X` correspond to
global sections `𝒪_T ⟶ det (q^* E)` of the determinant of the pulled-back sheaf
(`totalSpaceDeterminantHomEquiv`). The correspondence is natural in the bundle: the map of total
spaces induced by `det a` acts on points as `det (q^* a)` acts on sections
(`totalSpaceDeterminantHomEquiv_comp_map`).

The bijection combines the section-valued universal property `totalSpaceHomEquiv` of the total
space with the base-change isomorphism `q^* (det E) ≅ det (q^* E)`
(`FiniteLocallyFreeSheaf.pullbackDeterminantIso`).

Here `𝕍(E)` means `Spec_X (Sym E^∨)`, covariantly in the sheaf of sections `E`; see
`TauCeti.AlgebraicGeometry.totalSpaceScheme`. In the convention `V(F) = Spec_X (Sym F)` of the
references, `𝕍(det E)` is `V((det E)^∨)`.

## References

* A. Grothendieck, J. Dieudonné, *Éléments de géométrie algébrique II*, 1.7.
* The Stacks Project, [Tag 01M1](https://stacks.math.columbia.edu/tag/01M1).
-/

public section

open CategoryTheory MonoidalCategory

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry FiniteLocallyFreeSheaf

universe u

noncomputable section

variable {X : Scheme.{u}} {r : ℕ}

/-- **Points of the determinant line bundle are sections of the determinant.** For a finite
locally free sheaf `E` of constant rank `r` on `X` and a scheme `q : T ⟶ X` over `X`, morphisms
`T ⟶ 𝕍(det E)` over `X` correspond to global sections `𝒪_T ⟶ det (q^* E)`. -/
def totalSpaceDeterminantHomEquiv (E : FixedRank X r) (T : Over X) :
    (T ⟶ (MorphismProperty.Over.forget _ _ X).obj ((totalSpaceScheme X).obj
      ((InvertibleSheaf.toFiniteLocallyFree X).obj ((determinant X r).obj E)))) ≃
      (𝟙_ T.left.Modules ⟶ ((determinant T.left r).obj ((FixedRank.pullback T.hom).obj E)).obj) :=
  (totalSpaceHomEquiv ((InvertibleSheaf.toFiniteLocallyFree X).obj ((determinant X r).obj E))
    T).trans
    ((Iso.refl _).homCongr (eqToIso (InvertibleSheaf.pullback_obj_obj T.hom _).symm ≪≫
      (SheafOfModules.isInvertible T.left).ι.mapIso ((pullbackDeterminantIso T.hom r).app E)))

/-- The section of `det (q^* E)` of a point `t : T ⟶ 𝕍(det E)` is its section of
`q^* (det E)`, carried across the base-change isomorphism `q^* (det E) ≅ det (q^* E)`. -/
theorem totalSpaceDeterminantHomEquiv_apply (E : FixedRank X r) (T : Over X)
    (t : T ⟶ (MorphismProperty.Over.forget _ _ X).obj ((totalSpaceScheme X).obj
      ((InvertibleSheaf.toFiniteLocallyFree X).obj ((determinant X r).obj E)))) :
    totalSpaceDeterminantHomEquiv E T t =
      totalSpaceHomEquiv ((InvertibleSheaf.toFiniteLocallyFree X).obj ((determinant X r).obj E))
          T t ≫
        eqToHom (InvertibleSheaf.pullback_obj_obj T.hom _).symm ≫
          ((pullbackDeterminantIso T.hom r).hom.app E).hom :=
  -- Unfolding the bijection leaves the identity of the conjugation by `Iso.refl`.
  Category.id_comp (totalSpaceHomEquiv
    ((InvertibleSheaf.toFiniteLocallyFree X).obj ((determinant X r).obj E)) T t ≫
      eqToHom (InvertibleSheaf.pullback_obj_obj T.hom _).symm ≫
        ((pullbackDeterminantIso T.hom r).hom.app E).hom)

/-- The point of `𝕍(det E)` of a section `s` of `det (q^* E)` is the point whose section of
`q^* (det E)` is `s` read through the inverse base-change isomorphism. -/
theorem totalSpaceDeterminantHomEquiv_symm_apply (E : FixedRank X r) (T : Over X)
    (s : 𝟙_ T.left.Modules ⟶ ((determinant T.left r).obj ((FixedRank.pullback T.hom).obj E)).obj) :
    (totalSpaceDeterminantHomEquiv E T).symm s =
      (totalSpaceHomEquiv ((InvertibleSheaf.toFiniteLocallyFree X).obj ((determinant X r).obj E))
          T).symm
        (s ≫ ((pullbackDeterminantIso T.hom r).inv.app E).hom ≫
          eqToHom (InvertibleSheaf.pullback_obj_obj T.hom _)) :=
  congrArg (totalSpaceHomEquiv
    ((InvertibleSheaf.toFiniteLocallyFree X).obj ((determinant X r).obj E)) T).symm
    (Category.id_comp (s ≫ ((pullbackDeterminantIso T.hom r).inv.app E).hom ≫
      eqToHom (InvertibleSheaf.pullback_obj_obj T.hom _)))

/-- **Naturality in the vector bundle.** Composing a point of `𝕍(det E)` with the map of total
spaces induced by `det a`, for a morphism `a : E ⟶ F` of sheaves of constant rank `r`, corresponds
to applying `det (q^* a)` to its section of `det (q^* E)`. -/
theorem totalSpaceDeterminantHomEquiv_comp_map {E F : FixedRank X r} (a : E ⟶ F) (T : Over X)
    (t : T ⟶ (MorphismProperty.Over.forget _ _ X).obj ((totalSpaceScheme X).obj
      ((InvertibleSheaf.toFiniteLocallyFree X).obj ((determinant X r).obj E)))) :
    totalSpaceDeterminantHomEquiv F T (t ≫ (MorphismProperty.Over.forget _ _ X).map
        ((totalSpaceScheme X).map
          ((InvertibleSheaf.toFiniteLocallyFree X).map ((determinant X r).map a)))) =
      totalSpaceDeterminantHomEquiv E T t ≫
        ((determinant T.left r).map ((FixedRank.pullback T.hom).map a)).hom := by
  rw [totalSpaceDeterminantHomEquiv_apply, totalSpaceDeterminantHomEquiv_apply,
    totalSpaceHomEquiv_comp_map]
  -- The base-change isomorphism is natural in the bundle.
  have h := congrArg InducedCategory.Hom.hom
    ((pullbackDeterminantIso T.hom r).hom.naturality a)
  simp only [Functor.comp_map, ObjectProperty.FullSubcategory.comp_hom,
    InvertibleSheaf.pullback_map, Category.assoc] at h
  simp only [Category.assoc]
  rw [← h, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  -- `InvertibleSheaf.toFiniteLocallyFree` is the full-subcategory inclusion `ObjectProperty.ιOfLE`,
  -- which acts on a morphism by the same underlying morphism of sheaves.
  rfl

end

end TauCeti.AlgebraicGeometry
