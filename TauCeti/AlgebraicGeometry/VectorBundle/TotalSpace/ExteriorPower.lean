/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.VectorBundle.ExteriorPower.Pullback
public import TauCeti.AlgebraicGeometry.VectorBundle.TotalSpace

/-!
# Points of the total space of an exterior-power bundle

For a finite locally free sheaf `E` on a scheme `X` and `n : ℕ`, the exterior power `⋀ⁿ E` is
finite locally free, so it has a geometric total space `𝕍(⋀ⁿ E) = Spec_X (Sym (⋀ⁿ E)^∨)`. This
file identifies its points: for a scheme `q : T ⟶ X`
over `X`, morphisms `T ⟶ 𝕍(⋀ⁿ E)` over `X` correspond to global sections
`𝒪_T ⟶ ⋀ⁿ (q^* E)` of the exterior power of the pulled-back sheaf
(`totalSpaceExteriorPowerHomEquiv`). The correspondence is natural in the bundle: the map of
total spaces induced by `⋀ⁿ a` acts on points as `⋀ⁿ (q^* a)` acts on sections
(`totalSpaceExteriorPowerHomEquiv_comp_map`).

The bijection combines the section-valued universal property `totalSpaceHomEquiv` of the total
space with the base-change isomorphism `q^* (⋀ⁿ E) ≅ ⋀ⁿ (q^* E)`
(`FiniteLocallyFreeSheaf.pullbackExteriorPowerIso`).

Here `𝕍(E)` means `Spec_X (Sym E^∨)`, covariantly in the sheaf of sections `E`; see
`TauCeti.AlgebraicGeometry.totalSpaceScheme`. In the convention `V(F) = Spec_X (Sym F)` of the
references, `𝕍(⋀ⁿ E)` is `V((⋀ⁿ E)^∨)`.

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

variable {X : Scheme.{u}}

/-- **Points of the exterior-power bundle are sections of the exterior power.** For a finite
locally free sheaf `E` on `X`, `n : ℕ` and a scheme `q : T ⟶ X` over `X`, morphisms
`T ⟶ 𝕍(⋀ⁿ E)` over `X` correspond to global sections `𝒪_T ⟶ ⋀ⁿ (q^* E)`. -/
def totalSpaceExteriorPowerHomEquiv (n : ℕ) (E : FiniteLocallyFreeSheaf X) (T : Over X) :
    (T ⟶ (MorphismProperty.Over.forget _ _ X).obj
      ((totalSpaceScheme X).obj ((exteriorPower X n).obj E))) ≃
      (𝟙_ T.left.Modules ⟶ ((exteriorPower T.left n).obj ((pullback T.hom).obj E)).obj) :=
  (totalSpaceHomEquiv ((exteriorPower X n).obj E) T).trans
    ((Iso.refl _).homCongr (eqToIso (pullback_obj_obj T.hom _).symm ≪≫
      (Scheme.Modules.isFiniteLocallyFree T.left).ι.mapIso
        ((pullbackExteriorPowerIso T.hom n).app E)))

/-- The section of `⋀ⁿ (q^* E)` of a point `t : T ⟶ 𝕍(⋀ⁿ E)` is its section of
`q^* (⋀ⁿ E)`, carried across the base-change isomorphism `q^* (⋀ⁿ E) ≅ ⋀ⁿ (q^* E)`. -/
theorem totalSpaceExteriorPowerHomEquiv_apply (n : ℕ) (E : FiniteLocallyFreeSheaf X)
    (T : Over X) (t : T ⟶ (MorphismProperty.Over.forget _ _ X).obj
      ((totalSpaceScheme X).obj ((exteriorPower X n).obj E))) :
    totalSpaceExteriorPowerHomEquiv n E T t =
      totalSpaceHomEquiv ((exteriorPower X n).obj E) T t ≫
        eqToHom (pullback_obj_obj T.hom _).symm ≫
          ((pullbackExteriorPowerIso T.hom n).hom.app E).hom :=
  -- Unfolding the bijection leaves the identity of the conjugation by `Iso.refl`.
  Category.id_comp (totalSpaceHomEquiv ((exteriorPower X n).obj E) T t ≫
    eqToHom (pullback_obj_obj T.hom _).symm ≫ ((pullbackExteriorPowerIso T.hom n).hom.app E).hom)

/-- The point of `𝕍(⋀ⁿ E)` of a section `s` of `⋀ⁿ (q^* E)` is the point whose section of
`q^* (⋀ⁿ E)` is `s` read through the inverse base-change isomorphism. -/
theorem totalSpaceExteriorPowerHomEquiv_symm_apply (n : ℕ) (E : FiniteLocallyFreeSheaf X)
    (T : Over X)
    (s : 𝟙_ T.left.Modules ⟶ ((exteriorPower T.left n).obj ((pullback T.hom).obj E)).obj) :
    (totalSpaceExteriorPowerHomEquiv n E T).symm s =
      (totalSpaceHomEquiv ((exteriorPower X n).obj E) T).symm
        (s ≫ ((pullbackExteriorPowerIso T.hom n).inv.app E).hom ≫
          eqToHom (pullback_obj_obj T.hom _)) :=
  congrArg (totalSpaceHomEquiv ((exteriorPower X n).obj E) T).symm
    (Category.id_comp (s ≫ ((pullbackExteriorPowerIso T.hom n).inv.app E).hom ≫
      eqToHom (pullback_obj_obj T.hom _)))

/-- **Naturality in the vector bundle.** Composing a point of `𝕍(⋀ⁿ E)` with the map of total
spaces induced by `⋀ⁿ a`, for `a : E ⟶ F`, corresponds to applying `⋀ⁿ (q^* a)` to its
section of `⋀ⁿ (q^* E)`. -/
theorem totalSpaceExteriorPowerHomEquiv_comp_map (n : ℕ) {E F : FiniteLocallyFreeSheaf X}
    (a : E ⟶ F) (T : Over X) (t : T ⟶ (MorphismProperty.Over.forget _ _ X).obj
      ((totalSpaceScheme X).obj ((exteriorPower X n).obj E))) :
    totalSpaceExteriorPowerHomEquiv n F T (t ≫ (MorphismProperty.Over.forget _ _ X).map
        ((totalSpaceScheme X).map ((exteriorPower X n).map a))) =
      totalSpaceExteriorPowerHomEquiv n E T t ≫
        ((exteriorPower T.left n).map ((pullback T.hom).map a)).hom := by
  rw [totalSpaceExteriorPowerHomEquiv_apply, totalSpaceExteriorPowerHomEquiv_apply,
    totalSpaceHomEquiv_comp_map]
  -- The base-change isomorphism is natural in the bundle.
  have h := congrArg InducedCategory.Hom.hom
    ((pullbackExteriorPowerIso T.hom n).hom.naturality a)
  simp only [Functor.comp_map, ObjectProperty.FullSubcategory.comp_hom, pullback_map_hom,
    Category.assoc] at h
  simp only [Category.assoc]
  rw [← h, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

end

end TauCeti.AlgebraicGeometry
