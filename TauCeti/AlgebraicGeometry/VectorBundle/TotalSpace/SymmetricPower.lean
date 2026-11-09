/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.VectorBundle.SymmetricPower.Pullback
public import TauCeti.AlgebraicGeometry.VectorBundle.TotalSpace

/-!
# Points of the total space of a symmetric-power bundle

For a finite locally free sheaf `E` on a scheme `X` and `n : ℕ`, the symmetric power `Symⁿ E` is
finite locally free, so it has a geometric total space `𝕍(Symⁿ E) = Spec_X (Sym (Symⁿ E)^∨)`. This
file identifies its points: for a scheme `q : T ⟶ X`
over `X`, morphisms `T ⟶ 𝕍(Symⁿ E)` over `X` correspond to global sections
`𝒪_T ⟶ Symⁿ (q^* E)` of the symmetric power of the pulled-back sheaf
(`totalSpaceSymmetricPowerHomEquiv`). The correspondence is natural in the bundle: the map of
total spaces induced by `Symⁿ a` acts on points as `Symⁿ (q^* a)` acts on sections
(`totalSpaceSymmetricPowerHomEquiv_comp_map`).

The bijection combines the section-valued universal property `totalSpaceHomEquiv` of the total
space with the base-change isomorphism `q^* (Symⁿ E) ≅ Symⁿ (q^* E)`
(`FiniteLocallyFreeSheaf.pullbackSymmetricPowerIso`).

Here `𝕍(E)` means `Spec_X (Sym E^∨)`, covariantly in the sheaf of sections `E`; see
`TauCeti.AlgebraicGeometry.totalSpaceScheme`. In the convention `V(F) = Spec_X (Sym F)` of the
references, `𝕍(Symⁿ E)` is `V((Symⁿ E)^∨)`.

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

/-- **Points of the symmetric-power bundle are sections of the symmetric power.** For a finite
locally free sheaf `E` on `X`, `n : ℕ` and a scheme `q : T ⟶ X` over `X`, morphisms
`T ⟶ 𝕍(Symⁿ E)` over `X` correspond to global sections `𝒪_T ⟶ Symⁿ (q^* E)`. -/
def totalSpaceSymmetricPowerHomEquiv (n : ℕ) (E : FiniteLocallyFreeSheaf X) (T : Over X) :
    (T ⟶ (MorphismProperty.Over.forget _ _ X).obj
      ((totalSpaceScheme X).obj ((symmetricPower X n).obj E))) ≃
      (𝟙_ T.left.Modules ⟶ ((symmetricPower T.left n).obj ((pullback T.hom).obj E)).obj) :=
  (totalSpaceHomEquiv ((symmetricPower X n).obj E) T).trans
    ((Iso.refl _).homCongr (eqToIso (pullback_obj_obj T.hom _).symm ≪≫
      (Scheme.Modules.isFiniteLocallyFree T.left).ι.mapIso
        ((pullbackSymmetricPowerIso T.hom n).app E)))

/-- The section of `Symⁿ (q^* E)` of a point `t : T ⟶ 𝕍(Symⁿ E)` is its section of
`q^* (Symⁿ E)`, carried across the base-change isomorphism `q^* (Symⁿ E) ≅ Symⁿ (q^* E)`. -/
theorem totalSpaceSymmetricPowerHomEquiv_apply (n : ℕ) (E : FiniteLocallyFreeSheaf X)
    (T : Over X) (t : T ⟶ (MorphismProperty.Over.forget _ _ X).obj
      ((totalSpaceScheme X).obj ((symmetricPower X n).obj E))) :
    totalSpaceSymmetricPowerHomEquiv n E T t =
      totalSpaceHomEquiv ((symmetricPower X n).obj E) T t ≫
        eqToHom (pullback_obj_obj T.hom _).symm ≫
          ((pullbackSymmetricPowerIso T.hom n).hom.app E).hom :=
  -- Unfolding the bijection leaves the identity of the conjugation by `Iso.refl`.
  Category.id_comp (totalSpaceHomEquiv ((symmetricPower X n).obj E) T t ≫
    eqToHom (pullback_obj_obj T.hom _).symm ≫ ((pullbackSymmetricPowerIso T.hom n).hom.app E).hom)

/-- The point of `𝕍(Symⁿ E)` of a section `s` of `Symⁿ (q^* E)` is the point whose section of
`q^* (Symⁿ E)` is `s` read through the inverse base-change isomorphism. -/
theorem totalSpaceSymmetricPowerHomEquiv_symm_apply (n : ℕ) (E : FiniteLocallyFreeSheaf X)
    (T : Over X)
    (s : 𝟙_ T.left.Modules ⟶ ((symmetricPower T.left n).obj ((pullback T.hom).obj E)).obj) :
    (totalSpaceSymmetricPowerHomEquiv n E T).symm s =
      (totalSpaceHomEquiv ((symmetricPower X n).obj E) T).symm
        (s ≫ ((pullbackSymmetricPowerIso T.hom n).inv.app E).hom ≫
          eqToHom (pullback_obj_obj T.hom _)) :=
  congrArg (totalSpaceHomEquiv ((symmetricPower X n).obj E) T).symm
    (Category.id_comp (s ≫ ((pullbackSymmetricPowerIso T.hom n).inv.app E).hom ≫
      eqToHom (pullback_obj_obj T.hom _)))

/-- **Naturality in the vector bundle.** Composing a point of `𝕍(Symⁿ E)` with the map of total
spaces induced by `Symⁿ a`, for `a : E ⟶ F`, corresponds to applying `Symⁿ (q^* a)` to its
section of `Symⁿ (q^* E)`. -/
theorem totalSpaceSymmetricPowerHomEquiv_comp_map (n : ℕ) {E F : FiniteLocallyFreeSheaf X}
    (a : E ⟶ F) (T : Over X) (t : T ⟶ (MorphismProperty.Over.forget _ _ X).obj
      ((totalSpaceScheme X).obj ((symmetricPower X n).obj E))) :
    totalSpaceSymmetricPowerHomEquiv n F T (t ≫ (MorphismProperty.Over.forget _ _ X).map
        ((totalSpaceScheme X).map ((symmetricPower X n).map a))) =
      totalSpaceSymmetricPowerHomEquiv n E T t ≫
        ((symmetricPower T.left n).map ((pullback T.hom).map a)).hom := by
  rw [totalSpaceSymmetricPowerHomEquiv_apply, totalSpaceSymmetricPowerHomEquiv_apply,
    totalSpaceHomEquiv_comp_map]
  -- The base-change isomorphism is natural in the bundle.
  have h := congrArg InducedCategory.Hom.hom
    ((pullbackSymmetricPowerIso T.hom n).hom.naturality a)
  simp only [Functor.comp_map, ObjectProperty.FullSubcategory.comp_hom, pullback_map_hom,
    Category.assoc] at h
  simp only [Category.assoc]
  rw [← h, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

end

end TauCeti.AlgebraicGeometry
