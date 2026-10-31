/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.VectorBundle.Free
public import TauCeti.AlgebraicGeometry.VectorBundle.TotalSpace

/-!
# Free-bundle maps act on section vectors by matrices

For a finite type `I` and a scheme `q : T ⟶ X` over `X`, a point `t : T ⟶ 𝕍(𝒪_X^I)` over `X`
of the geometric total space `𝕍(𝒪_X^I) = Spec_X (Sym (𝒪_X^I)^∨)` of the free bundle has a section
`𝒪_T ⟶ q^* 𝒪_X^I` (`totalSpaceHomEquiv`), and through Mathlib's identification
`q^* 𝒪_X^I ≅ 𝒪_T^I` (`SheafOfModules.pullbackObjFreeIso`) this section has a coordinate vector
`I → Γ(T, ⊤)` (`FiniteLocallyFreeSheaf.unitHomFreeEquiv`).

A morphism of free bundles `𝒪_X^I ⟶ 𝒪_X^J` with matrix `A` over `Γ(X, 𝒪_X)`
(`FiniteLocallyFreeSheaf.freeMatrixHom`) acts on these section vectors over `T` by the matrix
obtained by pulling back every entry of `A` along `q`
(`unitHomFreeEquiv_totalSpaceHomEquiv_comp_map`).

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

-- Mathlib's pullback of free sheaves is stated for pushforwards known to be right adjoints; the
-- adjunction is recorded for `Scheme.Modules.pushforward`, which instance search does not unfold.
local instance (T : Over X) :
    (SheafOfModules.pushforward.{u} T.hom.toRingCatSheafHom).IsRightAdjoint :=
  inferInstanceAs (Scheme.Modules.pushforward T.hom).IsRightAdjoint

/-- **Free-bundle maps act on section vectors by matrices.** For a matrix `A` over `Γ(X, 𝒪_X)`
and a scheme `q : T ⟶ X` over `X`, composing a point of `𝕍(𝒪_X^I)` with the map of total spaces
induced by the morphism `𝒪_X^I ⟶ 𝒪_X^J` of matrix `A` multiplies the coordinate vector of its
section of `q^* 𝒪_X^I ≅ 𝒪_T^I` by the matrix obtained by pulling back every entry of `A` along
`q`. -/
theorem unitHomFreeEquiv_totalSpaceHomEquiv_comp_map {I J : Type u} [Fintype I] [Fintype J]
    (A : Matrix J I Γ(X, ⊤)) (T : Over X)
    (t : T ⟶ (MorphismProperty.Over.forget _ _ X).obj ((totalSpaceScheme X).obj (free X I))) :
    unitHomFreeEquiv T.left J (totalSpaceHomEquiv (free X J) T
        (t ≫ (MorphismProperty.Over.forget _ _ X).map
          ((totalSpaceScheme X).map (freeMatrixHom A))) ≫
        (SheafOfModules.pullbackObjFreeIso T.hom.toRingCatSheafHom J).hom) =
      A.map T.hom.appTop *ᵥ unitHomFreeEquiv T.left I (totalSpaceHomEquiv (free X I) T t ≫
        (SheafOfModules.pullbackObjFreeIso T.hom.toRingCatSheafHom I).hom) := by
  rw [totalSpaceHomEquiv_comp_map]
  -- Pulling back the matrix morphism along `q` gives the pulled-back matrix.
  exact (congrArg (unitHomFreeEquiv T.left J) ((Category.assoc _ _ _).trans
    ((congrArg (_ ≫ ·) (pullback_map_freeMatrixHom_comp_pullbackObjFreeIso_hom T.hom A)).trans
      (Category.assoc _ _ _).symm))).trans (unitHomFreeEquiv_comp_freeMatrixHom _ _)

end

end TauCeti.AlgebraicGeometry
