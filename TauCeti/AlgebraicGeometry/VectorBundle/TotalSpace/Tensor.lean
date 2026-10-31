/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.VectorBundle.TotalSpace

/-!
# Points of the total space of a tensor-product bundle

For finite locally free sheaves `E` and `F` on a scheme `X`, the tensor product `E ⊗ F` is finite
locally free, so it has a geometric total space `𝕍(E ⊗ F) = Spec_X (Sym (E ⊗ F)^∨)`. This file
identifies its points: for a scheme `q : T ⟶ X`
over `X`, morphisms `T ⟶ 𝕍(E ⊗ F)` over `X` correspond to global sections
`𝒪_T ⟶ q^* E ⊗ q^* F` of the tensor product of the pulled-back sheaves
(`totalSpaceTensorHomEquiv`). The correspondence is natural in both bundles: the map of total
spaces induced by `a ⊗ b` acts on points as `q^* a ⊗ q^* b` acts on sections
(`totalSpaceTensorHomEquiv_comp_map`).

The bijection combines the section-valued universal property `totalSpaceHomEquiv` of the total
space with the tensor comparison `q^* (E ⊗ F) ≅ q^* E ⊗ q^* F` of module pullback, which is an
isomorphism because `E` is quasicoherent
(`AlgebraicGeometry.Scheme.Modules.isIso_pullback_δ_of_isQuasicoherent`).

Here `𝕍(E)` means `Spec_X (Sym E^∨)`, covariantly in the sheaf of sections `E`; see
`TauCeti.AlgebraicGeometry.totalSpaceScheme`. In the convention `V(F) = Spec_X (Sym F)` of the
references, `𝕍(E ⊗ F)` is `V((E ⊗ F)^∨)`.

## References

* A. Grothendieck, J. Dieudonné, *Éléments de géométrie algébrique II*, 1.7.
* The Stacks Project, [Tag 01M1](https://stacks.math.columbia.edu/tag/01M1).
-/

public section

open CategoryTheory MonoidalCategory Functor.OplaxMonoidal

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry FiniteLocallyFreeSheaf

universe u

noncomputable section

variable {X : Scheme.{u}}

/-- **Points of the tensor-product bundle are sections of the tensor product.** For finite
locally free sheaves `E` and `F` on `X` and a scheme `q : T ⟶ X` over `X`, morphisms
`T ⟶ 𝕍(E ⊗ F)` over `X` correspond to global sections `𝒪_T ⟶ q^* E ⊗ q^* F`. -/
def totalSpaceTensorHomEquiv (E F : FiniteLocallyFreeSheaf X) (T : Over X) :
    (T ⟶ (MorphismProperty.Over.forget _ _ X).obj ((totalSpaceScheme X).obj (E ⊗ F))) ≃
      (𝟙_ T.left.Modules ⟶
        (Scheme.Modules.pullback T.hom).obj E.obj ⊗ (Scheme.Modules.pullback T.hom).obj F.obj) :=
  (totalSpaceHomEquiv (E ⊗ F) T).trans
    ((Iso.refl _).homCongr (asIso (δ (Scheme.Modules.pullback T.hom) E.obj F.obj)))

/-- The section of `q^* E ⊗ q^* F` of a point `t : T ⟶ 𝕍(E ⊗ F)` is its section of
`q^* (E ⊗ F)`, carried across the tensor comparison of pullback. -/
theorem totalSpaceTensorHomEquiv_apply (E F : FiniteLocallyFreeSheaf X) (T : Over X)
    (t : T ⟶ (MorphismProperty.Over.forget _ _ X).obj ((totalSpaceScheme X).obj (E ⊗ F))) :
    totalSpaceTensorHomEquiv E F T t =
      totalSpaceHomEquiv (E ⊗ F) T t ≫ δ (Scheme.Modules.pullback T.hom) E.obj F.obj :=
  -- Unfolding the bijection leaves the identity of the conjugation by `Iso.refl`.
  Category.id_comp (totalSpaceHomEquiv (E ⊗ F) T t ≫ δ (Scheme.Modules.pullback T.hom) E.obj F.obj)

/-- The point of `𝕍(E ⊗ F)` of a section `s` of `q^* E ⊗ q^* F` is the point whose section of
`q^* (E ⊗ F)` is `s` read through the inverse tensor comparison of pullback. -/
theorem totalSpaceTensorHomEquiv_symm_apply (E F : FiniteLocallyFreeSheaf X) (T : Over X)
    (s : 𝟙_ T.left.Modules ⟶
      (Scheme.Modules.pullback T.hom).obj E.obj ⊗ (Scheme.Modules.pullback T.hom).obj F.obj) :
    (totalSpaceTensorHomEquiv E F T).symm s =
      (totalSpaceHomEquiv (E ⊗ F) T).symm
        (s ≫ inv (δ (Scheme.Modules.pullback T.hom) E.obj F.obj)) :=
  congrArg (totalSpaceHomEquiv (E ⊗ F) T).symm
    (Category.id_comp (s ≫ inv (δ (Scheme.Modules.pullback T.hom) E.obj F.obj)))

/-- **Naturality in both bundles.** Composing a point of `𝕍(E ⊗ F)` with the map of total spaces
induced by `a ⊗ b`, for `a : E ⟶ E'` and `b : F ⟶ F'`, corresponds to applying `q^* a ⊗ q^* b` to
its section of `q^* E ⊗ q^* F`. -/
theorem totalSpaceTensorHomEquiv_comp_map {E E' F F' : FiniteLocallyFreeSheaf X} (a : E ⟶ E')
    (b : F ⟶ F') (T : Over X)
    (t : T ⟶ (MorphismProperty.Over.forget _ _ X).obj ((totalSpaceScheme X).obj (E ⊗ F))) :
    totalSpaceTensorHomEquiv E' F' T (t ≫ (MorphismProperty.Over.forget _ _ X).map
        ((totalSpaceScheme X).map (a ⊗ₘ b))) =
      totalSpaceTensorHomEquiv E F T t ≫
        ((Scheme.Modules.pullback T.hom).map a.hom ⊗ₘ
          (Scheme.Modules.pullback T.hom).map b.hom) := by
  rw [totalSpaceTensorHomEquiv_apply, totalSpaceTensorHomEquiv_apply,
    totalSpaceHomEquiv_comp_map, Category.assoc, Category.assoc]
  -- The tensor comparison of pullback is natural in both factors.
  exact congrArg (_ ≫ ·) (δ_natural (Scheme.Modules.pullback T.hom) a.hom b.hom).symm

end

end TauCeti.AlgebraicGeometry
