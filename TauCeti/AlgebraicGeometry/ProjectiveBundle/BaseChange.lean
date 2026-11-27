/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.GradedAlgebra.SymmetricAlgebra.GradedPullback
public import TauCeti.AlgebraicGeometry.ProjectiveBundle.Basic
public import TauCeti.AlgebraicGeometry.RelativeProj.BaseChange.Basic
public import TauCeti.AlgebraicGeometry.RelativeProj.Map

/-!
# Base change of projective bundles

For a morphism of schemes `g : X ⟶ Y` and a quasi-coherent module `E` on `Y`, the projective bundle
`P(g^* E) = Proj_X (Sym g^* E)` is the base change of `P(E) = Proj_Y (Sym E)` along `g`: the square

`P(g^* E) ⟶ P(E)`, `X ⟶ Y`

formed by the structure morphisms is cartesian (`ProjectiveBundles.projectiveBundle.isPullback`).

The morphism `P(g^* E) ⟶ P(E)` is the composite of the isomorphism of relative `Proj`s induced by
the isomorphism of graded algebras `g^* (Sym E) ≅ Sym (g^* E)`
(`TauCeti.AlgebraicGeometry.pullbackGradedSymmetricAlgebraIso`) with the projection
`Proj_X (g^* Sym E) ⟶ Proj_Y (Sym E)` of the base change of relative `Proj`
(`GradedQuasicoherentAlgebra.relativeProjPullbackHom`), which is cartesian over `g` by
`GradedQuasicoherentAlgebra.isPullback_relativeProjPullbackHom`.

## Main declarations

* `TauCeti.AlgebraicGeometry.ProjectiveBundles.projectiveBundle.pullbackHom g F`: the morphism
  `P(g^* F) ⟶ P(F)` over `g`, characterized by `relativeProjPullbackIso_inv_pullbackHom`.
* `TauCeti.AlgebraicGeometry.ProjectiveBundles.projectiveBundle.isPullback`: formation of the
  projective bundle commutes with arbitrary base change.

## References

* [The Stacks Project, Lemma 27.16.10](https://stacks.math.columbia.edu/tag/01O3), for base change
  of relative `Proj`.
* [The Stacks Project, Section 27.21, Projective bundles](https://stacks.math.columbia.edu/tag/01OA)
-/

public section

open CategoryTheory Limits

noncomputable section

universe u

namespace TauCeti.AlgebraicGeometry.ProjectiveBundles.projectiveBundle

open _root_.AlgebraicGeometry GradedQuasicoherentAlgebra

variable {X Y : Scheme.{u}} (g : X ⟶ Y) (F : QuasicoherentSheaf Y)

/-- The projective bundle of the pullback `g^* F` is the relative `Proj` of the pullback of the
graded symmetric algebra of `F`: the isomorphism of relative `Proj`s induced by
`g^* (Sym F) ≅ Sym (g^* F)`. -/
def relativeProjPullbackIso :
    projectiveBundle X ((QuasicoherentSheaf.pullback g).obj F).obj ≅
      ((GradedQuasicoherentAlgebra.pullback g).obj
        ((gradedSymmetricAlgebra Y).obj F)).obj.relativeProj :=
  CommMon.relativeProjMapIso
    ((ObjectProperty.ι _).mapIso (pullbackGradedSymmetricAlgebraIso g F))

/-- The isomorphism `relativeProjPullbackIso` lies over `X`. -/
@[reassoc (attr := simp)]
theorem relativeProjPullbackIso_hom_relativeProjToBase :
    (relativeProjPullbackIso g F).hom ≫
        ((GradedQuasicoherentAlgebra.pullback g).obj
          ((gradedSymmetricAlgebra Y).obj F)).obj.relativeProjToBase =
      projection X ((QuasicoherentSheaf.pullback g).obj F).obj :=
  CommMon.relativeProjMapIso_hom_relativeProjToBase _

/-- The morphism `P(g^* F) ⟶ P(F)` of projective bundles over `g : X ⟶ Y`: the identification of
`P(g^* F)` with the relative `Proj` of `g^* (Sym F)`, followed by the projection of the base
change of relative `Proj`. -/
def pullbackHom :
    projectiveBundle X ((QuasicoherentSheaf.pullback g).obj F).obj ⟶ projectiveBundle Y F.obj :=
  (relativeProjPullbackIso g F).hom ≫ relativeProjPullbackHom ((gradedSymmetricAlgebra Y).obj F) g

/-- Through the identification `relativeProjPullbackIso`, the morphism `pullbackHom` is the
projection `Proj_X (g^* Sym F) ⟶ Proj_Y (Sym F)` of the base change of relative `Proj`. -/
@[reassoc (attr := simp)]
theorem relativeProjPullbackIso_inv_pullbackHom :
    (relativeProjPullbackIso g F).inv ≫ pullbackHom g F =
      relativeProjPullbackHom ((gradedSymmetricAlgebra Y).obj F) g :=
  Iso.inv_hom_id_assoc _ _

/-- **Formation of the projective bundle commutes with arbitrary base change.** For a morphism of
schemes `g : X ⟶ Y` and a quasi-coherent module `F` on `Y`, the square formed by
`P(g^* F) ⟶ P(F)`, the structure morphisms and `g` is cartesian. -/
theorem isPullback :
    IsPullback (projection X ((QuasicoherentSheaf.pullback g).obj F).obj) (pullbackHom g F) g
      (projection Y F.obj) := by
  have h := (isPullback_relativeProjPullbackHom ((gradedSymmetricAlgebra Y).obj F) g).flip
  have h₀ : IsPullback (relativeProjPullbackIso g F).hom
      (projection X ((QuasicoherentSheaf.pullback g).obj F).obj)
      ((GradedQuasicoherentAlgebra.pullback g).obj
        ((gradedSymmetricAlgebra Y).obj F)).obj.relativeProjToBase (𝟙 X) :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  have h' := (h₀.paste_horiz h).flip
  rw [Category.id_comp] at h'
  exact h'

/-- The morphism `P(g^* F) ⟶ P(F)` lies over `g : X ⟶ Y`. -/
@[reassoc (attr := simp)]
theorem pullbackHom_projection :
    pullbackHom g F ≫ projection Y F.obj =
      projection X ((QuasicoherentSheaf.pullback g).obj F).obj ≫ g :=
  (isPullback g F).w.symm

end TauCeti.AlgebraicGeometry.ProjectiveBundles.projectiveBundle
