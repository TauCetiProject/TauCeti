/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.GradedAlgebra.SymmetricAlgebra.GradedPullback
public import TauCeti.AlgebraicGeometry.ProjectiveBundle.Basic
public import TauCeti.AlgebraicGeometry.RelativeProj.BaseChange
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

* `CategoryTheory.CommMon.relativeProjMapIso e`: an isomorphism `e : B ≅ A` of graded algebras with
  quasi-coherent homogeneous components induces an isomorphism `Proj_X(A) ≅ Proj_X(B)` of relative
  `Proj`s over `X`.
* `TauCeti.AlgebraicGeometry.ProjectiveBundles.projectiveBundle.pullbackHom g F`: the morphism
  `P(g^* F) ⟶ P(F)` over `g`.
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

namespace CategoryTheory.CommMon

open _root_.AlgebraicGeometry

variable {X : Scheme.{u}} {A B : CommMon (GradedObject ℕ X.Modules)}

/-- An isomorphism `φ : B ⟶ A` of graded algebras satisfies the irrelevant-ideal condition of
`CategoryTheory.CommMon.relativeProjMap`: it is bijective on sections over every open. -/
theorem irrelevant_le_map_of_isIso (φ : B ⟶ A) [IsIso φ] (U : X.Opens) :
    HomogeneousIdeal.irrelevant (A.gradedSectionsGrading U) ≤
      (HomogeneousIdeal.irrelevant (B.gradedSectionsGrading U)).map
        (CommMon.gradedSectionsGradedHom φ U) :=
  HomogeneousIdeal.irrelevant_le_map_of_grade_subset_range _ fun _ _ x _ ↦
    ⟨CommMon.gradedSectionsGradedHom (inv φ) U x, by
      rw [← GradedRingHom.comp_apply, ← CommMon.gradedSectionsGradedHom_comp, IsIso.inv_hom_id,
        CommMon.gradedSectionsGradedHom_id]
      rfl⟩

variable [∀ n, (A.X n).IsQuasicoherent] [∀ n, (B.X n).IsQuasicoherent]

/-- The morphism of relative `Proj`s induced by a morphism of graded algebras depends only on the
morphism, not on the proof of the irrelevant-ideal condition. -/
private theorem relativeProjMap_congr {φ ψ : B ⟶ A} (h : φ = ψ) (hφ hψ) :
    CommMon.relativeProjMap φ hφ = CommMon.relativeProjMap ψ hψ := by
  subst h
  rfl

/-- An isomorphism `e : B ≅ A` of graded algebras with quasi-coherent homogeneous components
induces an isomorphism `Proj_X(A) ≅ Proj_X(B)` of relative `Proj`s, inverse to the morphism
induced by `e⁻¹`. -/
def relativeProjMapIso (e : B ≅ A) : A.relativeProj ≅ B.relativeProj where
  hom := CommMon.relativeProjMap e.hom (fun U _ ↦ irrelevant_le_map_of_isIso e.hom U)
  inv := CommMon.relativeProjMap e.inv (fun U _ ↦ irrelevant_le_map_of_isIso e.inv U)
  hom_inv_id := by
    rw [← CommMon.relativeProjMap_comp _ _ _ _
      (fun U _ ↦ irrelevant_le_map_of_isIso (e.inv ≫ e.hom) U),
      relativeProjMap_congr e.inv_hom_id _ (fun U _ ↦ irrelevant_le_map_of_isIso (𝟙 A) U),
      CommMon.relativeProjMap_id]
  inv_hom_id := by
    rw [← CommMon.relativeProjMap_comp _ _ _ _
      (fun U _ ↦ irrelevant_le_map_of_isIso (e.hom ≫ e.inv) U),
      relativeProjMap_congr e.hom_inv_id _ (fun U _ ↦ irrelevant_le_map_of_isIso (𝟙 B) U),
      CommMon.relativeProjMap_id]

@[simp]
theorem relativeProjMapIso_hom (e : B ≅ A) :
    (relativeProjMapIso e).hom =
      CommMon.relativeProjMap e.hom (fun U _ ↦ irrelevant_le_map_of_isIso e.hom U) :=
  (rfl)

@[simp]
theorem relativeProjMapIso_inv (e : B ≅ A) :
    (relativeProjMapIso e).inv =
      CommMon.relativeProjMap e.inv (fun U _ ↦ irrelevant_le_map_of_isIso e.inv U) :=
  (rfl)

/-- The isomorphism of relative `Proj`s induced by an isomorphism of graded algebras lies over
`X`. -/
@[reassoc]
theorem relativeProjMapIso_hom_relativeProjToBase (e : B ≅ A) :
    (relativeProjMapIso e).hom ≫ B.relativeProjToBase = A.relativeProjToBase :=
  CommMon.relativeProjMap_relativeProjToBase _ _

end CategoryTheory.CommMon

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

end TauCeti.AlgebraicGeometry.ProjectiveBundles.projectiveBundle
