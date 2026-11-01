/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.IdealSheaf.ReesAlgebra
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import TauCeti.AlgebraicGeometry.RelativeProj.Proper

/-!
# The blowup of a scheme along an ideal sheaf

Let `I ⊆ 𝒪_X` be an ideal sheaf on a scheme `X`. The *blowup* of `X` along the closed subscheme
`V(I)` is the relative `Proj` of the Rees algebra `⨁ₙ Iⁿ` of `I`
(`AlgebraicGeometry.Scheme.IdealSheafData.reesAlgebra`),

`Bl_I X = Proj_X(⨁ₙ Iⁿ) ⟶ X`.

Over an affine open `U` of `X`, the graded ring of sections `⨁ n, Γ(Iⁿ, U)` of the Rees algebra is
the Rees algebra `Γ(X, U)[I(U)t]` of the ideal `I(U) ⊆ Γ(X, U)`, with its grading by the power of
`t` (`AlgebraicGeometry.Scheme.IdealSheafData.reesAlgebraSectionsEquiv`). Consequently the part of
the blowup over `U` is the blowup `Proj Γ(X, U)[I(U)t]` of the affine scheme `U ≅ Spec Γ(X, U)`
along `V(I(U))`, whose affine charts, universal property, behaviour away from the centre and base
change are developed in the other files of this directory. When `I` is of finite type, the Rees
algebras `Γ(X, U)[I(U)t]` are finitely generated, and the blowup is proper over `X`.

## Main definitions

* `AlgebraicGeometry.Scheme.IdealSheafData.blowup I`: the blowup of `X` along `V(I)`, with
  structure morphism `AlgebraicGeometry.Scheme.IdealSheafData.blowupToBase I`.
* `AlgebraicGeometry.Scheme.IdealSheafData.blowupChart I hU`: for an affine open `U`, the open
  immersion of the affine blowup `Proj Γ(X, U)[I(U)t]` into the blowup of `X`.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.isPullback_blowupChart`: over an affine open `U`, the
  blowup of `X` along `V(I)` is the blowup `Proj Γ(X, U)[I(U)t]` of `U` along `V(I(U))`; the chart
  lies over `U` (`blowupChart_blowupToBase`) and its image is the preimage of `U`
  (`opensRange_blowupChart`).
* `AlgebraicGeometry.Scheme.IdealSheafData.isProper_blowupToBase`: the blowup along an ideal sheaf
  of finite type is proper.

## References

* [The Stacks Project, Tag 01OF](https://stacks.math.columbia.edu/tag/01OF): the blowing up of a
  scheme along a quasi-coherent sheaf of ideals as the relative `Proj` of `⨁ₙ Iⁿ`, and its
  affine-local description.
* [The Stacks Project, Lemma 02NS](https://stacks.math.columbia.edu/tag/02NS): the blowing up along
  an ideal sheaf of finite type is projective, hence proper.
* R. Hartshorne, *Algebraic Geometry*, Section II.7, *Blowing up*.
-/

public section

open CategoryTheory MonoidalCategory Limits DirectSum Polynomial

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

noncomputable section

open TauCeti.AlgebraicGeometry

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-! ### The graded isomorphism over an affine open -/

section Affine

variable {U : X.Opens} (hU : IsAffineOpen U)
include hU

/-- `reesAlgebraSectionsEquiv`, as a graded ring homomorphism. -/
private def reesAlgebraSectionsGradedHom :
    I.reesAlgebra.obj.gradedSectionsGrading U →+*ᵍ reesAlgebra.grade (I.ideal ⟨U, hU⟩) where
  __ := (I.reesAlgebraSectionsEquiv hU).toRingHom
  map_mem hx := (I.reesAlgebraSectionsEquiv_mem_grade_iff hU).mpr hx

/-- The inverse of `reesAlgebraSectionsEquiv`, as a graded ring homomorphism. -/
private def reesAlgebraSectionsGradedHomInv :
    reesAlgebra.grade (I.ideal ⟨U, hU⟩) →+*ᵍ I.reesAlgebra.obj.gradedSectionsGrading U where
  __ := (I.reesAlgebraSectionsEquiv hU).symm.toRingHom
  map_mem {_ x} hx := (I.reesAlgebraSectionsEquiv_mem_grade_iff hU).mp <| by
    convert hx using 1
    exact (I.reesAlgebraSectionsEquiv hU).apply_symm_apply x

/-- The graded form of `reesAlgebraSectionsEquiv` preserves the scalars in degree zero. -/
private lemma reesAlgebraSectionsGradedHom_algebraMap (r : Γ(X, U)) :
    (I.reesAlgebraSectionsGradedHom hU).gradedZeroRingHom
        (algebraMap Γ(X, U) (I.reesAlgebra.obj.gradedSectionsGrading U 0) r) =
      algebraMap Γ(X, U) (reesAlgebra.grade (I.ideal ⟨U, hU⟩) 0) r :=
  Subtype.ext <| by
    rw [GradedRingHom.gradedZeroRingHom_apply_coe, SetLike.GradeZero.coe_algebraMap,
      SetLike.GradeZero.coe_algebraMap]
    exact (I.reesAlgebraSectionsEquiv hU).commutes r

/-- The isomorphism of projective spectra induced by `reesAlgebraSectionsEquiv` lies over
`Spec Γ(X, U)`. -/
private lemma map_reesAlgebraSectionsGradedHom_toSpecCoeff :
    (Proj.mapIso (I.reesAlgebraSectionsGradedHom hU) (I.reesAlgebraSectionsGradedHomInv hU)
        (I.reesAlgebraSectionsEquiv hU).apply_symm_apply
        (I.reesAlgebraSectionsEquiv hU).symm_apply_apply).hom ≫
      Proj.toSpecCoeff (I.reesAlgebra.obj.gradedSectionsGrading U) =
    Proj.toSpecCoeff (reesAlgebra.grade (I.ideal ⟨U, hU⟩)) :=
  (congrArg (· ≫ _) (Proj.mapIso_hom _ _ _ _)).trans
    (Proj.map_toSpecCoeff _ _ _ (I.reesAlgebraSectionsGradedHom_algebraMap hU))

end Affine

/-! ### The blowup -/

section Blowup

/-- The **blowup** `Bl_I X` of a scheme `X` along the closed subscheme `V(I)` cut out by an ideal
sheaf `I`: the relative `Proj` of the Rees algebra `⨁ₙ Iⁿ` of `I`. It is an abbreviation, so that
the API of the relative `Proj` applies to it directly. -/
abbrev blowup : Scheme.{u} :=
  I.reesAlgebra.obj.relativeProj

/-- The structure morphism `Bl_I X ⟶ X` of the blowup of `X` along `V(I)`. -/
abbrev blowupToBase : I.blowup ⟶ X :=
  I.reesAlgebra.obj.relativeProjToBase

/-- The **affine chart of the blowup** over an affine open `U` of `X`: the open immersion of the
blowup `Proj Γ(X, U)[I(U)t]` of `Spec Γ(X, U)` along `V(I(U))` into the blowup of `X` along
`V(I)`. Its image is the preimage of `U` (`isPullback_blowupChart`). -/
def blowupChart {U : X.Opens} (hU : IsAffineOpen U) :
    Proj (reesAlgebra.grade (I.ideal ⟨U, hU⟩)) ⟶ I.blowup :=
  (Proj.mapIso (I.reesAlgebraSectionsGradedHom hU) (I.reesAlgebraSectionsGradedHomInv hU)
      (I.reesAlgebraSectionsEquiv hU).apply_symm_apply
      (I.reesAlgebraSectionsEquiv hU).symm_apply_apply).hom ≫
    I.reesAlgebra.obj.relativeProjCover.f (⟨U, hU⟩ : X.AffineZariskiSite)

instance {U : X.Opens} (hU : IsAffineOpen U) : IsOpenImmersion (I.blowupChart hU) :=
  -- instance search does not find the open immersion property of the chart of the relative `Proj`
  -- at an index written as an anonymous constructor, so it is supplied explicitly
  @IsOpenImmersion.comp _ _ _ _ _ inferInstance
    (I.reesAlgebra.obj.isOpenImmersion_relativeProjCover_f ⟨U, hU⟩)

/-- The affine chart of the blowup over `U` lies over `U`: followed by the structure morphism
of the blowup, it is the structure morphism `Proj Γ(X, U)[I(U)t] ⟶ Spec Γ(X, U)` followed by the
inclusion `Spec Γ(X, U) ≅ U ⟶ X`. -/
@[reassoc]
theorem blowupChart_blowupToBase {U : X.Opens} (hU : IsAffineOpen U) :
    I.blowupChart hU ≫ I.blowupToBase =
      Proj.toSpecCoeff (reesAlgebra.grade (I.ideal ⟨U, hU⟩)) ≫ hU.fromSpec := by
  rw [blowupChart]
  exact (Category.assoc _ _ _).trans
    ((congrArg (_ ≫ ·) (I.reesAlgebra.obj.relativeProjCover_f_relativeProjToBase ⟨U, hU⟩)).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ hU.fromSpec) (I.map_reesAlgebraSectionsGradedHom_toSpecCoeff hU))))

/-- The image of the affine chart of the blowup over `U` is the preimage of `U`. -/
theorem opensRange_blowupChart {U : X.Opens} (hU : IsAffineOpen U) :
    (I.blowupChart hU).opensRange = I.blowupToBase ⁻¹ᵁ U :=
  -- as for the `IsOpenImmersion` instance above, the open immersion property of the chart of the
  -- relative `Proj` is supplied explicitly
  (@Scheme.Hom.opensRange_comp_of_isIso _ _ _ _ _ (Iso.isIso_hom _)
    (I.reesAlgebra.obj.isOpenImmersion_relativeProjCover_f ⟨U, hU⟩)).trans
      (I.reesAlgebra.obj.relativeProjToBase_preimage ⟨U, hU⟩).symm

/-- **Over an affine open `U` of `X`, the blowup of `X` along `V(I)` is the blowup
`Proj Γ(X, U)[I(U)t]` of `U ≅ Spec Γ(X, U)` along `V(I(U))`**: the affine chart over `U` is the
base change of the blowup along the inclusion `U ⟶ X`. -/
theorem isPullback_blowupChart {U : X.Opens} (hU : IsAffineOpen U) :
    IsPullback (Proj.toSpecCoeff (reesAlgebra.grade (I.ideal ⟨U, hU⟩)) ≫ hU.isoSpec.inv)
      (I.blowupChart hU) U.ι I.blowupToBase := by
  refine (I.reesAlgebra.obj.isPullback_relativeProjCover (⟨U, hU⟩ : X.AffineZariskiSite)).of_iso'
    (Proj.mapIso (I.reesAlgebraSectionsGradedHom hU) (I.reesAlgebraSectionsGradedHomInv hU)
      (I.reesAlgebraSectionsEquiv hU).apply_symm_apply
      (I.reesAlgebraSectionsEquiv hU).symm_apply_apply) (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ?_ (Category.comp_id _).symm (by simp) (by simp)
  rw [Iso.refl_hom, Category.comp_id]
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ hU.isoSpec.inv) (I.map_reesAlgebraSectionsGradedHom_toSpecCoeff hU))

/-- **The blowup along an ideal sheaf of finite type is proper.** If the ideal `I(U)` is finitely
generated for every affine open `U` of `X`, then `Bl_I X ⟶ X` is proper. -/
theorem isProper_blowupToBase (hI : ∀ U : X.affineOpens, (I.ideal U).FG) :
    IsProper I.blowupToBase := by
  refine CommMon.isProper_relativeProjToBase (fun U hU ↦ ?_) (fun U hU ↦ ?_)
  · have : Algebra.FiniteType Γ(X, U) (_root_.reesAlgebra (I.ideal ⟨U, hU⟩)) :=
      ⟨(_root_.reesAlgebra _).fg_top.mpr (reesAlgebra.fg (hI ⟨U, hU⟩))⟩
    exact Algebra.FiniteType.equiv this (I.reesAlgebraSectionsEquiv hU).symm
  · -- the unit `𝒪_X ⟶ I⁰` of the Rees algebra is an isomorphism, so `Γ(I⁰, U) ≅ Γ(X, U)`
    refine Module.Finite.of_surjective (Functor.LaxMonoidal.ε (Scheme.Modules.sectionsFunctor U) ≫
      (Scheme.Modules.sectionsFunctor U).map I.reesAlgebra.obj.toMon.one).hom ?_
    have : IsIso (Functor.LaxMonoidal.ε (Scheme.Modules.sectionsFunctor U)) := by
      rw [Scheme.Modules.sectionsFunctor_ε]
      exact IsIso.id _
    exact (ConcreteCategory.bijective_of_isIso _).2

end Blowup

end

end AlgebraicGeometry.Scheme.IdealSheafData
