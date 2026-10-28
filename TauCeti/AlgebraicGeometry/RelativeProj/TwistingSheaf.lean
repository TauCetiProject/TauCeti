/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Gluing
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Functor
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Localization
public import TauCeti.AlgebraicGeometry.RelativeProj.Basic

/-!
# The twisting sheaves of a relative `Proj`

Let `A` be a graded algebra on a scheme `X` with quasi-coherent homogeneous components. The
relative `Proj` of `A` is glued from the charts `Proj (⨁ n, Γ(Aₙ, U))` over the affine opens `U`
of `X`, along the morphisms `Proj (⨁ n, Γ(Aₙ, D(f))) ⟶ Proj (⨁ n, Γ(Aₙ, U))` induced by
restriction of sections to basic opens `D(f) ⊆ U`. Each chart carries its twisting sheaves `𝒪(n)`,
and these morphisms induce maps between them (`AlgebraicGeometry.Proj.twistingSheafMap`).

This file glues the twisting sheaves of the charts into the twisting sheaves `𝒪(n)`, `n ∈ ℤ`, of
the relative `Proj` (`CategoryTheory.CommMon.relativeProjTwistingSheaf`), and identifies their
restrictions to the charts with the twisting sheaves of the charts
(`CategoryTheory.CommMon.restrictRelativeProjTwistingSheafIso`). The gluing is
`TauCeti.ModulesGlueData.glued`; its input is that the maps of twisting sheaves are isomorphisms
over the overlap: the pullback of sections of `𝒪(n)` from an open `W` of `Proj (⨁ n, Γ(Aₙ, U))`
inside the locus where `f` is invertible is bijective. This holds because restriction of sections
is the localization away from `f` in degree zero
(`CategoryTheory.CommMon.isLocalization_gradedSections_basicOpen`).

## Main definitions

* `CategoryTheory.CommMon.relativeProjTwistingSheaf A n`: the twisting sheaf `𝒪(n)` on the
  relative `Proj` of `A`.
* `CategoryTheory.CommMon.restrictRelativeProjTwistingSheafIso A n U`: its restriction to the chart
  over an affine open `U` of `X` is the twisting sheaf `𝒪(n)` on `Proj (⨁ n, Γ(Aₙ, U))`.

## Main results

* `CategoryTheory.CommMon.bijective_twistingSheafMap_app_restrictGradedSections`: the map of
  twisting sheaves along a transition map of the charts of the relative `Proj` is bijective on
  sections over the locus where `f` is invertible.

## References

* [The Stacks Project, Section 27.15, Relative Proj](https://stacks.math.columbia.edu/tag/01NS)
* [The Stacks Project, Lemma 27.15.5](https://stacks.math.columbia.edu/tag/01NR)
-/

public section

open CategoryTheory DirectSum

namespace TauCeti

open _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} (A : CommMon (GradedObject ℕ X.Modules)) [∀ n, (A.X n).IsQuasicoherent]

section BasicOpen

variable {U : X.Opens} (hU : IsAffineOpen U) (f : Γ(X, U))
include hU

/-- **The twisting sheaves of the charts of the relative `Proj` agree on overlaps.** For an affine
open `U` of `X` and `f ∈ Γ(X, U)`, the map of twisting sheaves `𝒪(n)` along
`Proj (⨁ n, Γ(Aₙ, D(f))) ⟶ Proj (⨁ n, Γ(Aₙ, U))` is bijective on sections over every open `W` of
`Proj (⨁ n, Γ(Aₙ, U))` on which the image of `f` in degree zero is invertible. -/
theorem _root_.CategoryTheory.CommMon.bijective_twistingSheafMap_app_restrictGradedSections
    (i : X.basicOpen f ⟶ U) (n : ℤ) {W : (Proj (A.gradedSectionsGrading U)).Opens}
    (hW : W ≤ Proj.basicOpen _ (algebraMap Γ(X, U) (⨁ n, Γ(A.X n, U)) f)) :
    Function.Bijective ((Proj.twistingSheafMap (A.restrictGradedSectionsGradedHom i)
      (A.irrelevant_le_map_restrictGradedSectionsGradedHom f hU i) n).app W) := by
  have := Subsingleton.elim i (homOfLE (X.basicOpen_le f))
  subst this
  simp only [Proj.twistingSheafMap_app]
  exact Proj.twistingSheaf.bijective_comap_of_isLocalizationAway _ _
    (SetLike.algebraMap_mem_graded _ f) (by
      rw [CommMon.restrictGradedSectionsGradedHom_toRingHom]
      exact A.isLocalization_gradedSections_basicOpen hU f) hW

end BasicOpen

open Scheme.AffineZariskiSite

/-- The gluing datum of the twisting sheaves `𝒪(n)` of the charts `Proj (⨁ n, Γ(Aₙ, U))` of the
relative `Proj`, with the maps of twisting sheaves induced by restriction of sections. -/
@[expose, simps]
noncomputable def _root_.CategoryTheory.CommMon.relativeProjTwistingSheafGlueData (n : ℤ) :
    ModulesGlueData A.relativeProjGluingData.functor where
  obj U := Proj.twistingSheaf (A.gradedSectionsGrading U.toOpens) n
  map i := Proj.twistingSheafMap (A.restrictGradedSectionsGradedHom ((toOpensFunctor X).map i))
    (A.irrelevant_le_map_restrictGradedSectionsGradedHom_toOpensFunctor i) n
  map_id _ := Proj.twistingSheafMap_app_apply_of_eq_id _ _
    ((congrArg A.restrictGradedSectionsGradedHom (Subsingleton.elim _ (𝟙 _))).trans
      (A.restrictGradedSectionsGradedHom_id _)) n
  map_comp i j := Proj.twistingSheafMap_app_apply_of_eq_comp _ _ _ _ _ _
    ((congrArg A.restrictGradedSectionsGradedHom ((toOpensFunctor X).map_comp i j)).trans
      (A.restrictGradedSectionsGradedHom_comp _ _)) n

/-- The **twisting sheaf `𝒪(n)` on the relative `Proj`** of a graded algebra `A` on `X` with
quasi-coherent homogeneous components, glued from the twisting sheaves `𝒪(n)` of the charts
`Proj (⨁ n, Γ(Aₙ, U))` over the affine opens `U` of `X`. -/
@[expose, stacks 01NR "construction only; quasi-coherence and the graded map are not yet here"]
noncomputable def _root_.CategoryTheory.CommMon.relativeProjTwistingSheaf (n : ℤ) :
    A.relativeProj.Modules :=
  (A.relativeProjTwistingSheafGlueData n).glued

/-- The twisting sheaf `𝒪(n)` on the relative `Proj` is the glued module of the gluing datum of the
twisting sheaves of the charts. -/
theorem _root_.CategoryTheory.CommMon.relativeProjTwistingSheaf_def (n : ℤ) :
    A.relativeProjTwistingSheaf n = (A.relativeProjTwistingSheafGlueData n).glued :=
  (rfl)

/-- The maps of twisting sheaves along the transition maps of the charts of the relative `Proj`
are bijective on sections over opens inside the images of the transition maps. -/
theorem _root_.CategoryTheory.CommMon.bijective_relativeProjTwistingSheafGlueData_map_app
    (n : ℤ) {U V : X.AffineZariskiSite} (i : U ⟶ V)
    (W : (A.relativeProjGluingData.functor.obj V).Opens)
    (hW : W ≤ (A.relativeProjGluingData.functor.map i).opensRange) :
    Function.Bijective (((A.relativeProjTwistingSheafGlueData n).map i).app W) := by
  obtain ⟨U, hU⟩ := U
  obtain ⟨f, rfl⟩ := leOfHom i
  refine A.bijective_twistingSheafMap_app_restrictGradedSections V.2 f _ n fun _ hw ↦ ?_
  obtain ⟨y, rfl⟩ := hW hw
  exact (A.proj_map_restrictGradedSections_preimage_basicOpen_eq_top f V.2 _).ge trivial

/-- **The restriction of `𝒪(n)` to a chart of the relative `Proj` is `𝒪(n)`**: over an affine
open `U` of `X`, the restriction of the twisting sheaf `𝒪(n)` of the relative `Proj` to the chart
`Proj (⨁ n, Γ(Aₙ, U))` is the twisting sheaf `𝒪(n)` of the chart. -/
noncomputable def _root_.CategoryTheory.CommMon.restrictRelativeProjTwistingSheafIso (n : ℤ)
    (U : X.AffineZariskiSite) :
    (A.relativeProjTwistingSheaf n).restrict (A.relativeProjCover.f U) ≅
      Proj.twistingSheaf (A.gradedSectionsGrading U.toOpens) n :=
  (A.relativeProjTwistingSheafGlueData n).restrictGluedIso
    (A.bijective_relativeProjTwistingSheafGlueData_map_app n) U

/-- The isomorphism from the restriction of `𝒪(n)` to a chart of the relative `Proj` to the
twisting sheaf of the chart is the morphism adjoint to the projection of the glued module. -/
@[simp]
theorem _root_.CategoryTheory.CommMon.restrictRelativeProjTwistingSheafIso_hom (n : ℤ)
    (U : X.AffineZariskiSite) :
    (A.restrictRelativeProjTwistingSheafIso n U).hom =
      (A.relativeProjTwistingSheafGlueData n).restrictGluedHom U :=
  ModulesGlueData.restrictGluedIso_hom _ _ U

end TauCeti
