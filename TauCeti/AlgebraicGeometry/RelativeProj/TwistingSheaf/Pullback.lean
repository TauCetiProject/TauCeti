/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.LineBundle.LocalBasis
public import TauCeti.AlgebraicGeometry.Modules.Pullback.Sections
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Pullback
public import TauCeti.AlgebraicGeometry.RelativeProj.TwistingSheaf.Map

/-!
# Pulling back the twisting sheaves of a relative `Proj`

Let `φ : B ⟶ A` be a morphism of graded algebras on a scheme `X` with quasi-coherent homogeneous
components, inducing `f : Proj_X(A) ⟶ Proj_X(B)` (`CategoryTheory.CommMon.relativeProjMap`), and
let `f^* 𝒪(n) ⟶ 𝒪(n)` be the glued morphism of twisting sheaves
(`CategoryTheory.CommMon.relativeProjTwistingSheafMap`). This file proves that it is an isomorphism
when, over every affine open `U` of `X`, the standard opens
`D₊(φ b)` of the images of the elements `b` of degree one of `⨁ n, Γ(Bₙ, U)` cover the chart
`Proj (⨁ n, Γ(Aₙ, U))` (Stacks, Lemma 27.11.5 (01N1), on affine charts).

Over such a standard open, the morphism sends the pullback of the standard generator `bⁿ` of
`𝒪(n)` on `D₊(b)` to the standard generator `(φ b)ⁿ` of `𝒪(n)` on `D₊(φ b)`, which is a basis of
`𝒪(n)` there. These charts also trivialize the pullback of `𝒪(n)`. A morphism out of a line
bundle sending local sections onto local bases is an isomorphism
(`AlgebraicGeometry.Scheme.Modules.isIso_of_forall_exists_bijective_smul`).

## Main results

* `CategoryTheory.CommMon.π_app_relativeProjTwistingSheafMap_app_pullbackSections`: on the
  pullback of a section, the glued morphism of twisting sheaves is computed by the chart
  components.
* `CategoryTheory.CommMon.π_app_relativeProjTwistingSheafMap_app_chartGenerator`: the glued
  morphism sends the pullback of the standard generator `bⁿ` to the standard generator `(φ b)ⁿ`.
* `CategoryTheory.CommMon.isInvertible_pullback_relativeProjTwistingSheaf`: the covering
  hypothesis makes the pullback of `𝒪(n)` invertible.
* `CategoryTheory.CommMon.isIso_relativeProjTwistingSheafMap`: the glued morphism
  `f^* 𝒪(n) ⟶ 𝒪(n)` is an isomorphism under the covering hypothesis above.

## Implementation notes

As in `TauCeti.AlgebraicGeometry.RelativeProj.TwistingSheaf.Map`, the glued modules live on
`colimit _` while `CategoryTheory.CommMon.relativeProjMap` is typed on the relative `Proj`, so the
computations on sections are explicit term chains. They are split into separate lemmas because a
single proof exceeds the heartbeat limit.

## References

* [The Stacks Project, Lemma 27.11.5 (01N1)](https://stacks.math.columbia.edu/tag/01N1)
-/

public section

open CategoryTheory Limits DirectSum

namespace TauCeti

open _root_.AlgebraicGeometry ProjectiveSpectrum.TwistingSheaf

universe u

variable {X : Scheme.{u}} {A B : CommMon (GradedObject ℕ X.Modules)}
  [∀ n, (A.X n).IsQuasicoherent] [∀ n, (B.X n).IsQuasicoherent] (φ : B ⟶ A)
  (hφ : ∀ U : X.Opens, IsAffineOpen U →
    HomogeneousIdeal.irrelevant (A.gradedSectionsGrading U) ≤
      (HomogeneousIdeal.irrelevant (B.gradedSectionsGrading U)).map
        (CommMon.gradedSectionsGradedHom φ U)) (n : ℤ)

/-- On the pullback of a section `t` of `𝒪(n)` on `Proj_X(B)`, the glued morphism of twisting
sheaves `f^* 𝒪(n) ⟶ 𝒪(n)`, followed by the projection to a chart, is the chart component applied
to the projection of `t`. -/
theorem _root_.CategoryTheory.CommMon.π_app_relativeProjTwistingSheafMap_app_pullbackSections
    (U : X.AffineZariskiSite) (W : (colimit B.relativeProjGluingData.functor).Opens)
    (t : Γ((B.relativeProjTwistingSheafGlueData n).glued, W)) :
    ((A.relativeProjTwistingSheafGlueData n).π U).app (CommMon.relativeProjMap φ hφ ⁻¹ᵁ W)
      ((CommMon.relativeProjTwistingSheafMap φ hφ n).app (CommMon.relativeProjMap φ hφ ⁻¹ᵁ W)
        (Scheme.Hom.pullbackSections (CommMon.relativeProjMap φ hφ)
          (B.relativeProjTwistingSheaf n) W t)) =
      (CommMon.relativeProjTwistingSheafMapChart φ hφ n U).app W
        (((B.relativeProjTwistingSheafGlueData n).π U).app W t) := by
  have h := congr($(CommMon.homEquiv_relativeProjTwistingSheafMap_comp_π φ hφ n U).app W t)
  -- the adjunction is stated on `colimit _` and `relativeProjMap` on `relativeProj`, so the
  -- instances of `homEquiv_unit` only match up to unfolding
  erw [Adjunction.homEquiv_unit] at h
  exact (congrArg (fun x ↦ ((A.relativeProjTwistingSheafGlueData n).π U).app _
    ((CommMon.relativeProjTwistingSheafMap φ hφ n).app _ x))
      (Scheme.Hom.pullbackSections_apply _ _ W t)).trans h

/-- Restricting the image of the pullback of `t` to a smaller open `W` is restricting the image of
the pullback of `t` over the full preimage. -/
private theorem presheaf_map_relativeProjTwistingSheafMap_app_pullbackSectionsLE
    {V : (colimit B.relativeProjGluingData.functor).Opens} {V' W : A.relativeProj.Opens}
    (hV : V' ≤ CommMon.relativeProjMap φ hφ ⁻¹ᵁ V) (i : W ⟶ V')
    (t : Γ((B.relativeProjTwistingSheafGlueData n).glued, V)) :
    (A.relativeProjTwistingSheaf n).presheaf.map i.op
        ((CommMon.relativeProjTwistingSheafMap φ hφ n).app _
          (Scheme.Hom.pullbackSectionsLE _ _ _ _ hV t)) =
      (A.relativeProjTwistingSheaf n).presheaf.map (homOfLE (i.le.trans hV)).op
        ((CommMon.relativeProjTwistingSheafMap φ hφ n).app _
          (Scheme.Hom.pullbackSections (CommMon.relativeProjMap φ hφ)
            (B.relativeProjTwistingSheaf n) _ t)) := by
  refine (congrArg (fun z ↦ (A.relativeProjTwistingSheaf n).presheaf.map i.op
    ((CommMon.relativeProjTwistingSheafMap φ hφ n).app _ z))
      (Scheme.Hom.pullbackSectionsLE_apply _ _ _ _ hV t)).trans ?_
  refine (congrArg ((A.relativeProjTwistingSheaf n).presheaf.map i.op)
    (PresheafOfModules.naturality_apply (CommMon.relativeProjTwistingSheafMap φ hφ n).val
      (homOfLE hV).op _)).trans ?_
  exact (Functor.map_comp_apply _ _ _ _).symm

/-- **The glued morphism of twisting sheaves sends the standard generator `bⁿ` to `(φ b)ⁿ`**: if a
section `t` of `𝒪(n)` on `Proj_X(B)` restricts on the chart over `U` to the standard generator `bⁿ`
on `D₊(b)`, then the glued morphism sends the pullback of `t` to the standard generator `(φ b)ⁿ` on
every open inside `D₊(φ b)`. -/
theorem _root_.CategoryTheory.CommMon.π_app_relativeProjTwistingSheafMap_app_chartGenerator
    (U : X.AffineZariskiSite) {b : ⨁ n, Γ(B.X n, U.toOpens)}
    (hb : b ∈ B.gradedSectionsGrading U.toOpens 1)
    (t : Γ((B.relativeProjTwistingSheafGlueData n).glued,
      colimit.ι B.relativeProjGluingData.functor U ''ᵁ Proj.basicOpen _ b))
    (ht : ((B.relativeProjTwistingSheafGlueData n).π U).app _ t =
      Proj.twistingSheaf.chartGenerator n b hb _
        ((colimit.ι B.relativeProjGluingData.functor U).preimage_image_eq _).le)
    {W : A.relativeProj.Opens} (i : W ⟶ colimit.ι A.relativeProjGluingData.functor U ''ᵁ
      Proj.basicOpen _ (CommMon.gradedSectionsGradedHom φ U.toOpens b)) :
    ((A.relativeProjTwistingSheafGlueData n).π U).app W
      ((A.relativeProjTwistingSheaf n).presheaf.map i.op
        ((CommMon.relativeProjTwistingSheafMap φ hφ n).app _
          (Scheme.Hom.pullbackSectionsLE _ _ _ _
            (CommMon.image_basicOpen_le_preimage_relativeProjMap φ hφ U b) t))) =
      Proj.twistingSheaf.chartGenerator n _ (Graded.map_mem _ hb) _
        ((Scheme.Hom.preimage_mono _ i.le).trans
          ((colimit.ι A.relativeProjGluingData.functor U).preimage_image_eq _).le) := by
  have hVA := CommMon.image_basicOpen_le_preimage_relativeProjMap φ hφ U b
  -- restriction to `W` of the sections of the chart `𝒪(n)` over the preimage of the image of
  -- `D₊(b)`
  let res := ((Scheme.Modules.pushforward (colimit.ι A.relativeProjGluingData.functor U)).obj
    ((A.relativeProjTwistingSheafGlueData n).obj U)).presheaf.map (homOfLE (i.le.trans hVA)).op
  refine (congrArg (((A.relativeProjTwistingSheafGlueData n).π U).app W)
    (presheaf_map_relativeProjTwistingSheafMap_app_pullbackSectionsLE φ hφ n hVA i t)).trans ?_
  -- move the restriction to `W` past the projection `π` to the chart over `U`
  refine (PresheafOfModules.naturality_apply ((A.relativeProjTwistingSheafGlueData n).π U).val
    (homOfLE (i.le.trans hVA)).op _).trans ?_
  -- on the chart, the glued morphism is the chart component applied to the generator `bⁿ`
  refine (congrArg res
    (CommMon.π_app_relativeProjTwistingSheafMap_app_pullbackSections φ hφ n U _ t)).trans ?_
  rw [ht]
  refine (congrArg res (CommMon.relativeProjTwistingSheafMapChart_app_apply φ hφ n U _ _)).trans ?_
  -- the chart component sends `bⁿ` to `(φ b)ⁿ`
  refine (congrArg (fun z ↦ res
    ((Proj.twistingSheaf (A.gradedSectionsGrading U.toOpens) n).presheaf.map _ z))
    (Proj.twistingSheafMap_app_chartGenerator _ (hφ U.toOpens U.2) n hb _)).trans ?_
  -- and `(φ b)ⁿ` restricts to `(φ b)ⁿ`
  exact (Functor.map_comp_apply (Proj.twistingSheaf (A.gradedSectionsGrading U.toOpens) n).presheaf
    _ (homOfLE (Scheme.Hom.preimage_mono _ (i.le.trans hVA))).op _).symm.trans
      (Proj.twistingSheaf.res_chartGenerator _ _ _ _ _ _)

/-- The pullback of a relative twisting sheaf is invertible if the degree-one target charts
cover the source charts, even if the twisting sheaf is not invertible everywhere on the target. -/
theorem _root_.CategoryTheory.CommMon.isInvertible_pullback_relativeProjTwistingSheaf
    (h : ∀ (U : X.AffineZariskiSite) (y : Proj (A.gradedSectionsGrading U.toOpens)),
      ∃ b ∈ B.gradedSectionsGrading U.toOpens 1,
        y ∈ Proj.basicOpen _ (CommMon.gradedSectionsGradedHom φ U.toOpens b)) :
    AlgebraicGeometry.SheafOfModules.isInvertible A.relativeProj
      ((Scheme.Modules.pullback (CommMon.relativeProjMap φ hφ)).obj
        (B.relativeProjTwistingSheaf n)) := by
  have localTriviality (x : A.relativeProj) : ∃ (W : A.relativeProj.Opens) (_ : x ∈ W),
      Nonempty (SheafOfModules.unit W.toScheme.ringCatSheaf ≅
        ((Scheme.Modules.pullback (CommMon.relativeProjMap φ hφ)).obj
          (B.relativeProjTwistingSheaf n)).restrict W.ι) := by
    obtain ⟨U, y, hy⟩ : ∃ U : X.AffineZariskiSite,
        ∃ y : Proj (A.gradedSectionsGrading U.toOpens), A.relativeProjCover.f U y = x :=
      A.relativeProjCover.exists_eq x
    obtain ⟨b, hb, hyb⟩ := h U y
    let g : Proj (B.gradedSectionsGrading U.toOpens) ⟶ B.relativeProj := B.relativeProjCover.f U
    have : IsOpenImmersion g := B.isOpenImmersion_relativeProjCover_f U
    let V := Proj.basicOpen (B.gradedSectionsGrading U.toOpens) b
    let W : A.relativeProj.Opens := colimit.ι A.relativeProjGluingData.functor U ''ᵁ
      Proj.basicOpen _ (CommMon.gradedSectionsGradedHom φ U.toOpens b)
    have hW : W ≤ CommMon.relativeProjMap φ hφ ⁻¹ᵁ (g ''ᵁ V) :=
      CommMon.image_basicOpen_le_preimage_relativeProjMap φ hφ U b
    -- Transport the standard trivialization from D₊(b) to its image in the relative Proj.
    let e : SheafOfModules.unit V.toScheme.ringCatSheaf ≅
        (Proj.twistingSheaf (B.gradedSectionsGrading U.toOpens) n).restrict V.ι :=
      TauCeti.SheafOfModules.LocalTrivializations.unitIsoRestrict
        (M := Proj.twistingSheaf (B.gradedSectionsGrading U.toOpens) n)
        (TauCeti.SheafOfModules.freePUnitIsoUnit _ ≪≫ Proj.twistingSheaf.chartIso n b hb)
    let eV : SheafOfModules.unit (g ''ᵁ V).toScheme.ringCatSheaf ≅
        (B.relativeProjTwistingSheaf n).restrict (g ''ᵁ V).ι :=
      Scheme.Modules.unitIsoRestrictImage g V
        (e ≪≫ (Scheme.Modules.restrictFunctor V.ι).mapIso
          (B.restrictRelativeProjTwistingSheafIso n U).symm)
    -- Restriction of pullback is pullback of restriction along W → D₊(b).
    exact ⟨W, hy ▸ ⟨y, hyb, rfl⟩,
      ⟨Scheme.Modules.unitIsoRestrictPullback (CommMon.relativeProjMap φ hφ) hW eV⟩⟩
  choose W hx e using localTriviality
  exact AlgebraicGeometry.SheafOfModules.isInvertible_iff_exists_isOpenCover.mpr
    ⟨A.relativeProj, W, TopologicalSpace.IsOpenCover.mk
      (top_unique fun x _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hx x⟩), e⟩

/-- **The pullback of `𝒪(n)` along `Proj_X(A) ⟶ Proj_X(B)` is `𝒪(n)`**: if, over every affine open
`U` of `X`, the chart `Proj (⨁ n, Γ(Aₙ, U))` is covered by
the standard opens `D₊(φ b)` of the images of the elements `b` of degree one of `⨁ n, Γ(Bₙ, U)`,
then the glued morphism of twisting sheaves `f^* 𝒪(n) ⟶ 𝒪(n)` is an isomorphism. -/
theorem _root_.CategoryTheory.CommMon.isIso_relativeProjTwistingSheafMap
    (h : ∀ (U : X.AffineZariskiSite) (y : Proj (A.gradedSectionsGrading U.toOpens)),
      ∃ b ∈ B.gradedSectionsGrading U.toOpens 1,
        y ∈ Proj.basicOpen _ (CommMon.gradedSectionsGradedHom φ U.toOpens b)) :
    IsIso (CommMon.relativeProjTwistingSheafMap φ hφ n) := by
  have := CommMon.isInvertible_pullback_relativeProjTwistingSheaf φ hφ n h
  refine Scheme.Modules.isIso_of_forall_exists_bijective_smul _ fun x ↦ ?_
  obtain ⟨y, hy⟩ := A.relativeProjCover.covers x
  obtain ⟨b, hb, hyb⟩ := h (A.relativeProjCover.idx x) y
  generalize A.relativeProjCover.idx x = U at y hy b hb hyb
  -- `U` has the index type of the cover, which is `X.AffineZariskiSite` only after unfolding, so
  -- instance search does not find the open immersion instance for its charts
  have := A.isOpenImmersion_colimit_ι_relativeProjGluingData U
  have := B.isOpenImmersion_colimit_ι_relativeProjGluingData U
  obtain ⟨t, ht⟩ := ((B.relativeProjTwistingSheafGlueData n).bijective_π_app
    (B.bijective_relativeProjTwistingSheafGlueData_map_app n)
    ((colimit.ι B.relativeProjGluingData.functor U).image_le_opensRange
      (Proj.basicOpen _ b))).2
    (Proj.twistingSheaf.chartGenerator n b hb _
      ((colimit.ι B.relativeProjGluingData.functor U).preimage_image_eq _).le)
  refine ⟨_, hy ▸ ⟨y, hyb, rfl⟩, Scheme.Hom.pullbackSectionsLE _ _ _ _
    (CommMon.image_basicOpen_le_preimage_relativeProjMap φ hφ U b) t, fun W i ↦ ?_⟩
  have hWA : W ≤ (colimit.ι A.relativeProjGluingData.functor U).opensRange :=
    i.le.trans ((colimit.ι A.relativeProjGluingData.functor U).image_le_opensRange _)
  have hW : colimit.ι A.relativeProjGluingData.functor U ⁻¹ᵁ W ≤
      Proj.basicOpen _ (CommMon.gradedSectionsGradedHom φ U.toOpens b) :=
    (Scheme.Hom.preimage_mono _ i.le).trans
      ((colimit.ι A.relativeProjGluingData.functor U).preimage_image_eq _).le
  have := (colimit.ι A.relativeProjGluingData.functor U).isIso_app W hWA
  refine (((A.relativeProjTwistingSheafGlueData n).bijective_π_app
    (A.bijective_relativeProjTwistingSheafGlueData_map_app n) hWA).of_comp_iff' _).mp ?_
  have key (r : Γ(A.relativeProj, W)) : ((A.relativeProjTwistingSheafGlueData n).π U).app W
      (r • (A.relativeProjTwistingSheaf n).presheaf.map i.op
        ((CommMon.relativeProjTwistingSheafMap φ hφ n).app _
          (Scheme.Hom.pullbackSectionsLE _ _ _ _
            (CommMon.image_basicOpen_le_preimage_relativeProjMap φ hφ U b) t))) =
      Proj.twistingSheaf.chartSectionsLinearEquiv n _ (Graded.map_mem _ hb) _ hW
        ((colimit.ι A.relativeProjGluingData.functor U).app W r) := by
    refine (Scheme.Modules.Hom.app_smul _ r _).trans ?_
    -- the sections of the glued module and of `𝒪(n)` agree only after unfolding the definitions
    erw [CommMon.π_app_relativeProjTwistingSheafMap_app_chartGenerator φ hφ n U hb t ht i]
    exact (Proj.twistingSheaf.chartSectionsLinearEquiv_apply n _ _ _ hW _).symm
  exact Eq.mpr (congrArg Function.Bijective (funext key))
    ((Proj.twistingSheaf.chartSectionsLinearEquiv n _ (Graded.map_mem _ hb) _ hW).bijective.comp
      (ConcreteCategory.bijective_of_isIso ((colimit.ι A.relativeProjGluingData.functor U).app W)))

end TauCeti
