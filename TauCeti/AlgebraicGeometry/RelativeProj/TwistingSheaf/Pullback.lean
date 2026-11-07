/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.LineBundle.LocalBasis
public import TauCeti.AlgebraicGeometry.LineBundle.Pullback
public import TauCeti.AlgebraicGeometry.Modules.Pullback.Sections
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Pullback
public import TauCeti.AlgebraicGeometry.RelativeProj.TwistingSheaf.Map

/-!
# Pulling back the twisting sheaves of a relative `Proj`

Let `φ : B ⟶ A` be a morphism of graded algebras on a scheme `X` with quasi-coherent homogeneous
components, inducing `f : Proj_X(A) ⟶ Proj_X(B)` (`CategoryTheory.CommMon.relativeProjMap`), and
let `f^* 𝒪(n) ⟶ 𝒪(n)` be the glued morphism of twisting sheaves
(`CategoryTheory.CommMon.relativeProjTwistingSheafMap`). This file proves that it is an isomorphism
when `𝒪(n)` is invertible on `Proj_X(B)` and, over every affine open `U` of `X`, the standard opens
`D₊(φ b)` of the images of the elements `b` of degree one of `⨁ n, Γ(Bₙ, U)` cover the chart
`Proj (⨁ n, Γ(Aₙ, U))` (Stacks, Lemma 27.11.5 (01N1), on affine charts).

Over such a standard open, the morphism sends the pullback of the standard generator `bⁿ` of
`𝒪(n)` on `D₊(b)` to the standard generator `(φ b)ⁿ` of `𝒪(n)` on `D₊(φ b)`, which is a basis of
`𝒪(n)` there. A morphism out of a line bundle sending local sections onto local bases is an
isomorphism (`AlgebraicGeometry.Scheme.Modules.isIso_of_forall_exists_bijective_smul`).

## Main results

* `CategoryTheory.CommMon.π_app_relativeProjTwistingSheafMap_app_pullbackSections`: on the
  pullback of a section, the glued morphism of twisting sheaves is computed by the chart
  components.
* `CategoryTheory.CommMon.image_basicOpen_le_preimage_relativeProjMap`: the morphism of relative
  `Proj`s maps the image of `D₊(φ b)` into the image of `D₊(b)`.
* `CategoryTheory.CommMon.π_app_relativeProjTwistingSheafMap_app_chartGenerator`: the glued
  morphism sends the pullback of the standard generator `bⁿ` to the standard generator `(φ b)ⁿ`.
* `CategoryTheory.CommMon.isIso_relativeProjTwistingSheafMap`: the glued morphism
  `f^* 𝒪(n) ⟶ 𝒪(n)` is an isomorphism when `𝒪(n)` is invertible on `Proj_X(B)` and the
  covering hypothesis above holds.

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

open _root_.AlgebraicGeometry

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

/-- The morphism of relative `Proj`s maps the image of `D₊(φ b)` in the chart of `Proj_X(A)` over
`U` into the image of `D₊(b)` in the chart of `Proj_X(B)` over `U`. -/
theorem _root_.CategoryTheory.CommMon.image_basicOpen_le_preimage_relativeProjMap
    (U : X.AffineZariskiSite) (b : ⨁ n, Γ(B.X n, U.toOpens)) :
    colimit.ι A.relativeProjGluingData.functor U ''ᵁ
        Proj.basicOpen _ (CommMon.gradedSectionsGradedHom φ U.toOpens b) ≤
      CommMon.relativeProjMap φ hφ ⁻¹ᵁ
        (colimit.ι B.relativeProjGluingData.functor U ''ᵁ Proj.basicOpen _ b) := by
  rintro _ ⟨z, hz, rfl⟩
  exact ⟨Proj.map _ (hφ U.toOpens U.2) z, hz, congr($(CommMon.ι_relativeProjMap φ hφ U) z).symm⟩

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
  have hnat {Y : Scheme.{u}} {P Q : Y.Modules} (α : P ⟶ Q) {V V' : Y.Opens} (j : V ⟶ V')
      (z : Γ(P, V')) : α.app V (P.presheaf.map j.op z) = Q.presheaf.map j.op (α.app V' z) := by
    simpa only [Scheme.Modules.mapPresheaf_app, Opposite.unop_op] using
      α.mapPresheaf.naturality_apply j.op z
  have hres {Y : Scheme.{u}} {P : Y.Modules} {V₁ V₂ V₃ : Y.Opens} (j₁ : V₁ ⟶ V₂) (j₂ : V₂ ⟶ V₃)
      (z : Γ(P, V₃)) :
      P.presheaf.map j₁.op (P.presheaf.map j₂.op z) = P.presheaf.map (j₁ ≫ j₂).op z := by
    rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
  have e1 : (A.relativeProjTwistingSheaf n).presheaf.map i.op
      ((CommMon.relativeProjTwistingSheafMap φ hφ n).app _
        (Scheme.Hom.pullbackSectionsLE _ _ _ _ hVA t)) =
      (A.relativeProjTwistingSheaf n).presheaf.map (homOfLE (i.le.trans hVA)).op
        ((CommMon.relativeProjTwistingSheafMap φ hφ n).app _
          (Scheme.Hom.pullbackSections (CommMon.relativeProjMap φ hφ)
            (B.relativeProjTwistingSheaf n) _ t)) := by
    refine (congrArg (fun z ↦ (A.relativeProjTwistingSheaf n).presheaf.map i.op
      ((CommMon.relativeProjTwistingSheafMap φ hφ n).app _ z))
        (Scheme.Hom.pullbackSectionsLE_apply _ _ _ _ hVA t)).trans ?_
    refine (congrArg ((A.relativeProjTwistingSheaf n).presheaf.map i.op)
      (hnat _ (homOfLE hVA) _)).trans ?_
    exact hres _ _ _
  rw [e1]
  refine (hnat ((A.relativeProjTwistingSheafGlueData n).π U) _ _).trans ?_
  refine (congrArg (((Scheme.Modules.pushforward (colimit.ι A.relativeProjGluingData.functor U)).obj
    ((A.relativeProjTwistingSheafGlueData n).obj U)).presheaf.map (homOfLE (i.le.trans hVA)).op)
      (CommMon.π_app_relativeProjTwistingSheafMap_app_pullbackSections φ hφ n U _ t)).trans ?_
  rw [ht]
  refine (congrArg (((Scheme.Modules.pushforward (colimit.ι A.relativeProjGluingData.functor U)).obj
    ((A.relativeProjTwistingSheafGlueData n).obj U)).presheaf.map (homOfLE (i.le.trans hVA)).op)
      (CommMon.relativeProjTwistingSheafMapChart_app_apply φ hφ n U _ _)).trans ?_
  refine (congrArg (fun z ↦ ((Scheme.Modules.pushforward
    (colimit.ι A.relativeProjGluingData.functor U)).obj
      ((A.relativeProjTwistingSheafGlueData n).obj U)).presheaf.map (homOfLE (i.le.trans hVA)).op
        ((Proj.twistingSheaf (A.gradedSectionsGrading U.toOpens) n).presheaf.map _ z))
    (Proj.twistingSheafMap_app_chartGenerator _ (hφ U.toOpens U.2) n hb _)).trans ?_
  exact (hres (P := Proj.twistingSheaf (A.gradedSectionsGrading U.toOpens) n)
    (homOfLE (Scheme.Hom.preimage_mono _ (i.le.trans hVA))) _ _).trans
      (Proj.twistingSheaf.res_chartGenerator _ _ _ _ _ _)

/-- **The pullback of `𝒪(n)` along `Proj_X(A) ⟶ Proj_X(B)` is `𝒪(n)`**: if `𝒪(n)` is invertible on
`Proj_X(B)` and, over every affine open `U` of `X`, the chart `Proj (⨁ n, Γ(Aₙ, U))` is covered by
the standard opens `D₊(φ b)` of the images of the elements `b` of degree one of `⨁ n, Γ(Bₙ, U)`,
then the glued morphism of twisting sheaves `f^* 𝒪(n) ⟶ 𝒪(n)` is an isomorphism. -/
theorem _root_.CategoryTheory.CommMon.isIso_relativeProjTwistingSheafMap
    (hB : AlgebraicGeometry.SheafOfModules.isInvertible B.relativeProj
      (B.relativeProjTwistingSheaf n))
    (h : ∀ (U : X.AffineZariskiSite) (y : Proj (A.gradedSectionsGrading U.toOpens)),
      ∃ b ∈ B.gradedSectionsGrading U.toOpens 1,
        y ∈ Proj.basicOpen _ (CommMon.gradedSectionsGradedHom φ U.toOpens b)) :
    IsIso (CommMon.relativeProjTwistingSheafMap φ hφ n) := by
  -- with `hB` as an instance, the source `f^* 𝒪(n)` is invertible by `isInvertible_pullback`
  have := hB
  refine Scheme.Modules.isIso_of_forall_exists_bijective_smul _ fun x ↦ ?_
  obtain ⟨y, hy⟩ := A.relativeProjCover.covers x
  obtain ⟨b, hb, hyb⟩ := h (A.relativeProjCover.idx x) y
  generalize A.relativeProjCover.idx x = U at y hy b hb hyb
  -- the index type of the cover is `X.AffineZariskiSite` only after unfolding
  have : IsOpenImmersion (colimit.ι A.relativeProjGluingData.functor U) :=
    A.isOpenImmersion_relativeProjCover_f U
  have : IsOpenImmersion (colimit.ι B.relativeProjGluingData.functor U) :=
    B.isOpenImmersion_relativeProjCover_f U
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
