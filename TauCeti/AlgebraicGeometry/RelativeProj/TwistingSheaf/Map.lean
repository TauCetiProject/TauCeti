/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.RelativeProj.Map
public import TauCeti.AlgebraicGeometry.RelativeProj.TwistingSheaf

/-!
# The morphism of twisting sheaves induced by a morphism of graded algebras

Let `φ : B ⟶ A` be a morphism of graded algebras on a scheme `X` with quasi-coherent homogeneous
components, inducing `Proj_X(A) ⟶ Proj_X(B)` (`CategoryTheory.CommMon.relativeProjMap`). Over
every affine open `U` of `X`, the morphism of projective spectra
`Proj (⨁ n, Γ(Aₙ, U)) ⟶ Proj (⨁ n, Γ(Bₙ, U))` induces a morphism of twisting sheaves
(`AlgebraicGeometry.Proj.twistingSheafMap`). This file pushes them forward to morphisms
`𝒪(n) ⟶ (Proj_X(A) ⟶ Proj_X(B))_* (ι_U)_* 𝒪(n)` on `Proj_X(B)`, the components from which the
morphism `(Proj_X(A) ⟶ Proj_X(B))^* 𝒪(n) ⟶ 𝒪(n)` is glued. It is the relative form of the
comparison morphism of Stacks, Lemma 27.11.5 (01N1), which on affine charts is an isomorphism when
every point of `Proj_X(A)` lies in some `D₊(φ b)` with `b` of degree one, as for the graded map
`Sym A₁ ⟶ A` of an algebra generated in degree one.

## Main definitions

* `CategoryTheory.CommMon.relativeProjTwistingSheafMapChart φ hφ n U`: over the chart above an
  affine open `U`, the morphism `(ι_U)_* 𝒪(n) ⟶ (Proj_X(A) ⟶ Proj_X(B))_* (ι_U)_* 𝒪(n)` induced by
  the morphism of twisting sheaves of `Proj (⨁ n, Γ(Aₙ, U)) ⟶ Proj (⨁ n, Γ(Bₙ, U))`.
* `CategoryTheory.CommMon.relativeProjTwistingSheafMapComponent φ hφ n U`: its adjoint
  `(Proj_X(A) ⟶ Proj_X(B))^* 𝒪(n) ⟶ (ι_U)_* 𝒪(n)`, precomposed with the projection of `𝒪(n)`.
* `CategoryTheory.CommMon.relativeProjTwistingSheafMap φ hφ n`: the glued morphism
  `(Proj_X(A) ⟶ Proj_X(B))^* 𝒪(n) ⟶ 𝒪(n)`.

## Main results

* `CategoryTheory.CommMon.relativeProjTwistingSheafMapChart_transition`: the chart components are
  compatible with the transition morphisms of the twisting sheaves of the charts, so that they
  glue.
* `CategoryTheory.CommMon.relativeProjTwistingSheafMap_comp_π`: the glued morphism, followed by
  the projection to a chart, is the adjoint chart component.
* `CategoryTheory.CommMon.homEquiv_relativeProjTwistingSheafMap_comp_π`: the morphism
  `𝒪(n) ⟶ f_* 𝒪(n)` adjoint to the glued morphism, followed by the projection to a chart, is the
  chart component.

## Implementation notes

The glued modules and the morphisms between them live on `colimit _`, which is the relative `Proj`
only after unfolding `CategoryTheory.CommMon.relativeProj`, so the pushforwards and pullbacks along
`CategoryTheory.CommMon.relativeProjMap` are stated with these colimits as explicit arguments, and
the computations on sections use `erw` and explicit term chains rather than `simp`.

## References

* [The Stacks Project, Lemma 27.11.5 (01N1)](https://stacks.math.columbia.edu/tag/01N1)
* [The Stacks Project, Section 27.15, Relative Proj](https://stacks.math.columbia.edu/tag/01NS)
-/

public section

open CategoryTheory Limits

namespace TauCeti

open _root_.AlgebraicGeometry

universe u

noncomputable section

variable {X : Scheme.{u}} {A B : CommMon (GradedObject ℕ X.Modules)}
  [∀ n, (A.X n).IsQuasicoherent] [∀ n, (B.X n).IsQuasicoherent] (φ : B ⟶ A)
  (hφ : ∀ U : X.Opens, IsAffineOpen U →
    HomogeneousIdeal.irrelevant (A.gradedSectionsGrading U) ≤
      (HomogeneousIdeal.irrelevant (B.gradedSectionsGrading U)).map
        (CommMon.gradedSectionsGradedHom φ U)) (n : ℤ)

/-- Over the chart of `Proj_X(B)` above an affine open `U` of `X`, the morphism
`(ι_U)_* 𝒪(n) ⟶ (Proj_X(A) ⟶ Proj_X(B))_* (ι_U)_* 𝒪(n)` given by the morphism of twisting
sheaves of `Proj (⨁ n, Γ(Aₙ, U)) ⟶ Proj (⨁ n, Γ(Bₙ, U))`. -/
def _root_.CategoryTheory.CommMon.relativeProjTwistingSheafMapChart (U : X.AffineZariskiSite) :
    (Scheme.Modules.pushforward (colimit.ι B.relativeProjGluingData.functor U)).obj
        ((B.relativeProjTwistingSheafGlueData n).obj U) ⟶
      (Scheme.Modules.pushforward (X := colimit A.relativeProjGluingData.functor)
        (Y := colimit B.relativeProjGluingData.functor) (CommMon.relativeProjMap φ hφ)).obj
        ((Scheme.Modules.pushforward (colimit.ι A.relativeProjGluingData.functor U)).obj
          ((A.relativeProjTwistingSheafGlueData n).obj U)) :=
  (Scheme.Modules.pushforward (colimit.ι B.relativeProjGluingData.functor U)).map
      (Proj.twistingSheafMap (CommMon.gradedSectionsGradedHom φ U.toOpens) (hφ U.toOpens U.2) n) ≫
    (Scheme.Modules.pushforwardComp
      (Proj.map (CommMon.gradedSectionsGradedHom φ U.toOpens) (hφ U.toOpens U.2))
      (colimit.ι B.relativeProjGluingData.functor U)).hom.app
        (Proj.twistingSheaf (A.gradedSectionsGrading U.toOpens) n) ≫
    (Scheme.Modules.pushforwardCongr (CommMon.ι_relativeProjMap φ hφ U).symm).hom.app
      (Proj.twistingSheaf (A.gradedSectionsGrading U.toOpens) n) ≫
    (Scheme.Modules.pushforwardComp (Z := colimit B.relativeProjGluingData.functor)
      (colimit.ι A.relativeProjGluingData.functor U) (CommMon.relativeProjMap φ hφ)).inv.app
        (Proj.twistingSheaf (A.gradedSectionsGrading U.toOpens) n)

/-- On sections, the chart component of the morphism of twisting sheaves is the morphism of
twisting sheaves of the chart, followed by the restriction along
`ι_U⁻¹ f⁻¹ W = (Proj.map _)⁻¹ ι_U⁻¹ W`. -/
theorem _root_.CategoryTheory.CommMon.relativeProjTwistingSheafMapChart_app_apply
    (U : X.AffineZariskiSite) (W : (colimit B.relativeProjGluingData.functor).Opens)
    (t : Γ(Proj.twistingSheaf (B.gradedSectionsGrading U.toOpens) n,
      colimit.ι B.relativeProjGluingData.functor U ⁻¹ᵁ W)) :
    (CommMon.relativeProjTwistingSheafMapChart φ hφ n U).app W t =
      (Proj.twistingSheaf (A.gradedSectionsGrading U.toOpens) n).presheaf.map
        (eqToHom (show colimit.ι A.relativeProjGluingData.functor U ⁻¹ᵁ
            CommMon.relativeProjMap φ hφ ⁻¹ᵁ W =
            Proj.map (CommMon.gradedSectionsGradedHom φ U.toOpens) (hφ U.toOpens U.2) ⁻¹ᵁ
              colimit.ι B.relativeProjGluingData.functor U ⁻¹ᵁ W from
          congrArg (· ⁻¹ᵁ W) (CommMon.ι_relativeProjMap φ hφ U))).op
        ((Proj.twistingSheafMap (CommMon.gradedSectionsGradedHom φ U.toOpens)
          (hφ U.toOpens U.2) n).app (colimit.ι B.relativeProjGluingData.functor U ⁻¹ᵁ W) t) :=
  (rfl)

/-- The chart components of the morphism of twisting sheaves are compatible with the transition
morphisms of the twisting sheaves of the charts. -/
theorem _root_.CategoryTheory.CommMon.relativeProjTwistingSheafMapChart_transition
    {U V : X.AffineZariskiSite} (i : U ⟶ V) :
    CommMon.relativeProjTwistingSheafMapChart φ hφ n V ≫
      (Scheme.Modules.pushforward (X := colimit A.relativeProjGluingData.functor)
        (Y := colimit B.relativeProjGluingData.functor) (CommMon.relativeProjMap φ hφ)).map
        ((A.relativeProjTwistingSheafGlueData n).transition i) =
      (B.relativeProjTwistingSheafGlueData n).transition i ≫
        CommMon.relativeProjTwistingSheafMapChart φ hφ n U := by
  refine Scheme.Modules.hom_ext _ _ fun W ↦ ConcreteCategory.hom_ext _ _ fun t ↦ ?_
  -- `relativeProjMap` is typed on `relativeProj`, the glued modules on `colimit _`, so the goal
  -- is not type-correct at instance transparency and `rw` cannot rewrite it
  erw [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply, Scheme.Modules.pushforward_map_app,
    ModulesGlueData.transition_app_apply]
  refine Eq.trans ?_ (congrArg
    (fun x ↦ (CommMon.relativeProjTwistingSheafMapChart φ hφ n U).app W x)
    ((B.relativeProjTwistingSheafGlueData n).transition_app_apply i W t)).symm
  -- by `relativeProjTwistingSheafMapChart_app_apply` and `relativeProjTwistingSheafGlueData_map`
  -- (both by definition), both sides are restrictions of morphisms of twisting sheaves of the
  -- charts along the two equal composites `res ∘ φ_V = φ_U ∘ res`
  exact Proj.res_twistingSheafMap_app_res_of_comp_eq _ (hφ V.toOpens V.2) _
    (A.irrelevant_le_map_restrictGradedSectionsGradedHom_toOpensFunctor i) _
    (B.irrelevant_le_map_restrictGradedSectionsGradedHom_toOpensFunctor i) _ (hφ U.toOpens U.2)
    (CommMon.gradedSectionsGradedHom_comp_restrictGradedSectionsGradedHom φ
      ((Scheme.AffineZariskiSite.toOpensFunctor X).map i)).symm n _ _ _ _ t

/-- The composites of the projections of `𝒪(n)` on `Proj_X(B)` with the chart components of the
morphism of twisting sheaves are compatible with the transition morphisms of the charts of
`Proj_X(A)`. -/
theorem _root_.CategoryTheory.CommMon.π_relativeProjTwistingSheafMapChart_transition
    {U V : X.AffineZariskiSite} (i : U ⟶ V) :
    (B.relativeProjTwistingSheafGlueData n).π V ≫
      CommMon.relativeProjTwistingSheafMapChart φ hφ n V ≫
        (Scheme.Modules.pushforward (X := colimit A.relativeProjGluingData.functor)
          (Y := colimit B.relativeProjGluingData.functor) (CommMon.relativeProjMap φ hφ)).map
          ((A.relativeProjTwistingSheafGlueData n).transition i) =
      (B.relativeProjTwistingSheafGlueData n).π U ≫
        CommMon.relativeProjTwistingSheafMapChart φ hφ n U := by
  rw [CommMon.relativeProjTwistingSheafMapChart_transition, ModulesGlueData.π_transition_assoc]

/-- Over the chart of `Proj_X(A)` above an affine open `U` of `X`, the morphism
`f^* 𝒪(n) ⟶ (ι_U)_* 𝒪(n)` adjoint to the chart component of the morphism of twisting sheaves. -/
def _root_.CategoryTheory.CommMon.relativeProjTwistingSheafMapComponent (U : X.AffineZariskiSite) :
    (Scheme.Modules.pullback (X := colimit A.relativeProjGluingData.functor)
        (Y := colimit B.relativeProjGluingData.functor) (CommMon.relativeProjMap φ hφ)).obj
        (B.relativeProjTwistingSheafGlueData n).glued ⟶
      (Scheme.Modules.pushforward (colimit.ι A.relativeProjGluingData.functor U)).obj
        ((A.relativeProjTwistingSheafGlueData n).obj U) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction (X := colimit A.relativeProjGluingData.functor)
    (Y := colimit B.relativeProjGluingData.functor)
    (CommMon.relativeProjMap φ hφ)).homEquiv _ _).symm
      ((B.relativeProjTwistingSheafGlueData n).π U ≫
        CommMon.relativeProjTwistingSheafMapChart φ hφ n U)

/-- The adjoint chart components of the morphism of twisting sheaves are compatible with the
transition morphisms of the charts of `Proj_X(A)`. -/
theorem _root_.CategoryTheory.CommMon.relativeProjTwistingSheafMapComponent_transition
    {U V : X.AffineZariskiSite} (i : U ⟶ V) :
    CommMon.relativeProjTwistingSheafMapComponent φ hφ n V ≫
        (A.relativeProjTwistingSheafGlueData n).transition i =
      CommMon.relativeProjTwistingSheafMapComponent φ hφ n U := by
  rw [CommMon.relativeProjTwistingSheafMapComponent, CommMon.relativeProjTwistingSheafMapComponent,
    ← Adjunction.homEquiv_naturality_right_symm, Category.assoc,
    CommMon.π_relativeProjTwistingSheafMapChart_transition]

/-- **The morphism of twisting sheaves induced by a morphism of graded algebras**: for `φ : B ⟶ A`
inducing `f : Proj_X(A) ⟶ Proj_X(B)`, the morphism `f^* 𝒪(n) ⟶ 𝒪(n)` glued from the morphisms of
twisting sheaves of the charts `Proj (⨁ n, Γ(Aₙ, U)) ⟶ Proj (⨁ n, Γ(Bₙ, U))`. -/
def _root_.CategoryTheory.CommMon.relativeProjTwistingSheafMap :
    (Scheme.Modules.pullback (CommMon.relativeProjMap φ hφ)).obj (B.relativeProjTwistingSheaf n) ⟶
      A.relativeProjTwistingSheaf n :=
  (A.relativeProjTwistingSheafGlueData n).lift
    (CommMon.relativeProjTwistingSheafMapComponent φ hφ n)
    (CommMon.relativeProjTwistingSheafMapComponent_transition φ hφ n)

/-- The glued morphism of twisting sheaves, followed by the projection of `𝒪(n)` on `Proj_X(A)` to a
chart, is the adjoint chart component. -/
@[simp]
theorem _root_.CategoryTheory.CommMon.relativeProjTwistingSheafMap_comp_π
    (U : X.AffineZariskiSite) :
    CommMon.relativeProjTwistingSheafMap φ hφ n ≫ (A.relativeProjTwistingSheafGlueData n).π U =
      CommMon.relativeProjTwistingSheafMapComponent φ hφ n U :=
  (A.relativeProjTwistingSheafGlueData n).lift_π _
    (CommMon.relativeProjTwistingSheafMapComponent_transition φ hφ n) U

/-- The morphism `𝒪(n) ⟶ f_* 𝒪(n)` adjoint to the glued morphism of twisting sheaves, followed by
the projection of `𝒪(n)` on `Proj_X(A)` to a chart, is the chart component. -/
@[simp]
theorem _root_.CategoryTheory.CommMon.homEquiv_relativeProjTwistingSheafMap_comp_π
    (U : X.AffineZariskiSite) :
    ((Scheme.Modules.pullbackPushforwardAdjunction (X := colimit A.relativeProjGluingData.functor)
      (Y := colimit B.relativeProjGluingData.functor) (CommMon.relativeProjMap φ hφ)).homEquiv _ _
        (CommMon.relativeProjTwistingSheafMap φ hφ n)) ≫
      (Scheme.Modules.pushforward (X := colimit A.relativeProjGluingData.functor)
        (Y := colimit B.relativeProjGluingData.functor) (CommMon.relativeProjMap φ hφ)).map
        ((A.relativeProjTwistingSheafGlueData n).π U) =
      (B.relativeProjTwistingSheafGlueData n).π U ≫
        CommMon.relativeProjTwistingSheafMapChart φ hφ n U := by
  -- `relativeProjMap` is typed on `relativeProj`, the glued modules on `colimit _`, so the
  -- naturality of the adjunction is applied as a term rather than by `rw`
  exact ((Scheme.Modules.pullbackPushforwardAdjunction _).homEquiv_naturality_right _ _).symm.trans
    ((congrArg ((Scheme.Modules.pullbackPushforwardAdjunction _).homEquiv _ _)
      (CommMon.relativeProjTwistingSheafMap_comp_π φ hφ n U)).trans
      (Equiv.apply_symm_apply _ _))

end

end TauCeti
