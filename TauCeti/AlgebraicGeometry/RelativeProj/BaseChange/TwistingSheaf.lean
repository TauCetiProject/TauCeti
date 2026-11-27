/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.RelativeProj.BaseChange.Basic
public import TauCeti.AlgebraicGeometry.RelativeProj.TwistingSheaf

/-!
# The twisting sheaves of the relative `Proj` of a pulled-back graded algebra

Let `g : X ⟶ Y` be a morphism of schemes, `A` a graded quasicoherent algebra on `Y`, and
`h : Proj_X(g^* A) ⟶ Proj_Y(A)` the projection `relativeProjPullbackHom A g` of the relative `Proj`
of `g^* A` onto that of `A`. This file constructs the comparison morphism of twisting sheaves

`h^* 𝒪_A(n) ⟶ 𝒪_{g^* A}(n)`

(`GradedQuasicoherentAlgebra.relativeProjPullbackTwistingSheafHom`), for every `n ∈ ℤ`.

Over affine opens `V ≤ g⁻¹ U`, the chart `Proj (⨁ n, Γ(g^* Aₙ, V))` maps to the chart
`Proj (⨁ n, Γ(Aₙ, U))` by `Proj.map` of the pullback of sections, and the twisting sheaves of the
charts are related by `AlgebraicGeometry.Proj.twistingSheafMap`. Composing with the projection of
the glued twisting sheaf `𝒪_A(n)` to the chart over `U` gives morphisms
`𝒪_A(n) ⟶ h_* (ι_V)_* 𝒪(n)` (`relativeProjTwistingSheafChartHom`). They are compatible with
restriction in `V` (`relativeProjTwistingSheafChartHom_comp_transition`) and in `U`
(`relativeProjTwistingSheafChartHom_eq_of_le`), hence do not depend on `U`
(`relativeProjTwistingSheafChartHom_eq`): two choices agree on the charts over common basic
opens, which cover the chart over `V`. Their adjoints form a compatible family over the affine
opens of `X` lying over some affine open of `Y`, which is a downward closed set of charts covering
the relative `Proj` of `g^* A`, so they glue by `TauCeti.ModulesGlueData.liftOfCover`.

## Main definitions

* `GradedQuasicoherentAlgebra.relativeProjPullbackTwistingSheafHom A g n`: the comparison
  `h^* 𝒪_A(n) ⟶ 𝒪_{g^* A}(n)`.

## Main results

* `GradedQuasicoherentAlgebra.relativeProjPullbackTwistingSheafHom_π`: over the chart of an
  affine open `V ≤ g⁻¹ U`, the comparison is adjoint to the map of twisting sheaves induced by
  pullback of sections from `U` to `V`.

## References

* [The Stacks Project, Lemma 27.16.10](https://stacks.math.columbia.edu/tag/01O3)

The chart comparison and its gluing are adapted from the
[relative Proj base-change formalization](https://github.com/roed-math/TauCeti-w2-fresh/tree/8bf602f6c2bed52e7e390df1ba2c2de30f8a6dfb)
by `roed-math`.
-/

public section

open CategoryTheory

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry Scheme.AffineZariskiSite

universe u

namespace GradedQuasicoherentAlgebra

variable {X Y : Scheme.{u}} (A : GradedQuasicoherentAlgebra Y) (g : X ⟶ Y) (n : ℤ)

/-- The comparison of twisting sheaves over affine opens `V ≤ g⁻¹ U`: the projection of `𝒪_A(n)`
to the chart over `U` followed by the map of twisting sheaves along
`Proj (⨁ n, Γ(g^* Aₙ, V)) ⟶ Proj (⨁ n, Γ(Aₙ, U))`, as a morphism `𝒪_A(n) ⟶ h_* (ι_V)_* 𝒪(n)`. -/
noncomputable def relativeProjTwistingSheafChartHom {V : X.AffineZariskiSite}
    {U : Y.AffineZariskiSite} (hV : V.toOpens ≤ g ⁻¹ᵁ U.toOpens) :
    A.obj.relativeProjTwistingSheaf n ⟶
      (Scheme.Modules.pushforward (relativeProjPullbackHom A g)).obj
        ((Scheme.Modules.pushforward (((pullback g).obj A).obj.relativeProjCover.f V)).obj
          (Proj.twistingSheaf (((pullback g).obj A).obj.gradedSectionsGrading V.toOpens) n)) :=
  (A.obj.relativeProjTwistingSheafGlueData n).π U ≫
    (Scheme.Modules.pushforward (A.obj.relativeProjCover.f U)).map
      (Proj.twistingSheafMap (A.pullbackGradedSectionsGradedHom g hV)
        (A.irrelevant_le_map_pullbackGradedSectionsGradedHom g hV U.property V.property) n) ≫
    (Scheme.Modules.pushforwardComp (Proj.map (A.pullbackGradedSectionsGradedHom g hV)
        (A.irrelevant_le_map_pullbackGradedSectionsGradedHom g hV U.property V.property))
        (A.obj.relativeProjCover.f U)).hom.app
        (Proj.twistingSheaf (((pullback g).obj A).obj.gradedSectionsGrading V.toOpens) n) ≫
    (Scheme.Modules.pushforwardCongr
      (relativeProjCover_f_relativeProjPullbackHom A g V U hV).symm).hom.app
        (Proj.twistingSheaf (((pullback g).obj A).obj.gradedSectionsGrading V.toOpens) n) ≫
    (Scheme.Modules.pushforwardComp (((pullback g).obj A).obj.relativeProjCover.f V)
      (relativeProjPullbackHom A g)).inv.app
        (Proj.twistingSheaf (((pullback g).obj A).obj.gradedSectionsGrading V.toOpens) n)

/-- On sections over `W`, the chart comparison is the map of twisting sheaves applied to the
projection of the section to the chart over `U`, restricted along
`ι_V⁻¹ h⁻¹ W = (Proj.map)⁻¹ ι_U⁻¹ W`. -/
theorem relativeProjTwistingSheafChartHom_app_apply {V : X.AffineZariskiSite}
    {U : Y.AffineZariskiSite} (hV : V.toOpens ≤ g ⁻¹ᵁ U.toOpens) (W : A.obj.relativeProj.Opens)
    (s : Γ(A.obj.relativeProjTwistingSheaf n, W)) :
    (A.relativeProjTwistingSheafChartHom g n hV).app W s =
      (Proj.twistingSheaf (((pullback g).obj A).obj.gradedSectionsGrading V.toOpens) n).presheaf.map
        (eqToHom (show ((pullback g).obj A).obj.relativeProjCover.f V ⁻¹ᵁ
            relativeProjPullbackHom A g ⁻¹ᵁ W =
          Proj.map (A.pullbackGradedSectionsGradedHom g hV)
            (A.irrelevant_le_map_pullbackGradedSectionsGradedHom g hV U.property V.property) ⁻¹ᵁ
            A.obj.relativeProjCover.f U ⁻¹ᵁ W from
          congrArg (fun f ↦ f ⁻¹ᵁ W) (relativeProjCover_f_relativeProjPullbackHom A g V U hV))).op
        ((Proj.twistingSheafMap (A.pullbackGradedSectionsGradedHom g hV)
          (A.irrelevant_le_map_pullbackGradedSectionsGradedHom g hV U.property V.property) n).app
            (A.obj.relativeProjCover.f U ⁻¹ᵁ W)
          (((A.obj.relativeProjTwistingSheafGlueData n).π U).app W s)) :=
  (rfl)

/-- The chart comparison over `V ≤ g⁻¹ U'` does not change when `U'` is replaced by an affine open
`U` of `Y` of which it is a basic open. -/
private theorem relativeProjTwistingSheafChartHom_eq_of_le {V : X.AffineZariskiSite}
    {U U' : Y.AffineZariskiSite} (i : U' ⟶ U)
    (hV' : V.toOpens ≤ g ⁻¹ᵁ U'.toOpens) :
    A.relativeProjTwistingSheafChartHom g n
        (hV'.trans (g.preimage_mono (toOpens_mono (leOfHom i)))) =
      A.relativeProjTwistingSheafChartHom g n hV' := by
  let hV := hV'.trans (g.preimage_mono (toOpens_mono (leOfHom i)))
  refine Scheme.Modules.hom_ext _ _ fun W ↦ ?_
  refine ConcreteCategory.hom_ext _ _ fun s ↦ ?_
  refine (A.relativeProjTwistingSheafChartHom_app_apply g n hV W s).trans
    (Eq.trans ?_ (A.relativeProjTwistingSheafChartHom_app_apply g n hV' W s).symm)
  have key := ((A.obj.relativeProjTwistingSheafGlueData n).transition_app_apply i W
    (((A.obj.relativeProjTwistingSheafGlueData n).π U).app W s)).symm.trans
      ((A.obj.relativeProjTwistingSheafGlueData n).transition_app_π_app i W s)
  have h1 := (Proj.twistingSheafMap_app_apply_res_of_eq_comp
    (A.obj.restrictGradedSectionsGradedHom ((toOpensFunctor Y).map i))
    (A.obj.irrelevant_le_map_restrictGradedSections_toOpensFunctor i)
    (A.pullbackGradedSectionsGradedHom g hV')
    (A.irrelevant_le_map_pullbackGradedSectionsGradedHom g hV' U'.property V.property) _ _
    (pullbackGradedSectionsGradedHom_comp_restrictGradedSectionsGradedHom g A
      ((toOpensFunctor Y).map i) hV').symm n (V := A.obj.relativeProjCover.f U ⁻¹ᵁ W)
    (V' := A.obj.relativeProjCover.f U' ⁻¹ᵁ W)
    (W := ((pullback g).obj A).obj.relativeProjCover.f V ⁻¹ᵁ relativeProjPullbackHom A g ⁻¹ᵁ W)
    (congrArg (fun f ↦ f ⁻¹ᵁ W) (relativeProjCover_f_relativeProjPullbackHom A g V U hV))
    (congrArg (fun f ↦ f ⁻¹ᵁ W) (relativeProjCover_f_relativeProjPullbackHom A g V U' hV'))
    (congrArg (fun f ↦ f ⁻¹ᵁ W)
      (A.obj.relativeProjGluingData_functor_map_comp_relativeProjCover_f i).symm)
    (((A.obj.relativeProjTwistingSheafGlueData n).π U).app W s))
  refine h1.trans ?_
  exact congrArg (fun t ↦ (Proj.twistingSheaf
    (((pullback g).obj A).obj.gradedSectionsGrading V.toOpens) n).presheaf.map (eqToHom _).op
      ((Proj.twistingSheafMap (A.pullbackGradedSectionsGradedHom g hV')
        (A.irrelevant_le_map_pullbackGradedSectionsGradedHom g hV' U'.property V.property) n).app
          (A.obj.relativeProjCover.f U' ⁻¹ᵁ W) t)) key

/-- The chart comparisons are compatible with the transition maps of the twisting sheaf of the
relative `Proj` of `g^* A`. -/
private theorem relativeProjTwistingSheafChartHom_comp_transition {V V' : X.AffineZariskiSite}
    {U : Y.AffineZariskiSite} (a : V' ⟶ V)
    (hV : V.toOpens ≤ g ⁻¹ᵁ U.toOpens) :
    A.relativeProjTwistingSheafChartHom g n hV ≫
        (Scheme.Modules.pushforward (relativeProjPullbackHom A g)).map
          ((((pullback g).obj A).obj.relativeProjTwistingSheafGlueData n).transition a) =
      A.relativeProjTwistingSheafChartHom g n ((toOpens_mono (leOfHom a)).trans hV) := by
  let hV' := (toOpens_mono (leOfHom a)).trans hV
  refine Scheme.Modules.hom_ext _ _ fun W ↦ ?_
  refine ConcreteCategory.hom_ext _ _ fun s ↦ ?_
  have h1 := Proj.twistingSheafMap_app_apply_res_of_eq_comp
    (A.pullbackGradedSectionsGradedHom g hV)
    (A.irrelevant_le_map_pullbackGradedSectionsGradedHom g hV U.property V.property)
    (((pullback g).obj A).obj.restrictGradedSectionsGradedHom ((toOpensFunctor X).map a))
    (((pullback g).obj A).obj.irrelevant_le_map_restrictGradedSections_toOpensFunctor a)
    (A.pullbackGradedSectionsGradedHom g hV')
    (A.irrelevant_le_map_pullbackGradedSectionsGradedHom g hV' U.property V'.property)
    (restrictGradedSectionsGradedHom_comp_pullbackGradedSectionsGradedHom g A hV
      ((toOpensFunctor X).map a)).symm n
    (V := A.obj.relativeProjCover.f U ⁻¹ᵁ W)
    (V' := ((pullback g).obj A).obj.relativeProjCover.f V ⁻¹ᵁ relativeProjPullbackHom A g ⁻¹ᵁ W)
    (W := ((pullback g).obj A).obj.relativeProjCover.f V' ⁻¹ᵁ relativeProjPullbackHom A g ⁻¹ᵁ W)
    (congrArg (fun f ↦ f ⁻¹ᵁ W) (relativeProjCover_f_relativeProjPullbackHom A g V' U hV'))
    (congrArg (fun f ↦ f ⁻¹ᵁ relativeProjPullbackHom A g ⁻¹ᵁ W)
      (((pullback g).obj A).obj.relativeProjGluingData_functor_map_comp_relativeProjCover_f a).symm)
    (congrArg (fun f ↦ f ⁻¹ᵁ W) (relativeProjCover_f_relativeProjPullbackHom A g V U hV))
    (((A.obj.relativeProjTwistingSheafGlueData n).π U).app W s)
  -- as in `relativeProjTwistingSheafChartHom_eq` below, the section is stated over `h⁻¹ W`
  let t : Γ((Scheme.Modules.pushforward (((pullback g).obj A).obj.relativeProjCover.f V)).obj
      (Proj.twistingSheaf (((pullback g).obj A).obj.gradedSectionsGrading V.toOpens) n),
      relativeProjPullbackHom A g ⁻¹ᵁ W) := (A.relativeProjTwistingSheafChartHom g n hV).app W s
  have h2 := (((pullback g).obj A).obj.relativeProjTwistingSheafGlueData n).transition_app_apply a
    (relativeProjPullbackHom A g ⁻¹ᵁ W) t
  have h3 := A.relativeProjTwistingSheafChartHom_app_apply g n hV' W s
  have h4 := A.relativeProjTwistingSheafChartHom_app_apply g n hV W s
  refine h2.trans (Eq.trans ?_ (h3.trans h1).symm)
  exact congrArg (fun t ↦
    ((((pullback g).obj A).obj.relativeProjTwistingSheafGlueData n).obj V').presheaf.map
    (eqToHom _).op (((((pullback g).obj A).obj.relativeProjTwistingSheafGlueData n).map a).app
      (((pullback g).obj A).obj.relativeProjCover.f V ⁻¹ᵁ relativeProjPullbackHom A g ⁻¹ᵁ W) t)) h4

/-- **The chart comparison does not depend on the affine open of `Y`** below which `V` lies. -/
private theorem relativeProjTwistingSheafChartHom_eq {V : X.AffineZariskiSite}
    {U₁ U₂ : Y.AffineZariskiSite} (h₁ : V.toOpens ≤ g ⁻¹ᵁ U₁.toOpens)
    (h₂ : V.toOpens ≤ g ⁻¹ᵁ U₂.toOpens) :
    A.relativeProjTwistingSheafChartHom g n h₁ = A.relativeProjTwistingSheafChartHom g n h₂ := by
  refine Scheme.Modules.hom_ext _ _ fun W ↦ ConcreteCategory.hom_ext _ _ fun s ↦ ?_
  let x : Γ((Scheme.Modules.pushforward (((pullback g).obj A).obj.relativeProjCover.f V)).obj
      (Proj.twistingSheaf (((pullback g).obj A).obj.gradedSectionsGrading V.toOpens) n),
      relativeProjPullbackHom A g ⁻¹ᵁ W) := (A.relativeProjTwistingSheafChartHom g n h₁).app W s
  let y : Γ((Scheme.Modules.pushforward (((pullback g).obj A).obj.relativeProjCover.f V)).obj
      (Proj.twistingSheaf (((pullback g).obj A).obj.gradedSectionsGrading V.toOpens) n),
      relativeProjPullbackHom A g ⁻¹ᵁ W) := (A.relativeProjTwistingSheafChartHom g n h₂).app W s
  -- sections of the pushforward along `h` over `W` are sections over `h⁻¹ W`; stating them so
  -- keeps the unifier from unfolding the pushforwards below
  change x = y
  refine ModulesGlueData.eq_of_transition_app_eq_of_le_cover
    (((pullback g).obj A).obj.relativeProjTwistingSheafGlueData n)
    (fun i W hW ↦
      (((pullback g).obj A).obj.bijective_relativeProjTwistingSheafGlueData_map_app n i W hW).1)
    {k | ∃ U : Y.AffineZariskiSite, U ≤ U₁ ∧ U ≤ U₂ ∧ k.toOpens ≤ g ⁻¹ᵁ U.toOpens}
    (fun f ⟨U, hU₁, hU₂, hk⟩ ↦ ⟨U, hU₁, hU₂, (toOpens_mono (leOfHom f)).trans hk⟩) ?_
    fun k ⟨U, hU₁, hU₂, hk⟩ a ↦ ?_
  · rintro _ ⟨z, rfl⟩
    have hz : ((pullback g).obj A).obj.relativeProjCover.f V z ∈
        ((pullback g).obj A).obj.relativeProjToBase ⁻¹ᵁ V.toOpens := by
      rw [CommMon.relativeProjToBase_preimage _ V]
      exact ⟨z, rfl⟩
    obtain ⟨l, hl, -, hl₁, hl₂⟩ :=
      g.exists_affinePair_le (i := ⟨(V, U₁), h₁⟩) (j := ⟨(V, U₂), h₂⟩) le_rfl le_rfl hz
    refine ⟨l.val.1, ⟨l.val.2, hl₁.2, hl₂.2, l.property⟩, ?_⟩
    -- the charts of the glued twisting sheaf are by definition those of the relative `Proj`
    change _ ∈ (((pullback g).obj A).obj.relativeProjCover.f l.val.1).opensRange
    rw [← CommMon.relativeProjToBase_preimage _ l.val.1]
    exact hl
  · have e₁ := ConcreteCategory.congr_hom (congrArg (Scheme.Modules.Hom.app · W)
      (A.relativeProjTwistingSheafChartHom_comp_transition g n a h₁)) s
    have e₂ := ConcreteCategory.congr_hom (congrArg (Scheme.Modules.Hom.app · W)
      (A.relativeProjTwistingSheafChartHom_comp_transition g n a h₂)) s
    have e₃ := (A.relativeProjTwistingSheafChartHom_eq_of_le g n (homOfLE hU₁) hk).trans
      (A.relativeProjTwistingSheafChartHom_eq_of_le g n (homOfLE hU₂) hk).symm
    exact e₁.trans ((congrArg (fun φ ↦ (Scheme.Modules.Hom.app φ W) s) e₃).trans e₂.symm)

/-- The morphism `h^* 𝒪(n) ⟶ (ι_V)_* 𝒪(n)` adjoint to `relativeProjTwistingSheafChartHom`, for
an affine open `V` of `X` lying over some affine open of `Y`. -/
private noncomputable def pullbackRelativeProjTwistingSheafChartHom {V : X.AffineZariskiSite}
    (hV : ∃ U : Y.AffineZariskiSite, V.toOpens ≤ g ⁻¹ᵁ U.toOpens) :
    (Scheme.Modules.pullback (relativeProjPullbackHom A g)).obj
        (A.obj.relativeProjTwistingSheaf n) ⟶
      (Scheme.Modules.pushforward (((pullback g).obj A).obj.relativeProjCover.f V)).obj
        (Proj.twistingSheaf (((pullback g).obj A).obj.gradedSectionsGrading V.toOpens) n) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction _).homEquiv _ _).symm
    (A.relativeProjTwistingSheafChartHom g n hV.choose_spec)

/-- The morphism `pullbackRelativeProjTwistingSheafChartHom` is adjoint to the chart comparison
for any affine open `U` of `Y` with `V ≤ g⁻¹ U`. -/
private theorem pullbackRelativeProjTwistingSheafChartHom_eq {V : X.AffineZariskiSite}
    (hV : ∃ U : Y.AffineZariskiSite, V.toOpens ≤ g ⁻¹ᵁ U.toOpens) {U : Y.AffineZariskiSite}
    (hU : V.toOpens ≤ g ⁻¹ᵁ U.toOpens) :
    A.pullbackRelativeProjTwistingSheafChartHom g n hV =
      ((Scheme.Modules.pullbackPushforwardAdjunction _).homEquiv _ _).symm
        (A.relativeProjTwistingSheafChartHom g n hU) := by
  rw [pullbackRelativeProjTwistingSheafChartHom,
    A.relativeProjTwistingSheafChartHom_eq g n hV.choose_spec hU]

/-- The morphisms `pullbackRelativeProjTwistingSheafChartHom` are compatible with the transition
maps of the twisting sheaf of the relative `Proj` of `g^* A`. -/
private theorem pullbackRelativeProjTwistingSheafChartHom_comp_transition
    {V V' : X.AffineZariskiSite}
    (f : V' ⟶ V) (hV : ∃ U : Y.AffineZariskiSite, V.toOpens ≤ g ⁻¹ᵁ U.toOpens)
    (hV' : ∃ U : Y.AffineZariskiSite, V'.toOpens ≤ g ⁻¹ᵁ U.toOpens) :
    A.pullbackRelativeProjTwistingSheafChartHom g n hV ≫
        (((pullback g).obj A).obj.relativeProjTwistingSheafGlueData n).transition f =
      A.pullbackRelativeProjTwistingSheafChartHom g n hV' :=
  (Adjunction.homEquiv_naturality_right_symm _ _ _).symm.trans (congrArg _
    ((A.relativeProjTwistingSheafChartHom_comp_transition g n f hV.choose_spec).trans
        (A.relativeProjTwistingSheafChartHom_eq g n _ _)))

/-- **The comparison of twisting sheaves along the base change of a relative `Proj`**: the
morphism `h^* 𝒪_A(n) ⟶ 𝒪_{g^* A}(n)` for the projection `h` of the relative `Proj` of `g^* A`
onto that of `A`, glued from the chart comparisons over the affine opens `V ≤ g⁻¹ U`. -/
noncomputable def relativeProjPullbackTwistingSheafHom :
    (Scheme.Modules.pullback (relativeProjPullbackHom A g)).obj
        (A.obj.relativeProjTwistingSheaf n) ⟶
      ((pullback g).obj A).obj.relativeProjTwistingSheaf n :=
  (((pullback g).obj A).obj.relativeProjTwistingSheafGlueData n).liftOfCover
    (((pullback g).obj A).obj.bijective_relativeProjTwistingSheafGlueData_map_app n)
    {V | ∃ U : Y.AffineZariskiSite, V.toOpens ≤ g ⁻¹ᵁ U.toOpens}
    (fun f ⟨U, hU⟩ ↦ ⟨U, (toOpens_mono (leOfHom f)).trans hU⟩)
    (exists_mem_opensRange_relativeProjCover_f A g)
    (fun _ ↦ A.pullbackRelativeProjTwistingSheafChartHom g n)
    fun f hV ↦ A.pullbackRelativeProjTwistingSheafChartHom_comp_transition g n f hV _

/-- Over the chart of an affine open `V ≤ g⁻¹ U`, the comparison of twisting sheaves is adjoint to
the map of twisting sheaves induced by pullback of sections from `U` to `V`. -/
@[reassoc]
theorem relativeProjPullbackTwistingSheafHom_π {V : X.AffineZariskiSite}
    {U : Y.AffineZariskiSite} (hV : V.toOpens ≤ g ⁻¹ᵁ U.toOpens) :
    relativeProjPullbackTwistingSheafHom A g n ≫
        (((pullback g).obj A).obj.relativeProjTwistingSheafGlueData n).π V =
      ((Scheme.Modules.pullbackPushforwardAdjunction _).homEquiv _ _).symm
        (A.relativeProjTwistingSheafChartHom g n hV) :=
  ((((pullback g).obj A).obj.relativeProjTwistingSheafGlueData n).liftOfCover_π
    (((pullback g).obj A).obj.bijective_relativeProjTwistingSheafGlueData_map_app n)
    {V | ∃ U : Y.AffineZariskiSite, V.toOpens ≤ g ⁻¹ᵁ U.toOpens}
    (fun f ⟨U, hU⟩ ↦ ⟨U, (toOpens_mono (leOfHom f)).trans hU⟩)
    (exists_mem_opensRange_relativeProjCover_f A g)
    (fun _ ↦ A.pullbackRelativeProjTwistingSheafChartHom g n)
    (fun f hV ↦ A.pullbackRelativeProjTwistingSheafChartHom_comp_transition g n f hV _)
    ⟨U, hV⟩).trans (A.pullbackRelativeProjTwistingSheafChartHom_eq g n _ hV)

end GradedQuasicoherentAlgebra

end TauCeti.AlgebraicGeometry
