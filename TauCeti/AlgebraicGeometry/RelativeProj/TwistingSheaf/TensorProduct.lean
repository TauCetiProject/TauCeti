/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.TensorProduct
public import TauCeti.AlgebraicGeometry.RelativeProj.TwistingSheaf

/-!
# Tensor products of the twisting sheaves of a relative `Proj`

Let `A` be a graded algebra on a scheme `X` with quasi-coherent homogeneous components. The
twisting sheaves `𝒪(n)` of the relative `Proj` of `A` are glued from the twisting sheaves of the
charts `Proj (⨁ n, Γ(Aₙ, U))` over the affine opens `U` of `X`
(`CategoryTheory.CommMon.relativeProjTwistingSheaf`), so a section of `𝒪(n)` over an open `W` is a
family of sections of the twisting sheaves of the charts over the preimages of `W`, compatible
under the transition maps. Multiplying these families chartwise gives a multiplication
`Γ(W, 𝒪(m)) × Γ(W, 𝒪(n)) → Γ(W, 𝒪(m + n))`, since the transition maps of the charts are
multiplicative (`AlgebraicGeometry.Proj.twistingSheafMap_app_mul`), and hence a morphism
`𝒪(m) ⊗ 𝒪(n) ⟶ 𝒪(m + n)` of sheaves of modules on the relative `Proj`.

When the standard opens `D₊(f)` of the elements `f` of degree one cover every chart, for instance
when `A` is generated in degree one, this morphism is an isomorphism. On an open `W` of the image
of the chart over `U` whose preimage lies in such a `D₊(f)`, the projection to the chart identifies
the sections of `𝒪(n)` over `W` with those of the chart's `𝒪(n)`, which are free of rank one on
the basis section `fⁿ`; as these basis sections multiply to each other, multiplication of sections
over `W` is bijective on tensor products. Hence the classes of the invertible sheaves `𝒪(n)` in
the group of line-bundle classes satisfy `[𝒪(n)] = [𝒪(1)] ^ n` for every `n ∈ ℤ`, that is
`𝒪(n) ≅ 𝒪(1)^{⊗ n}`. The argument is the one for the projective spectrum of a graded ring in
`TauCeti/AlgebraicGeometry/ProjectiveSpectrum/TwistingSheaf/TensorProduct.lean`, applied chartwise.

## Main definitions

* `CategoryTheory.CommMon.relativeProjTwistingSheafMul A W m n`: multiplication of sections
  `Γ(W, 𝒪(m)) × Γ(W, 𝒪(n)) → Γ(W, 𝒪(m + n))` of the twisting sheaves of the relative `Proj`,
  characterized by `CategoryTheory.CommMon.π_app_relativeProjTwistingSheafMul`.
* `CategoryTheory.CommMon.relativeProjTwistingSheafTensorPresheafHom A m n`: multiplication, as a
  morphism from the sectionwise tensor product of `𝒪(m)` and `𝒪(n)` to `𝒪(m + n)`.
* `CategoryTheory.CommMon.relativeProjTwistingSheafTensorProductIso`: the isomorphism
  `𝒪(m) ⊗ 𝒪(n) ≅ 𝒪(m + n)` when the degree-one standard opens cover every chart, with
  `CategoryTheory.CommMon.relativeProjTwistingSheafTensorProductIso_hom_tmul` describing it on
  pure tensors.

## Main results

* `CategoryTheory.CommMon.lineBundleClass_relativeProjTwistingSheaf_eq_zpow`: when `A` is generated
  in degree one, `[𝒪(n)] = [𝒪(1)] ^ n` in the group of line-bundle classes of the relative `Proj`;
  `CategoryTheory.CommMon.lineBundleClass_relativeProjTwistingSheaf_eq_zpow_of_iSup_eq_top` under
  the weaker hypothesis that the degree-one standard opens cover every chart.

## References

* [The Stacks Project, Lemma 27.16.11](https://stacks.math.columbia.edu/tag/01O4)
* R. Hartshorne, *Algebraic Geometry*, Proposition II.5.12.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite TensorProduct DirectSum

namespace TauCeti

open _root_.AlgebraicGeometry Proj.twistingSheaf

universe u

variable {X : Scheme.{u}} (A : CommMon (GradedObject ℕ X.Modules)) [∀ n, (A.X n).IsQuasicoherent]

section Mul

variable {W : A.relativeProj.Opens}

/-- The preimage of an open `W` of the relative `Proj` in the chart over `U`. -/
private abbrev chartOpen (W : A.relativeProj.Opens) (U : X.AffineZariskiSite) :
    (Proj (A.gradedSectionsGrading U.toOpens)).Opens :=
  colimit.ι A.relativeProjGluingData.functor U ⁻¹ᵁ W

/-- Multiplication of sections of the twisting sheaves of the chart over `U`, over the preimage
of `W`. -/
private def chartMul (W : A.relativeProj.Opens) (U : X.AffineZariskiSite) (m n : ℤ)
    (s : Γ(Proj.twistingSheaf (A.gradedSectionsGrading U.toOpens) m, chartOpen A W U))
    (t : Γ(Proj.twistingSheaf (A.gradedSectionsGrading U.toOpens) n, chartOpen A W U)) :
    Γ(Proj.twistingSheaf (A.gradedSectionsGrading U.toOpens) (m + n), chartOpen A W U) :=
  mul (A.gradedSectionsGrading U.toOpens) (chartOpen A W U) m n s t

/-- The image of a section of `𝒪(n)` over `W` in the chart over `U`: a section of the twisting
sheaf `𝒪(n)` of `Proj (⨁ n, Γ(Aₙ, U))` over the preimage of `W`. -/
private def chartSection (n : ℤ) (U : X.AffineZariskiSite)
    (s : Γ(A.relativeProjTwistingSheaf n, W)) :
    Γ(Proj.twistingSheaf (A.gradedSectionsGrading U.toOpens) n, chartOpen A W U) :=
  ((A.relativeProjTwistingSheafGlueData n).π U).app W s

/-- The transition maps of the twisting sheaves of the charts are multiplicative. -/
private theorem transition_mul {U V : X.AffineZariskiSite} (i : U ⟶ V) (m n : ℤ)
    (s : Γ(Proj.twistingSheaf (A.gradedSectionsGrading V.toOpens) m, chartOpen A W V))
    (t : Γ(Proj.twistingSheaf (A.gradedSectionsGrading V.toOpens) n, chartOpen A W V)) :
    (((A.relativeProjTwistingSheafGlueData (m + n)).transition i).app W
        (chartMul A W V m n s t) :
        Γ(Proj.twistingSheaf (A.gradedSectionsGrading U.toOpens) (m + n), chartOpen A W U)) =
      chartMul A W U m n (((A.relativeProjTwistingSheafGlueData m).transition i).app W s)
        (((A.relativeProjTwistingSheafGlueData n).transition i).app W t) := by
  have h₁ := (A.relativeProjTwistingSheafGlueData (m + n)).transition_app_apply i W
  have h₂ := (A.relativeProjTwistingSheafGlueData m).transition_app_apply i W
  have h₃ := (A.relativeProjTwistingSheafGlueData n).transition_app_apply i W
  refine (h₁ (chartMul A W V m n s t)).trans (Eq.trans ?_
    (congrArg₂ (fun a b ↦ chartMul A W U m n a b) (h₂ s).symm (h₃ t).symm))
  exact Proj.res_twistingSheafMap_app_mul
    (A.restrictGradedSectionsGradedHom ((Scheme.AffineZariskiSite.toOpensFunctor X).map i))
    (A.irrelevant_le_map_restrictGradedSectionsGradedHom_toOpensFunctor i) _ _ s t

/-- The products, in the charts, of the images of two sections of twisting sheaves of the relative
`Proj` are compatible under the transition maps, hence the images of a single section. -/
private theorem exists_chartSection_eq_mul (m n : ℤ) (s : Γ(A.relativeProjTwistingSheaf m, W))
    (t : Γ(A.relativeProjTwistingSheaf n, W)) :
    ∃ u : Γ(A.relativeProjTwistingSheaf (m + n), W), ∀ U,
      chartSection A (m + n) U u = chartMul A W U m n (chartSection A m U s)
        (chartSection A n U t) := by
  have key : ∀ {U V : X.AffineZariskiSite} (i : U ⟶ V),
      ((A.relativeProjTwistingSheafGlueData (m + n)).transition i).app W
        (chartMul A W V m n (chartSection A m V s) (chartSection A n V t)) =
      chartMul A W U m n (chartSection A m U s) (chartSection A n U t) := fun i ↦
    (transition_mul A i m n _ _).trans (congrArg₂ (fun a b ↦ chartMul A W _ m n a b)
      ((A.relativeProjTwistingSheafGlueData m).transition_app_π_app i W s)
      ((A.relativeProjTwistingSheafGlueData n).transition_app_π_app i W t))
  exact (A.relativeProjTwistingSheafGlueData (m + n)).exists_π_app (U := W) _ key

/-- The restriction of a function on an open `W` of the relative `Proj` to the chart over `U`. -/
private def chartRes (U : X.AffineZariskiSite) (r : Γ(A.relativeProj, W)) :
    Γ(Proj (A.gradedSectionsGrading U.toOpens), chartOpen A W U) :=
  (colimit.ι A.relativeProjGluingData.functor U).app W r

/-- The images in the charts of a sum of sections are the sums of their images. -/
private theorem chartSection_add (k : ℤ) (U : X.AffineZariskiSite)
    (s s' : Γ(A.relativeProjTwistingSheaf k, W)) :
    chartSection A k U (s + s') = chartSection A k U s + chartSection A k U s' :=
  map_add _ s s'

/-- The image in the chart over `U` of the product of a section by a function `r` is the product
by the restriction of `r` to the chart. -/
private theorem chartSection_smul (k : ℤ) (U : X.AffineZariskiSite) (r : Γ(A.relativeProj, W))
    (s : Γ(A.relativeProjTwistingSheaf k, W)) :
    chartSection A k U (r • s) = chartRes A U r • chartSection A k U s :=
  Scheme.Modules.Hom.app_smul _ r s

/-- The image in the chart over `U` of the restriction of a section is the restriction of its
image. -/
private theorem chartSection_res (k : ℤ) (U : X.AffineZariskiSite) {W' : A.relativeProj.Opens}
    (i : W' ⟶ W) (s : Γ(A.relativeProjTwistingSheaf k, W)) :
    chartSection A k U ((A.relativeProjTwistingSheaf k).presheaf.map i.op s) =
      (Proj.twistingSheaf (A.gradedSectionsGrading U.toOpens) k).presheaf.map
        ((TopologicalSpace.Opens.map (colimit.ι A.relativeProjGluingData.functor U).base).map
          i).op (chartSection A k U s) :=
  NatTrans.naturality_apply ((A.relativeProjTwistingSheafGlueData k).π U).mapPresheaf i.op s

/-- The product of two sections of twisting sheaves of the relative `Proj`, before bundling it as
a bilinear map. -/
private def mulAux (m n : ℤ) (s : Γ(A.relativeProjTwistingSheaf m, W))
    (t : Γ(A.relativeProjTwistingSheaf n, W)) : Γ(A.relativeProjTwistingSheaf (m + n), W) :=
  (exists_chartSection_eq_mul A m n s t).choose

/-- The image of the product in every chart is the product of the images. -/
private theorem chartSection_mulAux (m n : ℤ) (U : X.AffineZariskiSite)
    (s : Γ(A.relativeProjTwistingSheaf m, W)) (t : Γ(A.relativeProjTwistingSheaf n, W)) :
    chartSection A (m + n) U (mulAux A m n s t) =
      chartMul A W U m n (chartSection A m U s) (chartSection A n U t) :=
  (exists_chartSection_eq_mul A m n s t).choose_spec U

/-- Sections of the twisting sheaves of the relative `Proj` agree if their images in all charts
agree. -/
private theorem ext_chartSection {k : ℤ} {s s' : Γ(A.relativeProjTwistingSheaf k, W)}
    (h : ∀ U, chartSection A k U s = chartSection A k U s') : s = s' :=
  (A.relativeProjTwistingSheafGlueData k).π_ext h

end Mul

/-- **Multiplication of sections of the twisting sheaves of a relative `Proj`**: the bilinear map
`Γ(W, 𝒪(m)) × Γ(W, 𝒪(n)) → Γ(W, 𝒪(m + n))` multiplying, in the chart `Proj (⨁ n, Γ(Aₙ, U))`
over every affine open `U` of `X`, the images of the sections. -/
def _root_.CategoryTheory.CommMon.relativeProjTwistingSheafMul (W : A.relativeProj.Opens)
    (m n : ℤ) :
    Γ(A.relativeProjTwistingSheaf m, W) →ₗ[Γ(A.relativeProj, W)]
      Γ(A.relativeProjTwistingSheaf n, W) →ₗ[Γ(A.relativeProj, W)]
        Γ(A.relativeProjTwistingSheaf (m + n), W) :=
  LinearMap.mk₂ _ (mulAux A m n)
    (fun s s' t ↦ ext_chartSection A fun U ↦ by
      simp only [chartSection_add, chartSection_mulAux, chartMul, mul_add_left])
    (fun r s t ↦ ext_chartSection A fun U ↦ by
      simp only [chartSection_smul, chartSection_mulAux, chartMul, mul_smul_left])
    (fun s t t' ↦ ext_chartSection A fun U ↦ by
      simp only [chartSection_add, chartSection_mulAux, chartMul, mul_add_right])
    (fun r s t ↦ ext_chartSection A fun U ↦ by
      simp only [chartSection_smul, chartSection_mulAux, chartMul, mul_smul_right])

section MulCharts

variable {A} {W : A.relativeProj.Opens} {m n : ℤ}

private theorem chartSection_relativeProjTwistingSheafMul (U : X.AffineZariskiSite)
    (s : Γ(A.relativeProjTwistingSheaf m, W)) (t : Γ(A.relativeProjTwistingSheaf n, W)) :
    chartSection A (m + n) U (A.relativeProjTwistingSheafMul W m n s t) =
      chartMul A W U m n (chartSection A m U s) (chartSection A n U t) :=
  chartSection_mulAux A m n U s t

/-- **The product of sections is computed in the charts**: in the chart `Proj (⨁ n, Γ(Aₙ, U))`
over an affine open `U` of `X`, the image of the product of two sections of twisting sheaves of
the relative `Proj` is the product of their images. -/
@[simp]
theorem _root_.CategoryTheory.CommMon.π_app_relativeProjTwistingSheafMul (U : X.AffineZariskiSite)
    (s : Γ(A.relativeProjTwistingSheaf m, W)) (t : Γ(A.relativeProjTwistingSheaf n, W)) :
    (((A.relativeProjTwistingSheafGlueData (m + n)).π U).app W
        (A.relativeProjTwistingSheafMul W m n s t) :
        Γ(Proj.twistingSheaf (A.gradedSectionsGrading U.toOpens) (m + n),
          colimit.ι A.relativeProjGluingData.functor U ⁻¹ᵁ W)) =
      mul (A.gradedSectionsGrading U.toOpens) (colimit.ι A.relativeProjGluingData.functor U ⁻¹ᵁ W)
        m n (((A.relativeProjTwistingSheafGlueData m).π U).app W s)
        (((A.relativeProjTwistingSheafGlueData n).π U).app W t) :=
  chartSection_relativeProjTwistingSheafMul U s t

/-- The multiplication of sections of twisting sheaves of a relative `Proj` commutes with
restriction. -/
@[simp]
theorem _root_.CategoryTheory.CommMon.res_relativeProjTwistingSheafMul {W' : A.relativeProj.Opens}
    (i : W' ⟶ W) (s : Γ(A.relativeProjTwistingSheaf m, W))
    (t : Γ(A.relativeProjTwistingSheaf n, W)) :
    (A.relativeProjTwistingSheaf (m + n)).presheaf.map i.op
        (A.relativeProjTwistingSheafMul W m n s t) =
      A.relativeProjTwistingSheafMul W' m n ((A.relativeProjTwistingSheaf m).presheaf.map i.op s)
        ((A.relativeProjTwistingSheaf n).presheaf.map i.op t) :=
  ext_chartSection A fun U ↦ (chartSection_res A (m + n) U i _).trans <|
    (congrArg _ (chartSection_relativeProjTwistingSheafMul U s t)).trans <| (res_mul _ _ _).trans <|
      (congrArg₂ (fun a b ↦ chartMul A W' U m n a b) (chartSection_res A m U i s).symm
        (chartSection_res A n U i t).symm).trans
      (chartSection_relativeProjTwistingSheafMul U _ _).symm

end MulCharts

variable (m n : ℤ)

/-- Multiplication of sections, as a morphism of presheaves of modules from the sectionwise tensor
product of the twisting sheaves `𝒪(m)` and `𝒪(n)` of a relative `Proj` to `𝒪(m + n)`. -/
def _root_.CategoryTheory.CommMon.relativeProjTwistingSheafTensorPresheafHom :
    PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := A.relativeProj.sheaf.obj)
      (A.relativeProjTwistingSheaf m).val (A.relativeProjTwistingSheaf n).val ⟶
        (A.relativeProjTwistingSheaf (m + n)).val where
  app W := ModuleCat.MonoidalCategory.tensorLift
    (fun s t ↦ A.relativeProjTwistingSheafMul W.unop m n s t)
    (fun s s' t ↦ (A.relativeProjTwistingSheafMul W.unop m n).map_add₂ s s' t)
    (fun r s t ↦ (A.relativeProjTwistingSheafMul W.unop m n).map_smul₂ r s t)
    (fun s t t' ↦ (A.relativeProjTwistingSheafMul W.unop m n s).map_add t t')
    (fun r s t ↦ (A.relativeProjTwistingSheafMul W.unop m n s).map_smul r t)
  naturality i := ModuleCat.MonoidalCategory.tensor_ext fun s t ↦
    (A.res_relativeProjTwistingSheafMul i.unop s t).symm

/-- Over an open `W`, the multiplication morphism is the linear map
`Γ(W, 𝒪(m)) ⊗ Γ(W, 𝒪(n)) → Γ(W, 𝒪(m + n))` induced by multiplication of sections. -/
@[simp]
theorem _root_.CategoryTheory.CommMon.relativeProjTwistingSheafTensorPresheafHom_app
    (W : A.relativeProj.Opens) :
    ModuleCat.Hom.hom (R := A.relativeProj.sheaf.obj.obj (op W))
        ((A.relativeProjTwistingSheafTensorPresheafHom m n).app (op W)) =
      TensorProduct.lift (A.relativeProjTwistingSheafMul W m n) :=
  TensorProduct.ext' fun _ _ ↦ rfl

/-- Over an open `W`, the multiplication morphism sends an element of
`Γ(W, 𝒪(m)) ⊗ Γ(W, 𝒪(n))` to its image under the map induced by multiplication of sections. -/
theorem _root_.CategoryTheory.CommMon.relativeProjTwistingSheafTensorPresheafHom_app_apply
    (W : A.relativeProj.Opens)
    (w : Γ(A.relativeProjTwistingSheaf m, W) ⊗[Γ(A.relativeProj, W)]
      Γ(A.relativeProjTwistingSheaf n, W)) :
    (A.relativeProjTwistingSheafTensorPresheafHom m n).app (op W) w =
      TensorProduct.lift (A.relativeProjTwistingSheafMul W m n) w :=
  congrArg (fun φ ↦ φ w) (A.relativeProjTwistingSheafTensorPresheafHom_app m n W)

section Chart

variable {A} {m n : ℤ} {U : X.AffineZariskiSite} {W : A.relativeProj.Opens}

/-- Over an open inside the image of the chart over `U`, sections of `𝒪(k)` are determined by
their images in the chart, and every section of the chart's `𝒪(k)` is such an image. -/
private theorem bijective_chartSection (k : ℤ)
    (hW : W ≤ (colimit.ι A.relativeProjGluingData.functor U).opensRange) :
    Function.Bijective (chartSection A k U (W := W)) :=
  (A.relativeProjTwistingSheafGlueData k).bijective_π_app
    (A.bijective_relativeProjTwistingSheafGlueData_map_app k) hW

/-- Over an open inside the image of the chart over `U`, restriction of functions to the chart is
bijective, since the chart is an open immersion. -/
private theorem bijective_chartRes
    (hW : W ≤ (colimit.ι A.relativeProjGluingData.functor U).opensRange) :
    Function.Bijective (chartRes A U (W := W)) := by
  have := (colimit.ι A.relativeProjGluingData.functor U).isIso_app W hW
  exact ConcreteCategory.bijective_of_isIso ((colimit.ι A.relativeProjGluingData.functor U).app W)

/-- Over an open `W` inside the image of the chart over `U` whose preimage lies in the standard
open `D₊(f)` of an element `f` of degree one, the section of `𝒪(k)` whose image in the chart is
the basis section `fᵏ`. -/
private def chartGen (f : A.gradedSectionsGrading U.toOpens 1)
    (hW : W ≤ (colimit.ι A.relativeProjGluingData.functor U).opensRange)
    (hf : chartOpen A W U ≤ Proj.basicOpen (A.gradedSectionsGrading U.toOpens) f.1) (k : ℤ) :
    Γ(A.relativeProjTwistingSheaf k, W) :=
  (Equiv.ofBijective _ (bijective_chartSection k hW)).symm
    (chartGenerator k f.1 f.2 (chartOpen A W U) hf)

private theorem chartSection_chartGen (f : A.gradedSectionsGrading U.toOpens 1)
    (hW : W ≤ (colimit.ι A.relativeProjGluingData.functor U).opensRange)
    (hf : chartOpen A W U ≤ Proj.basicOpen (A.gradedSectionsGrading U.toOpens) f.1) (k : ℤ) :
    chartSection A k U (chartGen f hW hf k) = chartGenerator k f.1 f.2 (chartOpen A W U) hf :=
  (Equiv.ofBijective _ (bijective_chartSection k hW)).apply_symm_apply _

/-- The sections of `𝒪(k)` over `W` are free of rank one on the section `fᵏ`. -/
private theorem bijective_smul_chartGen (f : A.gradedSectionsGrading U.toOpens 1)
    (hW : W ≤ (colimit.ι A.relativeProjGluingData.functor U).opensRange)
    (hf : chartOpen A W U ≤ Proj.basicOpen (A.gradedSectionsGrading U.toOpens) f.1) (k : ℤ) :
    Function.Bijective fun r : Γ(A.relativeProj, W) ↦ r • chartGen f hW hf k := by
  have h : (chartSection A k U ∘ fun r : Γ(A.relativeProj, W) ↦ r • chartGen f hW hf k) =
      chartSectionsLinearEquiv k f.1 f.2 (chartOpen A W U) hf ∘ chartRes A U :=
    funext fun r ↦ (chartSection_smul A k U r _).trans <|
      (congrArg (chartRes A U r • ·) (chartSection_chartGen f hW hf k)).trans
        (chartSectionsLinearEquiv_apply k f.1 f.2 _ hf _).symm
  refine (Function.Bijective.of_comp_iff' (bijective_chartSection k hW) _).mp ?_
  rw [h]
  exact (LinearEquiv.bijective _).comp (bijective_chartRes hW)

/-- The sections `fᵐ` and `fⁿ` multiply to `fᵐ⁺ⁿ`. -/
private theorem mul_chartGen (f : A.gradedSectionsGrading U.toOpens 1)
    (hW : W ≤ (colimit.ι A.relativeProjGluingData.functor U).opensRange)
    (hf : chartOpen A W U ≤ Proj.basicOpen (A.gradedSectionsGrading U.toOpens) f.1) :
    A.relativeProjTwistingSheafMul W m n (chartGen f hW hf m) (chartGen f hW hf n) =
      chartGen f hW hf (m + n) :=
  (bijective_chartSection (m + n) hW).1 <|
    (chartSection_relativeProjTwistingSheafMul U _ _).trans <|
      (congrArg₂ (fun a b ↦ chartMul A W U m n a b) (chartSection_chartGen f hW hf m)
        (chartSection_chartGen f hW hf n)).trans <|
      (mul_chartGenerator n f.1 f.2 _ hf m).trans (chartSection_chartGen f hW hf (m + n)).symm

/-- The trivialization `r ↦ r • fᵏ` of the sections of `𝒪(k)` over `W`. -/
private def chartLinearEquiv (f : A.gradedSectionsGrading U.toOpens 1)
    (hW : W ≤ (colimit.ι A.relativeProjGluingData.functor U).opensRange)
    (hf : chartOpen A W U ≤ Proj.basicOpen (A.gradedSectionsGrading U.toOpens) f.1) (k : ℤ) :
    Γ(A.relativeProj, W) ≃ₗ[Γ(A.relativeProj, W)] Γ(A.relativeProjTwistingSheaf k, W) :=
  LinearEquiv.ofBijective (LinearMap.toSpanSingleton _ _ (chartGen f hW hf k))
    (bijective_smul_chartGen f hW hf k)

private theorem chartLinearEquiv_apply (f : A.gradedSectionsGrading U.toOpens 1)
    (hW : W ≤ (colimit.ι A.relativeProjGluingData.functor U).opensRange)
    (hf : chartOpen A W U ≤ Proj.basicOpen (A.gradedSectionsGrading U.toOpens) f.1) (k : ℤ)
    (r : Γ(A.relativeProj, W)) :
    chartLinearEquiv f hW hf k r = r • chartGen f hW hf k :=
  (rfl)

/-- Over an open `W` inside the image of the chart over `U` whose preimage lies in a degree-one
standard open `D₊(f)`, multiplication of sections induces a bijection
`Γ(W, 𝒪(m)) ⊗ Γ(W, 𝒪(n)) → Γ(W, 𝒪(m + n))`. -/
private theorem bijective_lift_relativeProjTwistingSheafMul
    (f : A.gradedSectionsGrading U.toOpens 1)
    (hW : W ≤ (colimit.ι A.relativeProjGluingData.functor U).opensRange)
    (hf : chartOpen A W U ≤ Proj.basicOpen (A.gradedSectionsGrading U.toOpens) f.1) :
    Function.Bijective (TensorProduct.lift (A.relativeProjTwistingSheafMul W m n)) := by
  let e := TensorProduct.congr (chartLinearEquiv f hW hf m).symm
      (chartLinearEquiv f hW hf n).symm ≪≫ₗ TensorProduct.lid Γ(A.relativeProj, W) _ ≪≫ₗ
    chartLinearEquiv f hW hf (m + n)
  have : TensorProduct.lift (A.relativeProjTwistingSheafMul W m n) = e.toLinearMap :=
    TensorProduct.ext' fun s t ↦ by
      obtain ⟨a, rfl⟩ := (chartLinearEquiv f hW hf m).surjective s
      obtain ⟨b, rfl⟩ := (chartLinearEquiv f hW hf n).surjective t
      simp only [e, LinearEquiv.coe_coe, LinearEquiv.trans_apply, TensorProduct.congr_tmul,
        LinearEquiv.symm_apply_apply, TensorProduct.lid_tmul, TensorProduct.lift.tmul]
      -- the substantive step: the basis sections `fᵐ` and `fⁿ` multiply to `fᵐ⁺ⁿ`
      simp only [chartLinearEquiv_apply, map_smul, LinearMap.smul_apply, mul_chartGen,
        smul_eq_mul, smul_smul, mul_comm]
  rw [this]
  exact e.bijective

end Chart

section Cover

variable (h : ∀ U : X.Opens, IsAffineOpen U →
  ⨆ f : A.gradedSectionsGrading U 1, Proj.basicOpen (A.gradedSectionsGrading U) f = ⊤)
include h

/-- If the degree-one standard opens cover every chart, every point of an open `W` of the
relative `Proj` has a neighbourhood in `W` over which multiplication of sections of twisting
sheaves is bijective on tensor products. -/
private theorem exists_le_bijective_lift {W : A.relativeProj.Opens} {x : A.relativeProj}
    (hx : x ∈ W) : ∃ W' ≤ W, x ∈ W' ∧
      Function.Bijective (TensorProduct.lift (A.relativeProjTwistingSheafMul W' m n)) := by
  obtain ⟨U, y, rfl⟩ : ∃ (U : X.AffineZariskiSite) (y : Proj (A.gradedSectionsGrading U.toOpens)),
      colimit.ι A.relativeProjGluingData.functor U y = x :=
    A.relativeProjCover.exists_eq x
  obtain ⟨f, hy⟩ := TopologicalSpace.Opens.mem_iSup.mp ((h U.toOpens U.2).ge (Set.mem_univ y))
  refine ⟨W ⊓ colimit.ι A.relativeProjGluingData.functor U ''ᵁ Proj.basicOpen _ f.1, inf_le_left,
    ⟨hx, y, hy, rfl⟩, bijective_lift_relativeProjTwistingSheafMul f
      (inf_le_right.trans (Scheme.Hom.image_le_opensRange _ _)) fun z hz ↦ ?_⟩
  -- the chart is injective, so a point mapping into the image of `D₊(f)` lies in `D₊(f)`
  exact ((colimit.ι A.relativeProjGluingData.functor U).preimage_image_eq
    (Proj.basicOpen _ f.1)).le hz.2

/-- Multiplication of sections is locally surjective on tensor products of sections. -/
private theorem isLocallySurjective_relativeProjTwistingSheafTensorPresheafHom :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology A.relativeProj)
      ((PresheafOfModules.toPresheaf A.relativeProj.ringCatSheaf.obj).map
        (A.relativeProjTwistingSheafTensorPresheafHom m n)) where
  imageSieve_mem {W} s x hx := by
    obtain ⟨W', hW', hxW', hbij⟩ := exists_le_bijective_lift A m n h hx
    obtain ⟨w, hw⟩ := hbij.2 ((A.relativeProjTwistingSheaf (m + n)).presheaf.map (homOfLE hW').op s)
    exact ⟨_, homOfLE hW',
      ⟨w, (A.relativeProjTwistingSheafTensorPresheafHom_app_apply m n _ w).trans hw⟩, hxW'⟩

/-- Multiplication of sections is locally injective on tensor products of sections. -/
private theorem isLocallyInjective_relativeProjTwistingSheafTensorPresheafHom :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology A.relativeProj)
      ((PresheafOfModules.toPresheaf A.relativeProj.ringCatSheaf.obj).map
        (A.relativeProjTwistingSheafTensorPresheafHom m n)) where
  equalizerSieve_mem {W} z z' hz x hx := by
    obtain ⟨W', hW', hxW', hbij⟩ := exists_le_bijective_lift A m n h hx
    refine ⟨_, homOfLE hW', hbij.1 ?_, hxW'⟩
    refine (A.relativeProjTwistingSheafTensorPresheafHom_app_apply m n _ _).symm.trans
      (Eq.trans ?_ (A.relativeProjTwistingSheafTensorPresheafHom_app_apply m n _ _))
    exact (PresheafOfModules.naturality_apply (A.relativeProjTwistingSheafTensorPresheafHom m n)
        (homOfLE hW').op z).trans
      ((congrArg ((A.relativeProjTwistingSheaf (m + n)).val.map (homOfLE hW').op) hz).trans
        (PresheafOfModules.naturality_apply (A.relativeProjTwistingSheafTensorPresheafHom m n)
          (homOfLE hW').op z').symm)

/-- Sheafification of multiplication is an isomorphism, since multiplication is locally
bijective. -/
private theorem isIso_sheafification_map_relativeProjTwistingSheafTensorPresheafHom :
    IsIso ((PresheafOfModules.sheafification (R := A.relativeProj.ringCatSheaf)
      (𝟙 A.relativeProj.ringCatSheaf.obj)).map
        (A.relativeProjTwistingSheafTensorPresheafHom m n)) := by
  have := isLocallySurjective_relativeProjTwistingSheafTensorPresheafHom A m n h
  have := isLocallyInjective_relativeProjTwistingSheafTensorPresheafHom A m n h
  -- Mathlib identifies local bijectivity with the inverse image of isomorphisms under
  -- sheafification; the two sides have different categorical wrappers.
  change ((MorphismProperty.isomorphisms _).inverseImage
    (PresheafOfModules.sheafification (R := A.relativeProj.ringCatSheaf)
      (𝟙 A.relativeProj.ringCatSheaf.obj))) (A.relativeProjTwistingSheafTensorPresheafHom m n)
  rw [← PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms]
  exact (Opens.grothendieckTopology A.relativeProj).W_of_isLocallyBijective _

/-- **Multiplication identifies `𝒪(m) ⊗ 𝒪(n)` with `𝒪(m + n)` on a relative `Proj`** when, over
every affine open `U` of `X`, the standard opens of the elements of degree one cover the chart
`Proj (⨁ n, Γ(Aₙ, U))`. -/
def _root_.CategoryTheory.CommMon.relativeProjTwistingSheafTensorProductIso :
    TauCeti.SheafOfModules.tensorProduct A.relativeProj.sheaf (A.relativeProjTwistingSheaf m)
      (A.relativeProjTwistingSheaf n) ≅ A.relativeProjTwistingSheaf (m + n) :=
  TauCeti.SheafOfModules.tensorProductIso A.relativeProj.sheaf _ _ ≪≫
    @asIso _ _ _ _ _
      (isIso_sheafification_map_relativeProjTwistingSheafTensorPresheafHom A m n h) ≪≫
    TauCeti.SheafOfModules.sheafificationIso A.relativeProj.ringCatSheaf _

/-- The forward isomorphism is sheafified multiplication of sections. -/
private theorem relativeProjTwistingSheafTensorProductIso_hom :
    (A.relativeProjTwistingSheafTensorProductIso m n h).hom =
      (TauCeti.SheafOfModules.tensorProductIso A.relativeProj.sheaf _ _).hom ≫
        (PresheafOfModules.sheafification (R := A.relativeProj.ringCatSheaf)
          (𝟙 A.relativeProj.ringCatSheaf.obj)).map
          (A.relativeProjTwistingSheafTensorPresheafHom m n) ≫
        (TauCeti.SheafOfModules.sheafificationIso A.relativeProj.ringCatSheaf _).hom :=
  (rfl)

/-- On a pure tensor `s ⊗ t` of sections over `W`, sent into `𝒪(m) ⊗ 𝒪(n)` by the unit of
sheafification, the isomorphism `𝒪(m) ⊗ 𝒪(n) ≅ 𝒪(m + n)` is multiplication of sections. -/
@[simp]
theorem _root_.CategoryTheory.CommMon.relativeProjTwistingSheafTensorProductIso_hom_tmul
    (W : A.relativeProj.Opens) (s : Γ(A.relativeProjTwistingSheaf m, W))
    (t : Γ(A.relativeProjTwistingSheaf n, W)) :
    Scheme.Modules.Hom.app
      ((TauCeti.SheafOfModules.tensorProductIso A.relativeProj.sheaf (A.relativeProjTwistingSheaf m)
        (A.relativeProjTwistingSheaf n)).inv ≫
          (A.relativeProjTwistingSheafTensorProductIso m n h).hom) W
      (((PresheafOfModules.sheafificationAdjunction (𝟙 A.relativeProj.ringCatSheaf.obj)).unit.app
        (PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := A.relativeProj.sheaf.obj)
          (A.relativeProjTwistingSheaf m).val (A.relativeProjTwistingSheaf n).val)).app (op W)
            (s ⊗ₜ t)) =
      A.relativeProjTwistingSheafMul W m n s t := by
  let P := PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := A.relativeProj.sheaf.obj)
    (A.relativeProjTwistingSheaf m).val (A.relativeProjTwistingSheaf n).val
  let F := PresheafOfModules.sheafification (R := A.relativeProj.ringCatSheaf)
    (𝟙 A.relativeProj.ringCatSheaf.obj)
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 A.relativeProj.ringCatSheaf.obj)
  have hunit : adj.unit.app P ≫ (F.map (A.relativeProjTwistingSheafTensorPresheafHom m n) ≫
      (TauCeti.SheafOfModules.sheafificationIso A.relativeProj.ringCatSheaf _).hom).val =
      A.relativeProjTwistingSheafTensorPresheafHom m n :=
    TauCeti.SheafOfModules.unit_comp_val_sheafification_map_comp_sheafificationIso_hom
      (R := A.relativeProj.ringCatSheaf) (P := P) (M := A.relativeProjTwistingSheaf (m + n))
      (A.relativeProjTwistingSheafTensorPresheafHom m n)
  have hmap :
      (TauCeti.SheafOfModules.tensorProductIso A.relativeProj.sheaf _ _).inv ≫
        (A.relativeProjTwistingSheafTensorProductIso m n h).hom =
      F.map (A.relativeProjTwistingSheafTensorPresheafHom m n) ≫
        (TauCeti.SheafOfModules.sheafificationIso A.relativeProj.ringCatSheaf _).hom := by
    exact (congrArg
      (fun g ↦ (TauCeti.SheafOfModules.tensorProductIso A.relativeProj.sheaf _ _).inv ≫ g)
      (relativeProjTwistingSheafTensorProductIso_hom A m n h)).trans (Iso.inv_hom_id_assoc _ _)
  have hU := congrArg (fun g ↦ g.app (op W) (s ⊗ₜ t))
    ((congrArg (fun g ↦ adj.unit.app P ≫ g.val) hmap).trans hunit)
  -- Unfold the forgetful functor and the sheafification unit in `hU`, to express their action
  -- as `Hom.app` on the sectionwise pure tensor.
  change Scheme.Modules.Hom.app
      ((TauCeti.SheafOfModules.tensorProductIso A.relativeProj.sheaf (A.relativeProjTwistingSheaf m)
        (A.relativeProjTwistingSheaf n)).inv ≫
          (A.relativeProjTwistingSheafTensorProductIso m n h).hom) W
      ((adj.unit.app P).app (op W) (s ⊗ₜ t)) = A.relativeProjTwistingSheafMul W m n s t at hU
  exact hU

end Cover

/-- **`𝒪(n) ≅ 𝒪(1)^{⊗ n}` on a relative `Proj`.** If, over every affine open `U` of `X`, the
standard opens of the elements of degree one cover the chart `Proj (⨁ n, Γ(Aₙ, U))`, then all
twisting sheaves of the relative `Proj` are invertible, and the class of `𝒪(n)` in the group of
line-bundle classes is the `n`-th power of the class of `𝒪(1)`, for every `n ∈ ℤ`. -/
theorem
    _root_.CategoryTheory.CommMon.lineBundleClass_relativeProjTwistingSheaf_eq_zpow_of_iSup_eq_top
    (h : ∀ U : X.Opens, IsAffineOpen U →
      ⨆ f : A.gradedSectionsGrading U 1, Proj.basicOpen (A.gradedSectionsGrading U) f = ⊤)
    (n : ℤ) :
    TauCeti.AlgebraicGeometry.LineBundleClass.mk ⟨A.relativeProjTwistingSheaf n,
        A.isInvertible_relativeProjTwistingSheaf_of_iSup_eq_top h n⟩ =
      TauCeti.AlgebraicGeometry.LineBundleClass.mk ⟨A.relativeProjTwistingSheaf 1,
        A.isInvertible_relativeProjTwistingSheaf_of_iSup_eq_top h 1⟩ ^ n := by
  let φ : Multiplicative ℤ →* TauCeti.AlgebraicGeometry.LineBundleClass A.relativeProj :=
    MonoidHom.mk' (fun a ↦ TauCeti.AlgebraicGeometry.LineBundleClass.mk
      ⟨A.relativeProjTwistingSheaf a.toAdd,
        A.isInvertible_relativeProjTwistingSheaf_of_iSup_eq_top h a.toAdd⟩)
      fun a b ↦ by
        rw [← TauCeti.AlgebraicGeometry.LineBundleClass.mk_tensorProduct,
          TauCeti.AlgebraicGeometry.LineBundleClass.mk_eq_mk_iff,
          TauCeti.AlgebraicGeometry.InvertibleSheaf.tensorProduct_obj, toAdd_mul]
        exact ⟨(A.relativeProjTwistingSheafTensorProductIso a.toAdd b.toAdd h).symm⟩
  have := φ.map_zpow (Multiplicative.ofAdd 1) n
  rwa [← ofAdd_zsmul, zsmul_one] at this

/-- **`𝒪(n) ≅ 𝒪(1)^{⊗ n}` on the relative `Proj` of an algebra generated in degree one**: if,
over every affine open `U` of `X`, the ring `⨁ n, Γ(Aₙ, U)` is generated by `Γ(A₁, U)` as an
algebra over `Γ(A₀, U)`, then the class of `𝒪(n)` in the group of line-bundle classes of the
relative `Proj` is the `n`-th power of the class of `𝒪(1)`, for every `n ∈ ℤ`. -/
@[stacks 01O4 "second part"]
theorem _root_.CategoryTheory.CommMon.lineBundleClass_relativeProjTwistingSheaf_eq_zpow
    (h : ∀ U : X.Opens, IsAffineOpen U →
      Algebra.adjoin (A.gradedSectionsGrading U 0)
        (A.gradedSectionsGrading U 1 : Set (⨁ n, Γ(A.X n, U))) = ⊤)
    (n : ℤ) :
    TauCeti.AlgebraicGeometry.LineBundleClass.mk
        ⟨A.relativeProjTwistingSheaf n, A.isInvertible_relativeProjTwistingSheaf h n⟩ =
      TauCeti.AlgebraicGeometry.LineBundleClass.mk
        ⟨A.relativeProjTwistingSheaf 1, A.isInvertible_relativeProjTwistingSheaf h 1⟩ ^ n :=
  A.lineBundleClass_relativeProjTwistingSheaf_eq_zpow_of_iSup_eq_top (fun U hU ↦
    Proj.iSup_basicOpen_eq_top' _ _ (fun f ↦ ⟨1, f.2⟩) (by simpa using h U hU)) n

end TauCeti
