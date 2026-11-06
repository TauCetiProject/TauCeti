/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Sites.SmallAffineZariski
public import TauCeti.AlgebraicGeometry.Frobenius.Perfection.Affine
public import TauCeti.RingTheory.Perfect.FrobeniusColimit
public import TauCeti.RingTheory.Perfect.Localization

/-!
# The perfection of a scheme

Let `p` be a prime and `X` a scheme in which `p` vanishes. The *perfection* `X^perf` of `X` is
glued from the spectra `Spec (Γ(X, U)^perf)` over the affine opens `U` of `X`, where
`Γ(X, U)^perf` is the colimit of `Γ(X, U) → Γ(X, U) → ⋯` along the `p`-th power map
(`CommRingCat.frobeniusTower`). It comes with a morphism `X^perf ⟶ X`, which over each affine open
`U` is `Spec` of the colimit map `Γ(X, U) ⟶ Γ(X, U)^perf`. These rings glue because perfection
commutes with localization (`IsPRadical.isLocalization_map`). The gluing follows Mathlib's relative
normalization `AlgebraicGeometry.Scheme.Hom.normalization`, through the relative gluing data
`AlgebraicGeometry.Scheme.AffineZariskiSite.relativeGluingData` of a coequifibered presheaf.

The scheme `X^perf` is perfect and `X^perf ⟶ X` is a universal homeomorphism. Every morphism
from a perfect scheme `Y` to `X` lifts uniquely to `X^perf`, so `X ↦ X^perf` is right adjoint to
the inclusion of perfect schemes into schemes over `𝔽_p`, and a perfect scheme is its own
perfection.

The colimit perfection is used rather than Mathlib's `PerfectClosure`, which asks for
`CharP Γ(X, U) p`: the sections over the empty open form the zero ring, which has no
characteristic `p`.

## Main definitions

* `AlgebraicGeometry.Scheme.perfection X p hX`: the perfection `X^perf` of `X`.
* `AlgebraicGeometry.Scheme.fromPerfection X p hX`: the morphism `X^perf ⟶ X`.
* `AlgebraicGeometry.Scheme.IsPerfect.homPerfectionEquiv`: for a perfect scheme `Y`, the
  bijection `(Y ⟶ X^perf) ≃ (Y ⟶ X)` given by composition with `X^perf ⟶ X`.

## Main results

* `AlgebraicGeometry.Scheme.isPerfect_perfection`: the perfection of `X` is perfect.
* `AlgebraicGeometry.Scheme.isUniversalHomeomorphism_fromPerfection`: `X^perf ⟶ X` is a universal
  homeomorphism.
* `AlgebraicGeometry.Scheme.IsPerfect.bijective_comp_fromPerfection`: morphisms from a perfect
  scheme to `X` lift uniquely to `X^perf`.
* `AlgebraicGeometry.Scheme.isIso_fromPerfection`: a perfect scheme is its own perfection.

## References

* B. Bhatt and P. Scholze, *Projectivity of the Witt vector affine Grassmannian*, Invent. Math.
  209 (2017), Definition 3.1, Lemma 3.4 and Proposition 3.13.
* The Stacks Project, [Tag 01LH](https://stacks.math.columbia.edu/tag/01LH), relative gluing.
-/

public section

open CategoryTheory Limits Opposite

universe u

namespace AlgebraicGeometry.Scheme

open TauCeti.AlgebraicGeometry AffineZariskiSite

variable (X : Scheme.{u}) (p : ℕ) [Fact p.Prime] (hX : (p : Γ(X, ⊤)) = 0)

/-- The Frobenius towers `Γ(X, U) → Γ(X, U) → ⋯` of the rings of sections of a scheme `X` in which
`p` vanishes, as a functor on the opens of `X`. -/
noncomputable def frobeniusTowerDiagram : X.Opensᵒᵖ ⥤ ℕ ⥤ CommRingCat.{u} where
  obj U := CommRingCat.frobeniusTower Γ(X, U.unop) p (natCast_app_eq_zero hX U.unop)
  map i := CommRingCat.frobeniusTowerMap (X.presheaf.map i) _ _
  map_id U := by rw [X.presheaf.map_id, CommRingCat.frobeniusTowerMap_id]
  map_comp i j := by rw [X.presheaf.map_comp, CommRingCat.frobeniusTowerMap_comp]

/-- The presheaf `U ↦ Γ(X, U)^perf` of perfections of the rings of sections of `X`: the colimit of
the Frobenius tower of `Γ(X, U)`. -/
noncomputable def perfectionDiagram : X.Opensᵒᵖ ⥤ CommRingCat.{u} :=
  frobeniusTowerDiagram X p hX ⋙ colim

/-- The map from the structure presheaf of `X` to the presheaf of perfections of its rings of
sections: on each open, the colimit map from the first stage of the Frobenius tower. -/
noncomputable def perfectionDiagramMap : X.presheaf ⟶ perfectionDiagram X p hX where
  app U := colimit.ι ((frobeniusTowerDiagram X p hX).obj U) 0
  naturality U V i := by
    rw [← CommRingCat.frobeniusTowerMap_app (X.presheaf.map i) (natCast_app_eq_zero hX U.unop)
      (natCast_app_eq_zero hX V.unop) 0]
    exact (colimit.ι_map ((frobeniusTowerDiagram X p hX).map i) 0).symm

/-- The map from the sections of `X` over `U` to their perfection is `p`-radical. -/
instance isPRadical_perfectionDiagramMap_app (U : X.Opensᵒᵖ) :
    IsPRadical ((perfectionDiagramMap X p hX).app U).hom p :=
  CommRingCat.isPRadical_ι_app_of_isColimit (colimit.isColimit _) 0

/-- The perfection of the sections of `X` over `U` is a perfect ring. -/
instance perfectRing_perfectionDiagram_obj (U : X.Opensᵒᵖ) :
    PerfectRing ((perfectionDiagram X p hX).obj U) p :=
  CommRingCat.perfectRing_of_isColimit (colimit.isColimit _)

/-- The prime `p` vanishes in the perfection of the sections of `X` over `U`. -/
theorem natCast_perfectionDiagram_obj_eq_zero (U : X.Opensᵒᵖ) :
    (p : (perfectionDiagram X p hX).obj U) = 0 := by
  rw [← map_natCast ((perfectionDiagramMap X p hX).app U).hom, natCast_app_eq_zero hX, map_zero]

/-- Perfection commutes with restriction to basic opens: over a basic open `D(r)` of an affine
open `U`, the perfection of `Γ(X, D(r))` is the localization of the perfection of `Γ(X, U)` away
from `r`. This is the condition under which the spectra of the perfections glue. -/
theorem coequifibered_perfectionDiagramMap :
    ((toOpensFunctor X).op.whiskerLeft (perfectionDiagramMap X p hX)).Coequifibered := by
  refine coequifibered_iff_forall_isLocalizationAway.mpr fun U r ↦ ?_
  let : Algebra Γ(X, U.1) Γ(X, X.basicOpen r) :=
    (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom.toAlgebra
  have : IsLocalization.Away r Γ(X, X.basicOpen r) := U.2.isLocalization_basicOpen r
  have := IsPRadical.isLocalization_map (p := p) (.powers r)
    ((perfectionDiagramMap X p hX).app (op U.1)).hom
    ((perfectionDiagramMap X p hX).app (op (X.basicOpen r))).hom
    ((perfectionDiagram X p hX).map (homOfLE (X.basicOpen_le r)).op).hom
    (natCast_app_eq_zero hX U.1)
    congr(($((perfectionDiagramMap X p hX).naturality (homOfLE (X.basicOpen_le r)).op)).hom).symm
  rwa [Submonoid.map_powers] at this

/-- The relative gluing data of the perfection: the spectra of the perfections of the rings of
sections over the affine opens of `X`. -/
private noncomputable def perfectionGlueData : (directedCover X).RelativeGluingData :=
  relativeGluingData (coequifibered_perfectionDiagramMap X p hX)

private instance : ((perfectionGlueData X p hX).functor ⋙ Scheme.forget).IsLocallyDirected :=
  Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..

/-- The **perfection** `X^perf` of a scheme `X` in which the prime `p` vanishes, glued from the
spectra `Spec (Γ(X, U)^perf)` of the perfections of the rings of sections over the affine opens
`U` of `X`. Bhatt–Scholze 2017, Definition 3.1. -/
noncomputable def perfection : Scheme.{u} :=
  (perfectionGlueData X p hX).glued

/-- The morphism `X^perf ⟶ X` from the perfection of `X`. Over an affine open `U` of `X` it is
`Spec` of the map from `Γ(X, U)` to its perfection. -/
noncomputable def fromPerfection : X.perfection p hX ⟶ X :=
  (perfectionGlueData X p hX).toBase

/-- The chart `Spec (Γ(X, U)^perf) ⟶ X^perf` of the perfection of `X` over an affine open `U` of
`X`: an open immersion onto the preimage of `U`. -/
noncomputable def perfectionChart (U : X.affineOpens) :
    Spec ((perfectionDiagram X p hX).obj (op U.1)) ⟶ X.perfection p hX :=
  (perfectionGlueData X p hX).cover.f U

instance (U : X.affineOpens) : IsOpenImmersion (perfectionChart X p hX U) :=
  (perfectionGlueData X p hX).cover.map_prop U

/-- Over an affine open `U` of `X`, the morphism `X^perf ⟶ X` restricts to `Spec` of the map from
`Γ(X, U)` to its perfection. -/
@[reassoc]
theorem perfectionChart_fromPerfection (U : X.affineOpens) :
    perfectionChart X p hX U ≫ X.fromPerfection p hX =
      Spec.map ((perfectionDiagramMap X p hX).app (op U.1)) ≫ U.2.fromSpec :=
  colimit.ι_desc _ _

/-- The preimage in `X^perf` of an affine open `U` of `X` is the chart `Spec (Γ(X, U)^perf)`:
the square formed by `X^perf ⟶ X`, the open immersions of `U` and of the chart, and `Spec` of the
map from `Γ(X, U)` to its perfection is cartesian. -/
theorem isPullback_perfectionChart (U : X.affineOpens) :
    IsPullback (Spec.map ((perfectionDiagramMap X p hX).app (op U.1)) ≫ U.2.isoSpec.inv)
      (perfectionChart X p hX U) U.1.ι (X.fromPerfection p hX) :=
  (perfectionGlueData X p hX).isPullback_natTrans_ι_toBase U

/-- The prime `p` vanishes on the perfection of `X`. -/
theorem natCast_perfection_eq_zero : (p : Γ(X.perfection p hX, ⊤)) = 0 :=
  natCast_eq_zero_of_hom (X.fromPerfection p hX) hX

/-- **The perfection of a scheme is perfect.** -/
instance isPerfect_perfection : IsPerfect (X.perfection p hX) p :=
  have (U : X.AffineZariskiSite) : IsPerfect ((perfectionGlueData X p hX).cover.X U) p :=
    (isPerfect_Spec_iff _).2 ⟨natCast_perfectionDiagram_obj_eq_zero X p hX _,
      perfectRing_perfectionDiagram_obj X p hX _⟩
  @IsPerfect.of_openCover _ p _ (perfectionGlueData X p hX).cover this

/-- **The morphism from the perfection of a scheme is a universal homeomorphism.** Over each affine
open `U` it is `Spec` of the `p`-radical map from `Γ(X, U)` to its perfection. -/
instance isUniversalHomeomorphism_fromPerfection :
    IsUniversalHomeomorphism (X.fromPerfection p hX) := by
  refine IsZariskiLocalAtTarget.of_openCover (directedCover X) fun U ↦ ?_
  have := IsUniversalHomeomorphism.SpecMap_of_isPRadical
    ((perfectionDiagramMap X p hX).app (op U.1)) p (natCast_perfectionDiagram_obj_eq_zero X p hX _)
  have hP := (isPullback_perfectionChart X p hX U).flip
  have : IsUniversalHomeomorphism (hP.isoPullback.hom ≫ Limits.pullback.snd _ _) := by
    rw [hP.isoPullback_hom_snd]
    infer_instance
  exact (MorphismProperty.cancel_left_of_respectsIso @IsUniversalHomeomorphism
    hP.isoPullback.hom _).1 this

namespace IsPerfect

variable {X p hX} (Y : Scheme.{u}) [IsPerfect Y p]

/-- Over an affine open `U` of `X`, morphisms from a perfect scheme to `U` lift uniquely to the
chart `Spec (Γ(X, U)^perf)` of the perfection. -/
private theorem bijective_comp_chart (U : X.affineOpens) :
    Function.Bijective fun l : Y ⟶ Spec ((perfectionDiagram X p hX).obj (op U.1)) ↦
      l ≫ Spec.map ((perfectionDiagramMap X p hX).app (op U.1)) ≫ U.2.isoSpec.inv := by
  convert ((homSpecEquiv ((perfectionDiagramMap X p hX).app (op U.1)) Y
    (natCast_app_eq_zero hX U.1)).trans
    ((Iso.refl Y).homCongr U.2.isoSpec.symm)).bijective using 1
  ext1 l
  simp

/-- Two morphisms from a perfect scheme to the perfection of `X` agreeing after composition with
`X^perf ⟶ X` are equal: they agree over the preimage of every affine open `U` of `X`, where both
factor through the chart `Spec (Γ(X, U)^perf)`. -/
private theorem injective_comp_fromPerfection :
    Function.Injective fun g : Y ⟶ X.perfection p hX ↦ g ≫ X.fromPerfection p hX := by
  intro g g' hg
  simp only at hg
  let 𝒱 : Y.OpenCover := (directedCover X).pullback₁ (g ≫ X.fromPerfection p hX)
  refine Cover.hom_ext 𝒱 _ _ fun (U : X.AffineZariskiSite) ↦ ?_
  have : IsOpenImmersion (𝒱.f U) := 𝒱.map_prop U
  have : IsPerfect (𝒱.X U) p := of_etale (𝒱.f U)
  have hP := isPullback_perfectionChart X p hX U
  have h₁ : (directedCover X).pullbackHom (g ≫ X.fromPerfection p hX) U ≫ U.1.ι =
      (𝒱.f U ≫ g) ≫ X.fromPerfection p hX := by
    rw [Cover.pullbackHom_map, Category.assoc]
  -- `g ≫ X.fromPerfection p hX` occurs in the type of `𝒱`, so `hg` is applied by `congrArg`.
  have h₂ : (directedCover X).pullbackHom (g ≫ X.fromPerfection p hX) U ≫ U.1.ι =
      (𝒱.f U ≫ g') ≫ X.fromPerfection p hX :=
    h₁.trans ((Category.assoc _ _ _).trans
      ((congrArg (𝒱.f U ≫ ·) hg).trans (Category.assoc _ _ _).symm))
  have hl : hP.lift _ _ h₁ = hP.lift _ _ h₂ :=
    (bijective_comp_chart (𝒱.X U) U).1 ((hP.lift_fst _ _ h₁).trans (hP.lift_fst _ _ h₂).symm)
  exact (hP.lift_snd _ _ h₁).symm.trans (hl ▸ hP.lift_snd _ _ h₂)

/-- **Morphisms from a perfect scheme lift uniquely to the perfection.** If `Y` is perfect, then
composition with `X^perf ⟶ X` is a bijection from morphisms `Y ⟶ X^perf` to morphisms `Y ⟶ X`.
Thus perfection is right adjoint to the inclusion of perfect schemes. -/
theorem bijective_comp_fromPerfection :
    Function.Bijective fun g : Y ⟶ X.perfection p hX ↦ g ≫ X.fromPerfection p hX := by
  refine ⟨injective_comp_fromPerfection Y, fun f ↦ ?_⟩
  -- Over the preimage `Y_U` of each affine open `U` of `X`, lift `Y_U ⟶ U` to the chart over `U`,
  -- and glue the lifts, which agree on overlaps by uniqueness.
  let 𝒱 : Y.OpenCover := (directedCover X).pullback₁ f
  have (U : X.AffineZariskiSite) : IsOpenImmersion (𝒱.f U) := 𝒱.map_prop U
  have (U : X.AffineZariskiSite) : IsPerfect (𝒱.X U) p := of_etale (𝒱.f U)
  choose l hl using fun U : X.AffineZariskiSite ↦
    (bijective_comp_chart (hX := hX) (𝒱.X U) U).2 ((directedCover X).pullbackHom f U)
  simp only at hl
  have hg (U : X.AffineZariskiSite) :
      l U ≫ perfectionChart X p hX U ≫ X.fromPerfection p hX = 𝒱.f U ≫ f := by
    rw [← (isPullback_perfectionChart X p hX U).w, ← Category.assoc, hl, Cover.pullbackHom_map]
  refine ⟨𝒱.glueMorphisms (fun U ↦ l U ≫ perfectionChart X p hX U)
    fun (U V : X.AffineZariskiSite) ↦ ?_, ?_⟩
  · refine injective_comp_fromPerfection _ ?_
    simp only [Category.assoc, hg, Limits.pullback.condition_assoc]
  · refine Cover.hom_ext 𝒱 _ _ fun (U : X.AffineZariskiSite) ↦ ?_
    exact (Cover.ι_glueMorphisms_assoc 𝒱 _ _ U _).trans (by rw [Category.assoc, hg])

/-- For a perfect scheme `Y`, the bijection `(Y ⟶ X^perf) ≃ (Y ⟶ X)` given by composition with
`X^perf ⟶ X`. Its inverse lifts a morphism `Y ⟶ X` to the perfection of `X`. -/
noncomputable def homPerfectionEquiv : (Y ⟶ X.perfection p hX) ≃ (Y ⟶ X) :=
  .ofBijective _ (bijective_comp_fromPerfection Y)

@[simp]
theorem homPerfectionEquiv_apply (g : Y ⟶ X.perfection p hX) :
    homPerfectionEquiv Y g = g ≫ X.fromPerfection p hX :=
  (rfl)

/-- The lift of a morphism `f : Y ⟶ X` to the perfection of `X` composes with `X^perf ⟶ X` to
`f`. -/
@[reassoc (attr := simp)]
theorem homPerfectionEquiv_symm_comp (f : Y ⟶ X) :
    (homPerfectionEquiv (hX := hX) Y).symm f ≫ X.fromPerfection p hX = f :=
  (homPerfectionEquiv Y).apply_symm_apply f

/-- Two morphisms from a perfect scheme to the perfection of `X` are equal once they agree after
composition with `X^perf ⟶ X`. -/
theorem hom_ext_perfection {g g' : Y ⟶ X.perfection p hX}
    (h : g ≫ X.fromPerfection p hX = g' ≫ X.fromPerfection p hX) : g = g' :=
  injective_comp_fromPerfection Y h

/-- The lift to the perfection of `X` is natural in the perfect source: lifting `h ≫ f` for a
morphism `h : Y' ⟶ Y` of perfect schemes is `h` followed by the lift of `f`. -/
@[simp, reassoc]
theorem homPerfectionEquiv_symm_comp_left {Y' : Scheme.{u}} [IsPerfect Y' p] (h : Y' ⟶ Y)
    (f : Y ⟶ X) :
    (homPerfectionEquiv (hX := hX) Y').symm (h ≫ f) = h ≫ (homPerfectionEquiv Y).symm f :=
  hom_ext_perfection Y' (by simp)

end IsPerfect

/-- **A perfect scheme is its own perfection**: if `X` is perfect, then `X^perf ⟶ X` is an
isomorphism, whose inverse is the lift of the identity of `X`. -/
instance isIso_fromPerfection [IsPerfect X p] : IsIso (X.fromPerfection p hX) :=
  ⟨(IsPerfect.homPerfectionEquiv X).symm (𝟙 X), IsPerfect.hom_ext_perfection _ (by simp),
    IsPerfect.homPerfectionEquiv_symm_comp X (𝟙 X)⟩

end AlgebraicGeometry.Scheme

/-! ### Checks -/

namespace AlgebraicGeometry.Scheme

open Polynomial

variable {p : ℕ} [Fact p.Prime]

/-- The prime `p` vanishes on the affine line `𝔸¹_{𝔽_p}`. -/
private theorem natCast_Spec_polynomial_eq_zero : (p : Γ(Spec (.of (ZMod p)[X]), ⊤)) = 0 := by
  rw [← map_natCast (ΓSpecIso (.of (ZMod p)[X])).inv.hom, CharP.cast_eq_zero, map_zero]

/-- The perfection of the affine line `𝔸¹_{𝔽_p}` is not an isomorphism onto it, since `𝔸¹_{𝔽_p}`
is not perfect. -/
example : ¬ IsIso ((Spec (.of (ZMod p)[X])).fromPerfection p natCast_Spec_polynomial_eq_zero) :=
  fun _ ↦ not_isPerfect_Spec_polynomial (p := p) (ZMod p)
    (IsPerfect.of_etale (inv ((Spec (.of (ZMod p)[X])).fromPerfection p _)))

/-- Every morphism from a perfect scheme to the affine line `𝔸¹_{𝔽_p}` lifts uniquely to its
perfection. -/
example (Y : Scheme.{0}) [IsPerfect Y p] :
    Function.Bijective fun f : Y ⟶ (Spec (.of (ZMod p)[X])).perfection p
        natCast_Spec_polynomial_eq_zero ↦
      f ≫ (Spec (.of (ZMod p)[X])).fromPerfection p _ :=
  IsPerfect.bijective_comp_fromPerfection Y

/-- The point `Spec 𝔽_p` is perfect, so it is its own perfection. -/
example (h : (p : Γ(Spec (.of (ZMod p)), ⊤)) = 0) :
    IsIso ((Spec (.of (ZMod p))).fromPerfection p h) :=
  inferInstance

end AlgebraicGeometry.Scheme
