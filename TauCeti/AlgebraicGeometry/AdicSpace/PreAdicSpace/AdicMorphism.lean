/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.Affinoid.Complete
public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.Affinoid.Hom
public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.Analytic
public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.LocallyOfFiniteType.Basic
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.AdicHom
import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.Affinoid.Comap
import TauCeti.RingTheory.Huber.TopologicallyFiniteType.Adic

/-!
# Adic morphisms of pre-adic spaces

A morphism `f : X ⟶ Y` of pre-adic spaces is *adic* (Huber 1994, §3) when every point of `X` has
an open affinoid neighbourhood `U`, mapped by `f` into an open affinoid `V` of `Y`, such that the
ring homomorphism `𝒪_Y(V) → 𝒪_X(U)` induced by `f` is adic (`TauCeti.Huber.IsAdicHom`). The
charts are recorded exactly as in `TauCeti.PreAdicSpace.LocallyOfFiniteType`: isomorphisms of the
restrictions of `X` and `Y` with adic spectra `Spa(B, B⁺)` and `Spa(A, A⁺)`, `B` complete and
Hausdorff, under which `f` becomes the morphism induced by a morphism of Huber pairs
`(A, A⁺) → (B, B⁺)`. Continuity of the ring maps, which every morphism has, is not enough: the
structure morphism `Spa(ℤ_p⟦T⟧, ℤ_p⟦T⟧) ⟶ Spa(ℤ_p, ℤ_p)`, for the `(p, T)`-adic topology, is not
adic.

Adic morphisms are the morphisms along which analytic points behave: Huber's Proposition 3.2(ii)
(Wedhorn, Proposition 8.39) says that, between adic spaces, `f` is adic exactly when it maps
analytic points to analytic points, and that then the ring map of *every* pair of affinoid charts
with `f(U) ⊆ V` is adic. This file proves these statements. The affinoid input is Wedhorn's
Lemma 7.46 (`TauCeti.ValuationSpectrum.isAdicHom_iff_forall_isAnalyticPoint_comap`), read through
the identification of the analytic points of `Spa(A, A⁺)` with its analytic locus
(`TauCeti.ValuationSpectrum.analyticPoints_presentationLimitPreAdicSpace`).

## Main definitions

* `TauCeti.PreAdicSpace.IsAdicMorphism`: adic morphisms of pre-adic spaces. The name avoids the
  object property `TauCeti.PreAdicSpace.isAdic` of being an adic space.

## Main results

* `TauCeti.ValuationSpectrum.isAdicHom_iff_mapsTo_analyticPoints`: a continuous homomorphism `φ`
  into a complete Hausdorff Huber ring is adic exactly when the induced morphism of adic spectra
  maps analytic points to analytic points.
* `TauCeti.PreAdicSpace.mapsTo_analyticPoints_iff_of_fac`: a morphism identified on opens with
  `g` through isomorphisms maps the analytic points over those opens to analytic points exactly
  when `g` does.
* `TauCeti.PreAdicSpace.IsAdicMorphism.mapsTo_analyticPoints`: an adic morphism maps analytic
  points to analytic points.
* `TauCeti.PreAdicSpace.isAdicHom_of_mapsTo_analyticPoints_of_fac`: for a morphism mapping
  analytic points to analytic points, the ring map of every affinoid chart is adic.
* `TauCeti.PreAdicSpace.isAdicMorphism_iff_mapsTo_analyticPoints`: a morphism from an adic space
  to a locally affinoid pre-adic space is adic exactly when it maps analytic points to analytic
  points.
* `TauCeti.ValuationSpectrum.isAdicMorphism_presentationLimitPreAdicSpaceComap_iff`: the morphism
  of adic spectra induced by `φ` is adic exactly when `φ` is.
* `TauCeti.PreAdicSpace.isAdicMorphism_id`, `TauCeti.PreAdicSpace.IsAdicMorphism.comp`,
  `TauCeti.PreAdicSpace.IsAdicMorphism.of_comp`: identities and composites of adic morphisms are
  adic, and `f` is adic when `f ≫ g` is.
* `TauCeti.PreAdicSpace.isAdicMorphism_of_isOpenImmersion`: open immersions are adic.
* `TauCeti.PreAdicSpace.isAdicMorphism_of_analyticPoints_eq_univ`: every morphism into an
  analytic space is adic.
* `TauCeti.PreAdicSpace.LocallyOfFiniteType.isAdicMorphism`: morphisms locally of finite type
  are adic.

## References

* R. Huber, *A generalization of formal schemes and rigid analytic varieties*, Math. Z. 217
  (1994), §3, definition of adic morphisms and Proposition 3.2.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Lemma 7.46 and
  Proposition 8.39.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology

namespace TauCeti

open Huber

universe u

namespace ValuationSpectrum

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
  {B : Type u} [CommRing B] [UniformSpace B] [IsUniformAddGroup B] [IsTopologicalRing B]
  [CompleteSpace B] [T2Space B] [IsHuberRing B]
  (P : PairOfDefinition A) {Aplus : Subring A} (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a)
  (hP : P.ringOfDefinition ≤ Aplus)
  (P' : PairOfDefinition B) {Bplus : Subring B} (hBplus : ∀ ⦃b⦄, b ∈ Bplus → IsPowerBounded b)
  (hP' : P'.ringOfDefinition ≤ Bplus)

/-- **Wedhorn Lemma 7.46, for adic spectra.** A continuous homomorphism `φ : A → B` into a complete
Hausdorff Huber ring, carrying `A⁺` into `B⁺`, is adic exactly when the induced morphism
`Spa(B, B⁺) ⟶ Spa(A, A⁺)` of pre-adic spaces maps analytic points to analytic points. -/
theorem isAdicHom_iff_mapsTo_analyticPoints (φ : A →+* B) (hφ : Continuous φ)
    (hplus : ∀ a ∈ Aplus, φ a ∈ Bplus)
    (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa Bplus))
      (presentationLimitPresheaf P' Bplus)) :
    IsAdicHom φ ↔ Set.MapsTo
      (presentationLimitPreAdicSpaceComap φ hφ hplus hAplus hBplus hP hP' hsheaf).base
      (presentationLimitPreAdicSpace P' Bplus hBplus hP').analyticPoints
      (presentationLimitPreAdicSpace P Aplus hAplus hP).analyticPoints := by
  rw [isAdicHom_iff_forall_isAnalyticPoint_comap hφ
      fun _ hb ↦ mem_powerBoundedSubring.mpr (hBplus hb),
    analyticPoints_presentationLimitPreAdicSpace, analyticPoints_presentationLimitPreAdicSpace]
  -- on points, the induced morphism is pullback of valuations along `φ`
  have hbase (x : presentationLimitPreAdicSpace P' Bplus hBplus hP') :
      ((presentationLimitPreAdicSpaceComap φ hφ hplus hAplus hBplus hP hP' hsheaf).base x).1 =
        comap φ x.1 := by
    rw [presentationLimitPreAdicSpaceComap_toHom, presentationLimitPresheafedSpaceComap_base]
    exact spaComap_val _ _ _ _ _ x
  refine ⟨fun h x hx ↦ ?_, fun h v hv ↦ ?_⟩
  · exact (mem_spaAnalytic_iff _ _).mpr ⟨Subtype.property _, hbase x ▸ h _ hx⟩
  · exact hbase ⟨v, spaAnalytic_subset_spa Bplus hv⟩ ▸
      ((mem_spaAnalytic_iff _ _).mp (h (x := ⟨v, spaAnalytic_subset_spa Bplus hv⟩) hv)).2

end ValuationSpectrum

namespace PreAdicSpace

open ValuationSpectrum

variable {X Y Z : PreAdicSpace.{u}}

/-- **Adic morphisms** (Huber 1994, §3): a morphism `f : X ⟶ Y` of pre-adic spaces is *adic* when
every point `x` of `X` has an open neighbourhood `U`, mapped by `f` into an open `V` of `Y`,
together with Huber pairs `(A, A⁺)` and `(B, B⁺)`, `B` complete and Hausdorff with `Spa(B, B⁺)`
having a sheaf as structure presheaf, a morphism `φ : (A, A⁺) → (B, B⁺)` whose ring homomorphism
is adic, and isomorphisms identifying `X` restricted to `U` with `Spa(B, B⁺)` and `Y` restricted to
`V` with `Spa(A, A⁺)`, under which `f` becomes the morphism induced by `φ`. -/
def IsAdicMorphism (f : X ⟶ Y) : Prop :=
  ∀ x : X, ∃ (U : Opens X) (_ : x ∈ U) (V : Opens Y) (_ : U ≤ (Opens.map f.base).obj V)
    (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A) (_ : IsTopologicalRing A)
    (_ : IsHuberRing A) (S : Pair A) (P : PairOfDefinition A) (hP : P.ringOfDefinition ≤ S.plus)
    (B : Type u) (_ : CommRing B) (_ : UniformSpace B) (_ : IsUniformAddGroup B)
    (_ : IsTopologicalRing B) (_ : CompleteSpace B) (_ : T2Space B) (_ : IsHuberRing B)
    (T : Pair B) (P' : PairOfDefinition B) (hP' : P'.ringOfDefinition ≤ T.plus)
    (φ : Pair.Hom S T) (_ : IsAdicHom φ.toRingHom)
    (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa T.plus))
      (presentationLimitPresheaf P' T.plus))
    (eU : X.restrict U.isOpenEmbedding ≅
      presentationLimitPreAdicSpace P' T.plus T.isRingOfIntegralElements.isPowerBounded_of_mem hP')
    (eV : Y.restrict V.isOpenEmbedding ≅
      presentationLimitPreAdicSpace P S.plus S.isRingOfIntegralElements.isPowerBounded_of_mem hP),
    X.ofRestrict _ ≫ f =
      eU.hom ≫ presentationLimitPreAdicSpaceComap φ.toRingHom φ.continuous_toRingHom
        φ.map_mem_plus
        S.isRingOfIntegralElements.isPowerBounded_of_mem
        T.isRingOfIntegralElements.isPowerBounded_of_mem hP hP' hsheaf ≫ eV.inv ≫ Y.ofRestrict _

/-- Unfolding lemma for `TauCeti.PreAdicSpace.IsAdicMorphism`. -/
theorem isAdicMorphism_iff (f : X ⟶ Y) : IsAdicMorphism f ↔
    ∀ x : X, ∃ (U : Opens X) (_ : x ∈ U) (V : Opens Y) (_ : U ≤ (Opens.map f.base).obj V)
      (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A) (_ : IsTopologicalRing A)
      (_ : IsHuberRing A) (S : Pair A) (P : PairOfDefinition A) (hP : P.ringOfDefinition ≤ S.plus)
      (B : Type u) (_ : CommRing B) (_ : UniformSpace B) (_ : IsUniformAddGroup B)
      (_ : IsTopologicalRing B) (_ : CompleteSpace B) (_ : T2Space B) (_ : IsHuberRing B)
      (T : Pair B) (P' : PairOfDefinition B) (hP' : P'.ringOfDefinition ≤ T.plus)
      (φ : Pair.Hom S T) (_ : IsAdicHom φ.toRingHom)
      (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa T.plus))
        (presentationLimitPresheaf P' T.plus))
      (eU : X.restrict U.isOpenEmbedding ≅
        presentationLimitPreAdicSpace P' T.plus T.isRingOfIntegralElements.isPowerBounded_of_mem
          hP')
      (eV : Y.restrict V.isOpenEmbedding ≅
        presentationLimitPreAdicSpace P S.plus S.isRingOfIntegralElements.isPowerBounded_of_mem
          hP),
      X.ofRestrict _ ≫ f =
        eU.hom ≫ presentationLimitPreAdicSpaceComap φ.toRingHom φ.continuous_toRingHom
          φ.map_mem_plus
          S.isRingOfIntegralElements.isPowerBounded_of_mem
          T.isRingOfIntegralElements.isPowerBounded_of_mem hP hP' hsheaf ≫ eV.inv ≫
            Y.ofRestrict _ :=
  Iff.rfl

/-- **Analytic points through a chart.** Suppose that on an open `U` of `X`, mapped into an open
`V` of `Y`, the morphism `f` is identified with `g : X' ⟶ Y'` through isomorphisms of the
restrictions of `X` and `Y` with `X'` and `Y'`. Then `g` maps analytic points to analytic points
exactly when `f` maps the analytic points of `X` lying in `U` to analytic points. -/
theorem mapsTo_analyticPoints_iff_of_fac {X' Y' : PreAdicSpace.{u}} {f : X ⟶ Y} {U : Opens X}
    {V : Opens Y} (eU : X.restrict U.isOpenEmbedding ≅ X') (eV : Y.restrict V.isOpenEmbedding ≅ Y')
    (g : X' ⟶ Y') (hfac : X.ofRestrict _ ≫ f = eU.hom ≫ g ≫ eV.inv ≫ Y.ofRestrict _) :
    Set.MapsTo g.base X'.analyticPoints Y'.analyticPoints ↔
      ∀ x ∈ U, x ∈ X.analyticPoints → f.base x ∈ Y.analyticPoints := by
  -- on points, `f` restricted to `U` is `eV⁻¹ ∘ g ∘ eU`
  have hpt (p : X.restrict U.isOpenEmbedding) : f.base ((X.ofRestrict _).base p) =
      (Y.ofRestrict _).base (eV.inv.base (g.base (eU.hom.base p))) := by
    simpa only [comp_base, ConcreteCategory.comp_apply] using congrArg (fun k ↦ k.base p) hfac
  refine ⟨fun hg x hxU hx ↦ ?_, fun hf y hy ↦ ?_⟩
  · -- `x` is the image of the point `p = ⟨x, hxU⟩` of the restriction of `X` to `U`
    let p : X.restrict U.isOpenEmbedding := (⟨x, hxU⟩ : U)
    have hp : (X.ofRestrict _).base p = x := by
      rw [ofRestrict_base]
      rfl
    rw [← hp, hpt p, mem_analyticPoints_iff_of_isOpenImmersion,
      mem_analyticPoints_iff_of_isOpenImmersion eV.inv]
    exact hg ((mem_analyticPoints_iff_of_isOpenImmersion eU.hom).mpr
      ((mem_analyticPoints_iff_of_isOpenImmersion (X.ofRestrict _)).mp (hp ▸ hx)))
  · -- `y` is the image of the point `p = eU⁻¹(y)` of the restriction of `X` to `U`
    set p := eU.inv.base y with hp
    have hyp : eU.hom.base p = y := by
      rw [hp, ← ConcreteCategory.comp_apply, ← comp_base, eU.inv_hom_id]
      rfl
    have hpU : (X.ofRestrict _).base p ∈ U := by
      rw [ofRestrict_base]
      -- the points of the restriction of `X` to `U` are the points of `U`
      exact (show U from p).2
    have hfp := hf _ hpU ((mem_analyticPoints_iff_of_isOpenImmersion _).mpr
      ((mem_analyticPoints_iff_of_isOpenImmersion eU.hom).mp (hyp ▸ hy)))
    rw [hpt p, hyp, mem_analyticPoints_iff_of_isOpenImmersion,
      mem_analyticPoints_iff_of_isOpenImmersion eV.inv] at hfp
    exact hfp

/-- **An adic morphism maps analytic points to analytic points** (Huber 1994, Proposition 3.2;
Wedhorn, Proposition 8.39). -/
theorem IsAdicMorphism.mapsTo_analyticPoints {f : X ⟶ Y} (hf : IsAdicMorphism f) :
    Set.MapsTo f.base X.analyticPoints Y.analyticPoints := by
  intro x hx
  obtain ⟨U, hxU, V, -, A, _, _, _, _, S, P, hP, B, _, _, _, _, _, _, _, T, P', hP', φ, hφ,
    hsheaf, eU, eV, hfac⟩ := hf x
  exact (mapsTo_analyticPoints_iff_of_fac eU eV _ hfac).mp
    ((isAdicHom_iff_mapsTo_analyticPoints P _ hP P' _ hP' φ.toRingHom φ.continuous_toRingHom
      φ.map_mem_plus hsheaf).mp hφ) x hxU hx

/-- **Every affinoid chart of a morphism preserving analytic points is adic** (Huber 1994,
Proposition 3.2(ii); Wedhorn, Proposition 8.39). If `f` maps analytic points to analytic points,
and on an open `U` mapped into an open `V` it is identified with the morphism of adic spectra
induced by a continuous homomorphism `φ : A → B` into a complete Hausdorff Huber ring, then `φ`
is adic. -/
theorem isAdicHom_of_mapsTo_analyticPoints_of_fac {f : X ⟶ Y}
    (hf : Set.MapsTo f.base X.analyticPoints Y.analyticPoints) {U : Opens X} {V : Opens Y}
    {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
    {B : Type u} [CommRing B] [UniformSpace B] [IsUniformAddGroup B] [IsTopologicalRing B]
    [CompleteSpace B] [T2Space B] [IsHuberRing B]
    (P : PairOfDefinition A) {Aplus : Subring A} (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a)
    (hP : P.ringOfDefinition ≤ Aplus)
    (P' : PairOfDefinition B) {Bplus : Subring B} (hBplus : ∀ ⦃b⦄, b ∈ Bplus → IsPowerBounded b)
    (hP' : P'.ringOfDefinition ≤ Bplus) (φ : A →+* B) (hφ : Continuous φ)
    (hplus : ∀ a ∈ Aplus, φ a ∈ Bplus)
    (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa Bplus))
      (presentationLimitPresheaf P' Bplus))
    (eU : X.restrict U.isOpenEmbedding ≅ presentationLimitPreAdicSpace P' Bplus hBplus hP')
    (eV : Y.restrict V.isOpenEmbedding ≅ presentationLimitPreAdicSpace P Aplus hAplus hP)
    (hfac : X.ofRestrict _ ≫ f = eU.hom ≫
      presentationLimitPreAdicSpaceComap φ hφ hplus hAplus hBplus hP hP' hsheaf ≫ eV.inv ≫
        Y.ofRestrict _) :
    IsAdicHom φ :=
  (isAdicHom_iff_mapsTo_analyticPoints P hAplus hP P' hBplus hP' φ hφ hplus hsheaf).mpr
    ((mapsTo_analyticPoints_iff_of_fac eU eV _ hfac).mpr fun _ _ hx ↦ hf hx)

/-- **Huber 1994, Proposition 3.2(ii)** (Wedhorn, Proposition 8.39), the converse direction: a
morphism from an adic space to a locally affinoid pre-adic space which maps analytic points to
analytic points is adic. Its charts are any open affinoid `V` around the image of a point and any
open affinoid `U ⊆ f⁻¹(V)` around the point, presented by complete Hausdorff Huber pairs. -/
theorem isAdicMorphism_of_mapsTo_analyticPoints (hX : isAdic X) (hY : isLocallyAffinoid Y)
    {f : X ⟶ Y} (hf : Set.MapsTo f.base X.analyticPoints Y.analyticPoints) :
    IsAdicMorphism f := by
  intro x
  -- an open affinoid `V` around `f x`, and an open affinoid `U ⊆ f⁻¹(V)` around `x`
  obtain ⟨V, hV, hxV, -⟩ :=
    Opens.isBasis_iff_nbhd.mp (isBasis_affinoidOpens hY) (Opens.mem_top (f.base x))
  obtain ⟨U, hU, hxU, hUV⟩ := Opens.isBasis_iff_nbhd.mp
    (isBasis_affinoidOpens hX.isLocallyAffinoid) (U := (Opens.map f.base).obj V) hxV
  obtain ⟨A, _, _, _, _, _, _, _, S, P, hP, ⟨eV⟩⟩ := (isAffinoid_iff_exists_complete _).mp hV
  obtain ⟨B, _, _, _, _, _, _, _, T, P', hP', ⟨eU⟩⟩ := (isAffinoid_iff_exists_complete _).mp hU
  have hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa T.plus))
      (presentationLimitPresheaf P' T.plus) :=
    ObjectProperty.prop_of_iso isSheafy eU (isSheafy_restrict _ hX.isSheafy)
  -- the restriction `U ⟶ V` of `f`, transported to the adic spectra
  have hrange : Set.range (X.ofRestrict U.isOpenEmbedding ≫ f).base ⊆
      Set.range (Y.ofRestrict V.isOpenEmbedding).base := by
    rintro _ ⟨p, rfl⟩
    exact ⟨⟨_, hUV p.2⟩, rfl⟩
  let fUV := IsOpenImmersion.lift (Y.ofRestrict V.isOpenEmbedding) _ hrange
  let g := eU.inv ≫ fUV ≫ eV.hom
  -- the morphism of Huber pairs recovered from `g` on global sections
  have hplus : ∀ a ∈ S.plus, presentationLimitHomRingHom P S.plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem hP P' T.plus
      T.isRingOfIntegralElements.isPowerBounded_of_mem hP' g a ∈ T.plus := by
    simpa using (presentationLimitHomPairHom P P' S T hP hP' g).map_mem_plus
  let φ : Pair.Hom S T := ⟨_, continuous_presentationLimitHomRingHom P _ _ hP P' _ _ hP' g, hplus⟩
  have hg : presentationLimitPreAdicSpaceComap φ.toRingHom φ.continuous_toRingHom φ.map_mem_plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem
      T.isRingOfIntegralElements.isPowerBounded_of_mem hP hP' hsheaf = g :=
    presentationLimitPreAdicSpaceComap_presentationLimitHomRingHom P _ _ hP P' _ _ hP' hsheaf g
      φ.map_mem_plus
  have hfac : X.ofRestrict _ ≫ f = eU.hom ≫ presentationLimitPreAdicSpaceComap φ.toRingHom
      φ.continuous_toRingHom φ.map_mem_plus S.isRingOfIntegralElements.isPowerBounded_of_mem
      T.isRingOfIntegralElements.isPowerBounded_of_mem hP hP' hsheaf ≫ eV.inv ≫
        Y.ofRestrict _ := by
    simp [hg, g, fUV]
  exact ⟨U, hxU, V, hUV, A, inferInstance, inferInstance, inferInstance, inferInstance, S, P, hP,
    B, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, T, P', hP', φ,
    isAdicHom_of_mapsTo_analyticPoints_of_fac hf P _ hP P' _ hP' _ _ _ hsheaf eU eV hfac,
    hsheaf, eU, eV, hfac⟩

/-- **Huber 1994, Proposition 3.2(ii)** (Wedhorn, Proposition 8.39): a morphism from an adic space
to a locally affinoid pre-adic space is adic exactly when it maps analytic points to analytic
points. -/
theorem isAdicMorphism_iff_mapsTo_analyticPoints (hX : isAdic X) (hY : isLocallyAffinoid Y)
    (f : X ⟶ Y) :
    IsAdicMorphism f ↔ Set.MapsTo f.base X.analyticPoints Y.analyticPoints :=
  ⟨IsAdicMorphism.mapsTo_analyticPoints, isAdicMorphism_of_mapsTo_analyticPoints hX hY⟩

/-- The identity of an adic space is adic. -/
theorem isAdicMorphism_id (hX : isAdic X) : IsAdicMorphism (𝟙 X) :=
  isAdicMorphism_of_mapsTo_analyticPoints hX hX.isLocallyAffinoid (Set.mapsTo_id _)

/-- **Composites of adic morphisms are adic**, for an adic source and a locally affinoid target. -/
theorem IsAdicMorphism.comp (hX : isAdic X) (hZ : isLocallyAffinoid Z) {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : IsAdicMorphism f) (hg : IsAdicMorphism g) : IsAdicMorphism (f ≫ g) :=
  isAdicMorphism_of_mapsTo_analyticPoints hX hZ <| by
    simpa [comp_base] using hg.mapsTo_analyticPoints.comp hf.mapsTo_analyticPoints

/-- **Cancellation**: if `f ≫ g` is adic, then so is `f`, for an adic source and a locally affinoid
middle space. A point of `Y` over an analytic point of `Z` is analytic. -/
theorem IsAdicMorphism.of_comp (hX : isAdic X) (hY : isLocallyAffinoid Y) {f : X ⟶ Y}
    {g : Y ⟶ Z} (h : IsAdicMorphism (f ≫ g)) : IsAdicMorphism f :=
  isAdicMorphism_of_mapsTo_analyticPoints hX hY fun x hx ↦
    preimage_analyticPoints_subset g (by simpa [comp_base] using h.mapsTo_analyticPoints hx)

/-- **Open immersions are adic**, for an adic source and a locally affinoid target: an open
immersion preserves analytic points. -/
theorem isAdicMorphism_of_isOpenImmersion (hX : isAdic X) (hY : isLocallyAffinoid Y) (f : X ⟶ Y)
    [IsOpenImmersion f] : IsAdicMorphism f :=
  isAdicMorphism_of_mapsTo_analyticPoints hX hY fun _ hx ↦
    (mem_analyticPoints_iff_of_isOpenImmersion f).mpr hx

/-- **Every morphism into an analytic space is adic** (Huber 1994, Proposition 3.2): if every
point of `Y` is analytic, every morphism from an adic space to `Y` is adic. -/
theorem isAdicMorphism_of_analyticPoints_eq_univ (hX : isAdic X) (hY : isLocallyAffinoid Y)
    (hYa : Y.analyticPoints = Set.univ) (f : X ⟶ Y) : IsAdicMorphism f :=
  isAdicMorphism_of_mapsTo_analyticPoints hX hY (hYa ▸ Set.mapsTo_univ _ _)

/-- **Morphisms locally of finite type are adic**: a morphism of Huber pairs topologically of
finite type into a complete Hausdorff pair is adic (Huber 1994, Lemma 3.3(ii)), so the charts of a
morphism locally of finite type witness that it is adic. -/
theorem LocallyOfFiniteType.isAdicMorphism {f : X ⟶ Y} (hf : LocallyOfFiniteType f) :
    IsAdicMorphism f := by
  intro x
  obtain ⟨U, hxU, V, hUV, A, _, _, _, _, S, P, hP, B, _, _, _, _, _, _, _, T, P', hP', φ, hφ,
    hsheaf, eU, eV, hfac⟩ := (locallyOfFiniteType_iff f).mp hf x
  exact ⟨U, hxU, V, hUV, A, inferInstance, inferInstance, inferInstance, inferInstance, S, P, hP,
    B, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, T, P', hP', φ, hφ.isTopologicallyFiniteType_toRingHom.isAdicHom, hsheaf, eU,
    eV, hfac⟩

end PreAdicSpace

namespace ValuationSpectrum

open PreAdicSpace

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
  {B : Type u} [CommRing B] [UniformSpace B] [IsUniformAddGroup B] [IsTopologicalRing B]
  [CompleteSpace B] [T2Space B] [IsHuberRing B]
  (P : PairOfDefinition A) {Aplus : Subring A} (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a)
  (hP : P.ringOfDefinition ≤ Aplus)
  (P' : PairOfDefinition B) {Bplus : Subring B} (hBplus : ∀ ⦃b⦄, b ∈ Bplus → IsPowerBounded b)
  (hP' : P'.ringOfDefinition ≤ Bplus)

/-- **Adic morphisms of affinoids** (Wedhorn, Lemma 7.46 and Proposition 8.39): for a continuous
homomorphism `φ : A → B` into a complete Hausdorff Huber ring with `Spa(B, B⁺)` sheafy, the induced
morphism `Spa(B, B⁺) ⟶ Spa(A, A⁺)` is adic exactly when `φ` is. -/
theorem isAdicMorphism_presentationLimitPreAdicSpaceComap_iff (φ : A →+* B) (hφ : Continuous φ)
    (hplus : ∀ a ∈ Aplus, φ a ∈ Bplus)
    (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa Bplus))
      (presentationLimitPresheaf P' Bplus)) :
    IsAdicMorphism (presentationLimitPreAdicSpaceComap φ hφ hplus hAplus hBplus hP hP' hsheaf) ↔
      IsAdicHom φ := by
  rw [isAdicHom_iff_mapsTo_analyticPoints P hAplus hP P' hBplus hP' φ hφ hplus hsheaf]
  exact isAdicMorphism_iff_mapsTo_analyticPoints
    (isAdic_presentationLimitPreAdicSpace P' Bplus hBplus hP' hsheaf)
    (isPreAdic_presentationLimitPreAdicSpace P Aplus hAplus hP).isLocallyAffinoid _

end ValuationSpectrum

end TauCeti
