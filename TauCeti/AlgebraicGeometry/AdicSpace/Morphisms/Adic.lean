/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.Analytic
public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.Affinoid.Comap
public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.Affinoid.Complete
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.AdicHom

/-!
# Adic morphisms of adic spaces

A morphism `f : X ⟶ Y` of adic spaces is *adic* (Huber 1994, §3) if every point of `X` has an
open neighbourhood `U`, mapped by `f` into an open `V` of `Y`, such that `U ≅ Spa(B, B⁺)` and
`V ≅ Spa(A, A⁺)` for Huber pairs, `B` complete and Hausdorff, under which `f` restricted to
`U → V` is the morphism induced by a morphism of Huber pairs `(A, A⁺) → (B, B⁺)` whose ring
homomorphism is adic (`TauCeti.Huber.IsAdicHom`). The charts are those of
`TauCeti.PreAdicSpace.LocallyOfFiniteType`, with adicness in place of topological finite type.

The main theorem identifies adic morphisms with the morphisms sending analytic points to analytic
points (Huber 1994, Proposition 3.2(ii); Wedhorn, Proposition 8.39). On an affinoid chart this is
Wedhorn's Lemma 7.46: the morphism `Spa(φ)` induced by `φ : (A, A⁺) → (B, B⁺)`, with `B` complete,
sends analytic points to analytic points exactly when `φ` is adic. Globally, a morphism sending
analytic points to analytic points restricts, over affinoid opens `U ⊆ f⁻¹(V)` with complete
models, to the morphism induced by its global-sections map, which is then adic.

Since every morphism of pre-adic spaces pulls analytic points back to analytic points, the
characterisation gives the formal properties at once: adic morphisms contain the identities, the
open immersions and every morphism into a space all of whose points are analytic (for instance
`Spa(ℚ_p, ℤ_p)`), and are stable under composition; if `f ≫ g` is adic then so is `f`. A morphism
of affinoid adic spaces induced by a morphism of Huber pairs is adic exactly when its ring
homomorphism is. Adic morphisms are thus the morphisms that restrict to the analytic loci
(`TauCeti.PreAdicSpace.analyticLocusMap`).

## Main definitions

* `TauCeti.AdicSpace.IsAdic`: adic morphisms of adic spaces.

## Main results

* `TauCeti.ValuationSpectrum.mapsTo_analyticPoints_presentationLimitPreAdicSpaceComap_iff`: the
  morphism of adic spectra induced by a morphism of Huber pairs with complete target sends
  analytic points to analytic points exactly when the ring homomorphism is adic.
* `TauCeti.AdicSpace.isAdic_iff_mapsTo_analyticPoints`: a morphism of adic spaces is adic exactly
  when it sends analytic points to analytic points.
* `TauCeti.AdicSpace.IsAdic.isMultiplicative`, `TauCeti.AdicSpace.IsAdic.respectsIso`: identities
  are adic, composites of adic morphisms are adic, and adicness is invariant under isomorphisms.
* `TauCeti.AdicSpace.IsAdic.of_isOpenImmersion`: open immersions are adic.
* `TauCeti.AdicSpace.IsAdic.of_comp`: if `f ≫ g` is adic, then `f` is adic.
* `TauCeti.AdicSpace.IsAdic.of_analyticPoints_eq_univ`: every morphism into an adic space all of
  whose points are analytic is adic.
* `TauCeti.AdicSpace.isAdic_homMk_presentationLimitPreAdicSpaceComap_iff`: a morphism of affinoid
  adic spaces induced by a morphism of Huber pairs is adic exactly when its ring homomorphism is.

## References

* R. Huber, *A generalization of formal schemes and rigid analytic varieties*, Math. Z. 217
  (1994), §3, definition of adic morphisms and Proposition 3.2.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Lemma 7.46 and
  Proposition 8.39.
-/

public section

open CategoryTheory TopologicalSpace Topology

namespace TauCeti

open Huber

universe u

namespace ValuationSpectrum

open PreAdicSpace

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  {B : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
  (P : PairOfDefinition A) (P' : PairOfDefinition B) {Aplus : Subring A} {Bplus : Subring B}
  (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) (hBplus : ∀ ⦃b⦄, b ∈ Bplus → IsPowerBounded b)
  (hP : P.ringOfDefinition ≤ Aplus) (hP' : P'.ringOfDefinition ≤ Bplus)
  (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa Bplus))
    (presentationLimitPresheaf P' Bplus))

/-- **Wedhorn Lemma 7.46(1), on adic spectra**: if `φ` is adic, the morphism `Spa(φ)` it induces
sends analytic points to analytic points. -/
theorem _root_.TauCeti.Huber.IsAdicHom.mapsTo_analyticPoints_presentationLimitPreAdicSpaceComap
    {φ : A →+* B} (hφ : IsAdicHom φ) (hplus : ∀ a ∈ Aplus, φ a ∈ Bplus) :
    Set.MapsTo (presentationLimitPreAdicSpaceComap φ hφ.continuous hplus hAplus hBplus hP hP'
        hsheaf).base
      (presentationLimitPreAdicSpace P' Bplus hBplus hP').analyticPoints
      (presentationLimitPreAdicSpace P Aplus hAplus hP).analyticPoints := by
  intro x hx
  rw [analyticPoints_presentationLimitPreAdicSpace] at hx ⊢
  have h := hφ.mapsTo_spaAnalytic hplus hx
  rw [← presentationLimitPreAdicSpaceComap_base_val φ hφ.continuous hplus hAplus hBplus hP hP'
    hsheaf x] at h
  exact h

/-- **Wedhorn Lemma 7.46, on adic spectra**: for a continuous `φ : A → B` with `B` complete, the
morphism `Spa(φ)` it induces sends analytic points to analytic points exactly when `φ` is adic. -/
theorem mapsTo_analyticPoints_presentationLimitPreAdicSpaceComap_iff {B : Type u} [CommRing B]
    [UniformSpace B] [IsUniformAddGroup B] [IsTopologicalRing B] [CompleteSpace B] [T2Space B]
    [IsHuberRing B] [IsHuberRing A] (P' : PairOfDefinition B) {Bplus : Subring B}
    (hBplus : ∀ ⦃b⦄, b ∈ Bplus → IsPowerBounded b) (hP' : P'.ringOfDefinition ≤ Bplus)
    (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa Bplus))
      (presentationLimitPresheaf P' Bplus))
    (φ : A →+* B) (hφ : Continuous φ) (hplus : ∀ a ∈ Aplus, φ a ∈ Bplus) :
    Set.MapsTo (presentationLimitPreAdicSpaceComap φ hφ hplus hAplus hBplus hP hP' hsheaf).base
        (presentationLimitPreAdicSpace P' Bplus hBplus hP').analyticPoints
        (presentationLimitPreAdicSpace P Aplus hAplus hP).analyticPoints ↔ IsAdicHom φ := by
  refine ⟨fun h ↦ isAdicHom_of_mapsTo_spaAnalytic hφ (Aplus := Aplus)
    (fun _ hb ↦ mem_powerBoundedSubring.mpr (hBplus hb)) fun v hv ↦ ?_,
    fun h ↦ h.mapsTo_analyticPoints_presentationLimitPreAdicSpaceComap P P' hAplus hBplus hP hP'
      hsheaf hplus⟩
  -- read `v` as a point of `Spa(B, B⁺)`, analytic there
  let x : presentationLimitPreAdicSpace P' Bplus hBplus hP' := ⟨v, spaAnalytic_subset_spa _ hv⟩
  have hx : x ∈ (presentationLimitPreAdicSpace P' Bplus hBplus hP').analyticPoints := by
    rw [analyticPoints_presentationLimitPreAdicSpace]
    exact hv
  have hφx := h hx
  rw [analyticPoints_presentationLimitPreAdicSpace] at hφx
  -- membership in the preimage under `Subtype.val` is membership of the underlying valuation
  have hφx' : ((presentationLimitPreAdicSpaceComap φ hφ hplus hAplus hBplus hP hP' hsheaf).base x :
      spa Aplus).1 ∈ spaAnalytic Aplus := hφx
  rwa [presentationLimitPreAdicSpaceComap_base_val] at hφx'

end ValuationSpectrum

namespace AdicSpace

open PreAdicSpace ValuationSpectrum

/-- **Adic morphisms** (Huber 1994, §3): a morphism `f : X ⟶ Y` of adic spaces is *adic* when
every point `x` of `X` has an open neighbourhood `U`, mapped by `f` into an open `V` of `Y`,
together with Huber pairs `(A, A⁺)` and `(B, B⁺)`, `B` complete and Hausdorff with `Spa(B, B⁺)`
having a sheaf as structure presheaf, a morphism `φ : (A, A⁺) → (B, B⁺)` whose ring homomorphism
is adic, and isomorphisms identifying `X` restricted to `U` with `Spa(B, B⁺)` and `Y` restricted
to `V` with `Spa(A, A⁺)`, under which `f` becomes the morphism induced by `φ`. By
`isAdic_iff_mapsTo_analyticPoints` these are the morphisms sending analytic points to analytic
points. -/
def IsAdic : MorphismProperty AdicSpace.{u} := fun X Y f ↦
  ∀ x : X.obj, ∃ (U : Opens X.obj) (_ : x ∈ U) (V : Opens Y.obj)
    (_ : U ≤ (Opens.map f.hom.base).obj V)
    (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A) (_ : IsTopologicalRing A)
    (_ : IsHuberRing A) (S : Pair A) (P : PairOfDefinition A) (hP : P.ringOfDefinition ≤ S.plus)
    (B : Type u) (_ : CommRing B) (_ : UniformSpace B) (_ : IsUniformAddGroup B)
    (_ : IsTopologicalRing B) (_ : CompleteSpace B) (_ : T2Space B) (_ : IsHuberRing B)
    (T : Pair B) (P' : PairOfDefinition B) (hP' : P'.ringOfDefinition ≤ T.plus)
    (φ : Pair.Hom S T) (_ : IsAdicHom φ.toRingHom)
    (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa T.plus))
      (presentationLimitPresheaf P' T.plus))
    (eU : X.obj.restrict U.isOpenEmbedding ≅
      presentationLimitPreAdicSpace P' T.plus T.isRingOfIntegralElements.isPowerBounded_of_mem hP')
    (eV : Y.obj.restrict V.isOpenEmbedding ≅
      presentationLimitPreAdicSpace P S.plus S.isRingOfIntegralElements.isPowerBounded_of_mem hP),
    X.obj.ofRestrict _ ≫ f.hom =
      eU.hom ≫ presentationLimitPreAdicSpaceComap φ.toRingHom φ.continuous_toRingHom
        φ.map_mem_plus
        S.isRingOfIntegralElements.isPowerBounded_of_mem
        T.isRingOfIntegralElements.isPowerBounded_of_mem hP hP' hsheaf ≫ eV.inv ≫
          Y.obj.ofRestrict _

variable {X Y Z : AdicSpace.{u}}

/-- Unfolding lemma for `TauCeti.AdicSpace.IsAdic`. -/
theorem isAdic_iff (f : X ⟶ Y) : IsAdic f ↔
    ∀ x : X.obj, ∃ (U : Opens X.obj) (_ : x ∈ U) (V : Opens Y.obj)
      (_ : U ≤ (Opens.map f.hom.base).obj V)
      (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A) (_ : IsTopologicalRing A)
      (_ : IsHuberRing A) (S : Pair A) (P : PairOfDefinition A) (hP : P.ringOfDefinition ≤ S.plus)
      (B : Type u) (_ : CommRing B) (_ : UniformSpace B) (_ : IsUniformAddGroup B)
      (_ : IsTopologicalRing B) (_ : CompleteSpace B) (_ : T2Space B) (_ : IsHuberRing B)
      (T : Pair B) (P' : PairOfDefinition B) (hP' : P'.ringOfDefinition ≤ T.plus)
      (φ : Pair.Hom S T) (_ : IsAdicHom φ.toRingHom)
      (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa T.plus))
        (presentationLimitPresheaf P' T.plus))
      (eU : X.obj.restrict U.isOpenEmbedding ≅
        presentationLimitPreAdicSpace P' T.plus T.isRingOfIntegralElements.isPowerBounded_of_mem
          hP')
      (eV : Y.obj.restrict V.isOpenEmbedding ≅
        presentationLimitPreAdicSpace P S.plus S.isRingOfIntegralElements.isPowerBounded_of_mem
          hP),
      X.obj.ofRestrict _ ≫ f.hom =
        eU.hom ≫ presentationLimitPreAdicSpaceComap φ.toRingHom φ.continuous_toRingHom
          φ.map_mem_plus
          S.isRingOfIntegralElements.isPowerBounded_of_mem
          T.isRingOfIntegralElements.isPowerBounded_of_mem hP hP' hsheaf ≫ eV.inv ≫
            Y.obj.ofRestrict _ :=
  Iff.rfl

/-- An adic morphism sends analytic points to analytic points: on a chart it is the morphism
induced by an adic homomorphism, and the chart isomorphisms and inclusions identify analytic
points. -/
private theorem IsAdic.mapsTo_analyticPoints {f : X ⟶ Y} (hf : IsAdic f) :
    Set.MapsTo f.hom.base X.obj.analyticPoints Y.obj.analyticPoints := by
  intro x hx
  obtain ⟨U, hxU, V, -, A, _, _, _, _, S, P, hP, B, _, _, _, _, _, _, _, T, P', hP', φ, hφ,
    hsheaf, eU, eV, hfac⟩ := hf x
  have hx' : (⟨x, hxU⟩ : X.obj.restrict U.isOpenEmbedding) ∈
      (X.obj.restrict U.isOpenEmbedding).analyticPoints := by
    rw [analyticPoints_restrict]
    exact hx
  -- follow `x` around the chart square
  have h : Set.MapsTo (X.obj.ofRestrict U.isOpenEmbedding ≫ f.hom).base
      (X.obj.restrict U.isOpenEmbedding).analyticPoints Y.obj.analyticPoints := by
    rw [hfac]
    exact (mapsTo_analyticPoints_of_isOpenImmersion (Y.obj.ofRestrict V.isOpenEmbedding)).comp
      ((mapsTo_analyticPoints_of_isOpenImmersion eV.inv).comp
        ((hφ.mapsTo_analyticPoints_presentationLimitPreAdicSpaceComap P P'
          S.isRingOfIntegralElements.isPowerBounded_of_mem
          T.isRingOfIntegralElements.isPowerBounded_of_mem hP hP' hsheaf φ.map_mem_plus).comp
            (mapsTo_analyticPoints_of_isOpenImmersion eU.hom)))
  exact h hx'

/-- A morphism sending analytic points to analytic points is adic: over affinoid opens
`U ⊆ f⁻¹(V)` with complete models, its restriction is the morphism induced by its
global-sections map, which is adic by Wedhorn's Lemma 7.46. -/
private theorem isAdic_of_mapsTo_analyticPoints {f : X ⟶ Y}
    (hf : Set.MapsTo f.hom.base X.obj.analyticPoints Y.obj.analyticPoints) : IsAdic f := by
  intro x
  -- affinoid opens `V ∋ f x` and `x ∈ U ⊆ f⁻¹(V)`, with complete models
  obtain ⟨V, hV, hxV⟩ := Y.property.isLocallyAffinoid (f.hom.base x)
  obtain ⟨U, hU, hxU, hUV⟩ := Opens.isBasis_iff_nbhd.mp
    (isBasis_affinoidOpens X.property.isLocallyAffinoid) (U := (Opens.map f.hom.base).obj V)
    (x := x) hxV
  obtain ⟨B, _, _, _, _, _, _, _, T, P', hP', ⟨eU⟩⟩ := (isAffinoid_iff_exists_complete _).mp hU
  obtain ⟨A, _, _, _, _, _, _, _, S, P, hP, ⟨eV⟩⟩ := (isAffinoid_iff_exists_complete _).mp hV
  have hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa T.plus))
      (presentationLimitPresheaf P' T.plus) :=
    (isSheafy_presentationLimitPreAdicSpace_iff P' T.plus _ hP').mp
      (ObjectProperty.prop_of_iso isSheafy eU
        (isSheafy_restrict U.isOpenEmbedding X.property.isSheafy))
  -- the restriction `l : U → V` of `f`, and the morphism `g` of adic spectra it gives
  have hrange : Set.range (X.obj.ofRestrict U.isOpenEmbedding ≫ f.hom).base ⊆
      Set.range (Y.obj.ofRestrict V.isOpenEmbedding).base := by
    rintro _ ⟨⟨y, hy⟩, rfl⟩
    exact ⟨⟨f.hom.base y, hUV hy⟩, rfl⟩
  let l := IsOpenImmersion.lift (Y.obj.ofRestrict V.isOpenEmbedding)
    (X.obj.ofRestrict U.isOpenEmbedding ≫ f.hom) hrange
  have hl : l ≫ Y.obj.ofRestrict V.isOpenEmbedding = X.obj.ofRestrict U.isOpenEmbedding ≫ f.hom :=
    IsOpenImmersion.lift_fac _ _ _
  let g := eU.inv ≫ l ≫ eV.hom
  let φ := presentationLimitHomPairHom P P' S T hP hP' g
  have hg : presentationLimitPreAdicSpaceComap φ.toRingHom φ.continuous_toRingHom φ.map_mem_plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem
      T.isRingOfIntegralElements.isPowerBounded_of_mem hP hP' hsheaf = g :=
    presentationLimitPreAdicSpace_hom_ext _ _ _ _ _ _ _ _ hsheaf (by
      rw [presentationLimitHomRingHom_presentationLimitPreAdicSpaceComap,
        presentationLimitHomPairHom_toRingHom])
  -- `l` sends analytic points to analytic points, since `l` followed by the inclusion of `V` does
  have hlan : Set.MapsTo l.base (X.obj.restrict U.isOpenEmbedding).analyticPoints
      (Y.obj.restrict V.isOpenEmbedding).analyticPoints := by
    rw [← mapsTo_analyticPoints_comp_iff_of_isOpenImmersion l (Y.obj.ofRestrict V.isOpenEmbedding),
      hl]
    exact hf.comp (mapsTo_analyticPoints_of_isOpenImmersion _)
  have hgan : Set.MapsTo g.base _ _ :=
    (mapsTo_analyticPoints_of_isOpenImmersion eV.hom).comp
      (hlan.comp (mapsTo_analyticPoints_of_isOpenImmersion eU.inv))
  refine ⟨U, hxU, V, hUV, A, inferInstance, inferInstance, inferInstance, inferInstance, S, P, hP,
    B, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, T, P', hP', φ, ?_, hsheaf, eU, eV, ?_⟩
  · exact (mapsTo_analyticPoints_presentationLimitPreAdicSpaceComap_iff P _ hP P' _ hP' hsheaf
      _ _ _).mp (by rw [hg]; exact hgan)
  · -- cancel the chart isomorphisms; `l` followed by the inclusion of `V` is `f` on `U`
    rw [hg]
    simp [g, hl]

/-- **Adic morphisms are the morphisms preserving analytic points** (Huber 1994, Proposition
3.2(ii); Wedhorn, Proposition 8.39): a morphism of adic spaces is adic exactly when it sends
analytic points to analytic points. -/
theorem isAdic_iff_mapsTo_analyticPoints (f : X ⟶ Y) :
    IsAdic f ↔ Set.MapsTo f.hom.base X.obj.analyticPoints Y.obj.analyticPoints :=
  ⟨IsAdic.mapsTo_analyticPoints, isAdic_of_mapsTo_analyticPoints⟩

/-- **Identities are adic and composites of adic morphisms are adic.** -/
instance IsAdic.isMultiplicative : IsAdic.{u}.IsMultiplicative where
  id_mem _ := (isAdic_iff_mapsTo_analyticPoints _).mpr (Set.mapsTo_id _)
  comp_mem f g hf hg := (isAdic_iff_mapsTo_analyticPoints _).mpr
    (((isAdic_iff_mapsTo_analyticPoints g).mp hg).comp ((isAdic_iff_mapsTo_analyticPoints f).mp hf))

/-- **Open immersions are adic.** -/
theorem IsAdic.of_isOpenImmersion (f : X ⟶ Y) [PreAdicSpace.IsOpenImmersion f.hom] : IsAdic f :=
  (isAdic_iff_mapsTo_analyticPoints f).mpr (mapsTo_analyticPoints_of_isOpenImmersion f.hom)

/-- **Being adic is invariant under isomorphisms**: isomorphisms are open immersions, hence adic,
and adic morphisms are stable under composition. -/
instance IsAdic.respectsIso : IsAdic.{u}.RespectsIso :=
  MorphismProperty.respectsIso_of_isStableUnderComposition fun _ _ f (_ : IsIso f) ↦
    have : IsIso f.hom := (ObjectProperty.ι _).map_isIso f
    IsAdic.of_isOpenImmersion f

/-- **Cancellation**: if `f ≫ g` is adic, then so is `f`. A point over a non-analytic point is
non-analytic, so if `g (f x)` is analytic then so is `f x`. -/
theorem IsAdic.of_comp {f : X ⟶ Y} {g : Y ⟶ Z} (h : IsAdic (f ≫ g)) : IsAdic f :=
  (isAdic_iff_mapsTo_analyticPoints f).mpr fun _ hx ↦ preimage_analyticPoints_subset g.hom
    ((isAdic_iff_mapsTo_analyticPoints (f ≫ g)).mp h hx)

/-- **Every morphism into an analytic adic space is adic**: if every point of `Y` is analytic, for
instance if `Y` is the adic spectrum of a Tate ring such as `Spa(ℚ_p, ℤ_p)`
(`TauCeti.ValuationSpectrum.analyticPoints_presentationLimitPreAdicSpace_of_isTateRing`), then
every morphism `X ⟶ Y` is adic. -/
theorem IsAdic.of_analyticPoints_eq_univ (f : X ⟶ Y) (hY : Y.obj.analyticPoints = Set.univ) :
    IsAdic f :=
  (isAdic_iff_mapsTo_analyticPoints f).mpr fun _ _ ↦ hY ▸ Set.mem_univ _

/-- **Affinoid morphisms**: for a morphism of Huber pairs `φ : (A, A⁺) → (B, B⁺)` with `B`
complete and Hausdorff, between pairs whose adic spectra are adic spaces, the morphism
`Spa(B, B⁺) ⟶ Spa(A, A⁺)` induced by `φ` is adic exactly when the ring homomorphism of `φ` is
adic. -/
theorem isAdic_homMk_presentationLimitPreAdicSpaceComap_iff {A : Type u} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A] {B : Type u} [CommRing B]
    [UniformSpace B] [IsUniformAddGroup B] [IsTopologicalRing B] [CompleteSpace B] [T2Space B]
    [IsHuberRing B] {S : Pair A} {T : Pair B} (P : PairOfDefinition A) (P' : PairOfDefinition B)
    (hP : P.ringOfDefinition ≤ S.plus) (hP' : P'.ringOfDefinition ≤ T.plus)
    (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa T.plus))
      (presentationLimitPresheaf P' T.plus))
    (hA : PreAdicSpace.isAdic (presentationLimitPreAdicSpace P S.plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem hP)) (φ : Pair.Hom S T) :
    IsAdic (X := ⟨_, isAdic_presentationLimitPreAdicSpace P' T.plus
        T.isRingOfIntegralElements.isPowerBounded_of_mem hP' hsheaf⟩) (Y := ⟨_, hA⟩)
      (ObjectProperty.homMk (presentationLimitPreAdicSpaceComap φ.toRingHom
        φ.continuous_toRingHom φ.map_mem_plus S.isRingOfIntegralElements.isPowerBounded_of_mem
        T.isRingOfIntegralElements.isPowerBounded_of_mem hP hP' hsheaf)) ↔
      IsAdicHom φ.toRingHom :=
  (isAdic_iff_mapsTo_analyticPoints _).trans
    (mapsTo_analyticPoints_presentationLimitPreAdicSpaceComap_iff P _ hP P' _ hP' hsheaf _ _ _)

end AdicSpace

end TauCeti
