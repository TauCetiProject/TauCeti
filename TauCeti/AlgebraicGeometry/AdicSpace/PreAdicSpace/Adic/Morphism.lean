/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.Affinoid.Comap
public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.Affinoid.Complete
public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.Analytic
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.AdicHom

/-!
# Adic morphisms of adic spaces

A morphism `f : X ⟶ Y` of adic spaces is *adic* (Huber) when every point of `X` has an open
neighbourhood `U`, mapped by `f` into an open `V ⊆ Y`, such that `U ≅ Spa(B, B⁺)` and
`V ≅ Spa(A, A⁺)` for Huber pairs, `B` complete and Hausdorff, under which `f` restricted to
`U → V` is the morphism induced by a morphism of Huber pairs `(A, A⁺) → (B, B⁺)` whose ring
homomorphism is adic (`TauCeti.Huber.IsAdicHom`). For instance `Spa(ℤ_p⟦T⟧) → Spa(ℤ_p)` is not
adic, although `ℤ_p → ℤ_p⟦T⟧` is continuous.

The main theorem is Huber's characterisation (Wedhorn, Proposition 8.39): `f` is adic exactly when
it sends analytic points to analytic points (`isAdic_iff_mapsTo_analyticPoints`). Its affinoid core
is Wedhorn's Lemma 7.46: for a continuous homomorphism `φ` of Huber pairs with complete target,
`Spa(φ)` preserves analytic points exactly when `φ` is adic
(`TauCeti.ValuationSpectrum.mapsTo_analyticPoints_presentationLimitPreAdicSpaceComap_iff`). For
the converse direction, a point `x` has an affinoid neighbourhood mapped into an affinoid
neighbourhood of `f x`; both have complete models, and between complete affinoids every morphism
is induced by its map of global sections
(`TauCeti.ValuationSpectrum.presentationLimitPreAdicSpaceComap_presentationLimitHomRingHom`).

The characterisation makes the formal properties immediate: adic morphisms contain the identities
and the open immersions and are stable under composition, if `f ≫ g` is adic then so is `f`, and
every morphism into an adic space all of whose points are analytic is adic.

## Main definitions

* `TauCeti.AdicSpace.IsAdic`: adic morphisms of adic spaces.

## Main results

* `TauCeti.ValuationSpectrum.mapsTo_analyticPoints_presentationLimitPreAdicSpaceComap_iff`: over a
  complete target, `Spa(φ)` preserves analytic points exactly when `φ` is adic.
* `TauCeti.AdicSpace.isAdic_iff_mapsTo_analyticPoints`: a morphism of adic spaces is adic exactly
  when it sends analytic points to analytic points.
* `TauCeti.AdicSpace.IsAdic.comp`, `TauCeti.AdicSpace.isAdic_id`,
  `TauCeti.AdicSpace.IsAdic.of_comp`, `TauCeti.AdicSpace.isAdic_of_isOpenImmersion` and
  `TauCeti.AdicSpace.isAdic_of_analyticPoints_eq_univ`: the formal properties of adic morphisms.

## References

* R. Huber, *A generalization of formal schemes and rigid analytic varieties*, Math. Z. 217
  (1994), §3, the definition of adic morphisms and Proposition 3.2.
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

section Comap

variable {A B : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [CommRing B]
  [TopologicalSpace B] [IsTopologicalRing B] {P : PairOfDefinition A} {Aplus : Subring A}
  {P' : PairOfDefinition B} {Bplus : Subring B}

/-- **Wedhorn Lemma 7.46(1) on adic spectra.** If `φ : A → B` is adic and carries `A⁺` into
`B⁺`, then the morphism `Spa(B, B⁺) ⟶ Spa(A, A⁺)` it induces sends analytic points to analytic
points. -/
theorem mapsTo_analyticPoints_presentationLimitPreAdicSpaceComap {φ : A →+* B}
    (hφ : IsAdicHom φ) (hplus : ∀ a ∈ Aplus, φ a ∈ Bplus)
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) (hBplus : ∀ ⦃b⦄, b ∈ Bplus → IsPowerBounded b)
    (hP : P.ringOfDefinition ≤ Aplus) (hP' : P'.ringOfDefinition ≤ Bplus)
    (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa Bplus))
      (presentationLimitPresheaf P' Bplus)) :
    Set.MapsTo
      (presentationLimitPreAdicSpaceComap φ hφ.continuous hplus hAplus hBplus hP hP' hsheaf).base
      (presentationLimitPreAdicSpace P' Bplus hBplus hP').analyticPoints
      (presentationLimitPreAdicSpace P Aplus hAplus hP).analyticPoints := by
  intro x hx
  rw [analyticPoints_presentationLimitPreAdicSpace] at hx ⊢
  have h := hφ.mapsTo_spaAnalytic hplus hx
  rwa [← presentationLimitPreAdicSpaceComap_base_apply_coe φ hφ.continuous hplus hAplus hBplus hP
    hP' hsheaf x] at h

/-- **Wedhorn Lemma 7.46 on adic spectra.** Let `φ : A → B` be a continuous homomorphism of Huber
rings carrying `A⁺` into `B⁺`, with `B` complete. The morphism `Spa(B, B⁺) ⟶ Spa(A, A⁺)` induced
by `φ` sends analytic points to analytic points exactly when `φ` is adic. -/
theorem mapsTo_analyticPoints_presentationLimitPreAdicSpaceComap_iff [IsHuberRing A]
    {B : Type u} [CommRing B] [UniformSpace B] [IsUniformAddGroup B] [IsTopologicalRing B]
    [CompleteSpace B] [T2Space B] [IsHuberRing B] {P' : PairOfDefinition B} {Bplus : Subring B}
    {φ : A →+* B} (hφ : Continuous φ) (hplus : ∀ a ∈ Aplus, φ a ∈ Bplus)
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) (hBplus : ∀ ⦃b⦄, b ∈ Bplus → IsPowerBounded b)
    (hP : P.ringOfDefinition ≤ Aplus) (hP' : P'.ringOfDefinition ≤ Bplus)
    (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa Bplus))
      (presentationLimitPresheaf P' Bplus)) :
    Set.MapsTo (presentationLimitPreAdicSpaceComap φ hφ hplus hAplus hBplus hP hP' hsheaf).base
        (presentationLimitPreAdicSpace P' Bplus hBplus hP').analyticPoints
        (presentationLimitPreAdicSpace P Aplus hAplus hP).analyticPoints ↔
      IsAdicHom φ := by
  refine ⟨fun h ↦ isAdicHom_of_mapsTo_spaAnalytic hφ (Aplus := Aplus)
    (fun _ hb ↦ mem_powerBoundedSubring.mpr (hBplus hb)) fun v hv ↦ ?_,
    fun h ↦ mapsTo_analyticPoints_presentationLimitPreAdicSpaceComap h hplus hAplus hBplus hP hP'
      hsheaf⟩
  -- read the analytic valuation `v` as a point of `Spa(B, B⁺)`
  let x : presentationLimitPreAdicSpace P' Bplus hBplus hP' :=
    ⟨v, ((mem_spaAnalytic_iff _ _).mp hv).1⟩
  have hx : x ∈ (presentationLimitPreAdicSpace P' Bplus hBplus hP').analyticPoints := by
    rwa [analyticPoints_presentationLimitPreAdicSpace]
  have hfx := h hx
  rw [analyticPoints_presentationLimitPreAdicSpace] at hfx
  rw [← presentationLimitPreAdicSpaceComap_base_apply_coe φ hφ hplus hAplus hBplus hP hP' hsheaf x]
  exact hfx

end Comap

end ValuationSpectrum

namespace AdicSpace

open PreAdicSpace ValuationSpectrum

variable {X Y Z : AdicSpace.{u}}

/-- **Adic morphisms** (Huber 1994, §3): a morphism `f : X ⟶ Y` of adic spaces is *adic* when
every point `x` of `X` has an open neighbourhood `U`, mapped by `f` into an open `V` of `Y`,
together with Huber pairs `(A, A⁺)` and `(B, B⁺)`, `B` complete and Hausdorff with `Spa(B, B⁺)`
having a sheaf as structure presheaf, a morphism `φ : (A, A⁺) → (B, B⁺)` whose ring homomorphism
is adic, and isomorphisms identifying `X` restricted to `U` with `Spa(B, B⁺)` and `Y` restricted to
`V` with `Spa(A, A⁺)`, under which `f` becomes the morphism induced by `φ`.

Equivalently, `f` sends analytic points to analytic points (`isAdic_iff_mapsTo_analyticPoints`).
The name `IsAdic` is that of a morphism property; the object property of being an adic space is
`TauCeti.PreAdicSpace.isAdic`. -/
def IsAdic (f : X ⟶ Y) : Prop :=
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
        φ.map_mem_plus S.isRingOfIntegralElements.isPowerBounded_of_mem
        T.isRingOfIntegralElements.isPowerBounded_of_mem hP hP' hsheaf ≫ eV.inv ≫
          Y.obj.ofRestrict _

/-- Unfolding lemma for `TauCeti.AdicSpace.IsAdic`. -/
theorem isAdic_def (f : X ⟶ Y) : IsAdic f ↔
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
          φ.map_mem_plus S.isRingOfIntegralElements.isPowerBounded_of_mem
          T.isRingOfIntegralElements.isPowerBounded_of_mem hP hP' hsheaf ≫ eV.inv ≫
            Y.obj.ofRestrict _ :=
  Iff.rfl

/-- **An adic morphism sends analytic points to analytic points** (Wedhorn, Proposition 8.39):
near every point it is the morphism of adic spectra induced by an adic homomorphism, which
preserves analytic points by Wedhorn's Lemma 7.46(1). -/
theorem IsAdic.mapsTo_analyticPoints {f : X ⟶ Y} (hf : IsAdic f) :
    Set.MapsTo f.hom.base X.obj.analyticPoints Y.obj.analyticPoints := by
  intro x hx
  obtain ⟨U, hxU, V, -, A, _, _, _, _, S, P, hP, B, _, _, _, _, _, _, _, T, P', hP', φ, hφ,
    hsheaf, eU, eV, hfac⟩ := hf x
  -- the restriction of `f` to `U` is a composite of maps preserving analytic points
  have h : Set.MapsTo (X.obj.ofRestrict U.isOpenEmbedding ≫ f.hom).base
      (X.obj.restrict U.isOpenEmbedding).analyticPoints Y.obj.analyticPoints := by
    rw [hfac, comp_base, comp_base, comp_base, TopCat.coe_comp, TopCat.coe_comp, TopCat.coe_comp]
    exact (mapsTo_analyticPoints_of_isOpenImmersion _).comp <|
      (mapsTo_analyticPoints_of_isOpenImmersion _).comp <|
        (mapsTo_analyticPoints_presentationLimitPreAdicSpaceComap hφ _ _ _ _ _ hsheaf).comp
          (mapsTo_analyticPoints_of_isOpenImmersion _)
  exact h (x := ⟨x, hxU⟩) (by rwa [analyticPoints_restrict])

/-- **A morphism of adic spaces preserving analytic points is adic** (Wedhorn, Proposition 8.39).
A point `x` has an affinoid neighbourhood `U` mapped into an affinoid neighbourhood `V` of `f x`.
On complete models `Spa(B, B⁺)` of `U` and `Spa(A, A⁺)` of `V`, the restriction of `f` is induced
by its map of global sections `φ : A → B`, which is adic by Wedhorn's Lemma 7.46(2). -/
theorem isAdic_of_mapsTo_analyticPoints (f : X ⟶ Y)
    (hf : Set.MapsTo f.hom.base X.obj.analyticPoints Y.obj.analyticPoints) : IsAdic f := by
  intro x
  obtain ⟨V, hV, hxV⟩ := Y.property.isLocallyAffinoid (f.hom.base x)
  obtain ⟨U, hU, hxU, hUV⟩ := Opens.isBasis_iff_nbhd.mp
    (isBasis_affinoidOpens X.property.isLocallyAffinoid)
    (show x ∈ (Opens.map f.hom.base).obj V from hxV)
  obtain ⟨B, _, _, _, _, _, _, _, T, P', hP', ⟨eU⟩⟩ := (isAffinoid_iff_exists_complete _).mp hU
  obtain ⟨A, _, _, _, _, _, _, _, S, P, hP, ⟨eV⟩⟩ := (isAffinoid_iff_exists_complete _).mp hV
  have hsheaf := (isSheafy_presentationLimitPreAdicSpace_iff P' T.plus _ hP').mp
    (ObjectProperty.prop_of_iso isSheafy eU
      (isSheafy_restrict U.isOpenEmbedding X.property.isSheafy))
  -- the restriction of `f` to `U → V`, read on the complete models
  let fUV := PreAdicSpace.IsOpenImmersion.lift (Y.obj.ofRestrict V.isOpenEmbedding)
    (X.obj.ofRestrict U.isOpenEmbedding ≫ f.hom) (by
      rintro _ ⟨y, rfl⟩
      exact ⟨⟨f.hom.base y.1, hUV y.2⟩, rfl⟩)
  have hfUV : fUV ≫ Y.obj.ofRestrict V.isOpenEmbedding =
      X.obj.ofRestrict U.isOpenEmbedding ≫ f.hom :=
    PreAdicSpace.IsOpenImmersion.lift_fac _ _ _
  let g := eU.inv ≫ fUV ≫ eV.hom
  -- between complete affinoids, `g` is induced by its map of global sections
  let φ := presentationLimitHomPairHom P P' S T hP hP' g
  have hg : presentationLimitPreAdicSpaceComap φ.toRingHom φ.continuous_toRingHom φ.map_mem_plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem
      T.isRingOfIntegralElements.isPowerBounded_of_mem hP hP' hsheaf = g := by
    have key : ∀ (ψ : A →+* B) (hψ : Continuous ψ) (hplus : ∀ a ∈ S.plus, ψ a ∈ T.plus),
        ψ = presentationLimitHomRingHom P S.plus _ hP P' T.plus _ hP' g →
        presentationLimitPreAdicSpaceComap ψ hψ hplus
          S.isRingOfIntegralElements.isPowerBounded_of_mem
          T.isRingOfIntegralElements.isPowerBounded_of_mem hP hP' hsheaf = g := by
      rintro _ _ hplus rfl
      exact presentationLimitPreAdicSpaceComap_presentationLimitHomRingHom P S.plus _ hP P' T.plus
        _ hP' hsheaf g hplus
    exact key _ _ _ (presentationLimitHomPairHom_toRingHom P P' S T hP hP' g)
  refine ⟨U, hxU, V, hUV, A, inferInstance, inferInstance, inferInstance, inferInstance, S, P, hP,
    B, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, T, P', hP', φ, ?_, hsheaf, eU, eV, ?_⟩
  · rw [← mapsTo_analyticPoints_presentationLimitPreAdicSpaceComap_iff φ.continuous_toRingHom
      φ.map_mem_plus S.isRingOfIntegralElements.isPowerBounded_of_mem
      T.isRingOfIntegralElements.isPowerBounded_of_mem hP hP' hsheaf, hg]
    -- `fUV` preserves analytic points because `f` does
    have h : Set.MapsTo fUV.base (X.obj.restrict U.isOpenEmbedding).analyticPoints
        (Y.obj.restrict V.isOpenEmbedding).analyticPoints := by
      intro y hy
      rw [← preimage_analyticPoints_of_isOpenImmersion (Y.obj.ofRestrict V.isOpenEmbedding),
        Set.mem_preimage, ← TopCat.comp_app, ← comp_base, hfUV]
      exact hf (mapsTo_analyticPoints_of_isOpenImmersion _ hy)
    rw [comp_base, comp_base, TopCat.coe_comp, TopCat.coe_comp]
    exact (mapsTo_analyticPoints_of_isOpenImmersion _).comp
      (h.comp (mapsTo_analyticPoints_of_isOpenImmersion _))
  · simp only [hg, g, Category.assoc, Iso.hom_inv_id_assoc, hfUV]

/-- **Huber's characterisation of adic morphisms** (Wedhorn, Proposition 8.39): a morphism of adic
spaces is adic exactly when it sends analytic points to analytic points. -/
theorem isAdic_iff_mapsTo_analyticPoints (f : X ⟶ Y) :
    IsAdic f ↔ Set.MapsTo f.hom.base X.obj.analyticPoints Y.obj.analyticPoints :=
  ⟨IsAdic.mapsTo_analyticPoints, isAdic_of_mapsTo_analyticPoints f⟩

/-- An open immersion of adic spaces is adic. -/
theorem isAdic_of_isOpenImmersion (f : X ⟶ Y) [PreAdicSpace.IsOpenImmersion f.hom] :
    IsAdic f :=
  isAdic_of_mapsTo_analyticPoints f (mapsTo_analyticPoints_of_isOpenImmersion f.hom)

/-- The identity of an adic space is adic. -/
theorem isAdic_id (X : AdicSpace.{u}) : IsAdic (𝟙 X) :=
  isAdic_of_isOpenImmersion _

/-- A composite of adic morphisms is adic. -/
theorem IsAdic.comp {f : X ⟶ Y} {g : Y ⟶ Z} (hf : IsAdic f) (hg : IsAdic g) : IsAdic (f ≫ g) :=
  isAdic_of_mapsTo_analyticPoints _ (hg.mapsTo_analyticPoints.comp hf.mapsTo_analyticPoints)

/-- **Cancellation for adic morphisms**: if `f ≫ g` is adic, then so is `f`. A point of `X` over
a non-analytic point of `Y` would lie over a non-analytic point of `Z`, since every morphism pulls
analytic points back to analytic points. -/
theorem IsAdic.of_comp {f : X ⟶ Y} {g : Y ⟶ Z} (hfg : IsAdic (f ≫ g)) : IsAdic f :=
  isAdic_of_mapsTo_analyticPoints _ fun _ hx ↦
    preimage_analyticPoints_subset g.hom (hfg.mapsTo_analyticPoints hx)

/-- Every morphism into an adic space all of whose points are analytic is adic. -/
theorem isAdic_of_analyticPoints_eq_univ (f : X ⟶ Y) (hY : Y.obj.analyticPoints = Set.univ) :
    IsAdic f :=
  isAdic_of_mapsTo_analyticPoints f fun _ _ ↦ hY ▸ Set.mem_univ _

/-- Adic morphisms contain the identities and are stable under composition. -/
instance isAdic_isMultiplicative : MorphismProperty.IsMultiplicative (@IsAdic.{u}) where
  id_mem := isAdic_id
  comp_mem _ _ hf hg := hf.comp hg

/-- Being adic is invariant under isomorphisms of the source and of the target: isomorphisms are
open immersions, hence adic. -/
instance isAdic_respectsIso : MorphismProperty.RespectsIso (@IsAdic.{u}) :=
  MorphismProperty.RespectsIso.mk _ (fun e _ hf ↦ (isAdic_of_isOpenImmersion e.hom).comp hf)
    fun e _ hf ↦ hf.comp (isAdic_of_isOpenImmersion e.hom)

end AdicSpace

end TauCeti
