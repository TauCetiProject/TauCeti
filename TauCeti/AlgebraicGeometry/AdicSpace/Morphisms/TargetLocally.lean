/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.Adic
public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.Comap

/-!
# Morphisms of adic spaces locally on the target induced by morphisms of Huber pairs

Given a property `Q` of morphisms of complete Hausdorff Huber pairs, a morphism `f : X ⟶ Y` of
adic spaces is *target-locally `Q`* when every point of `Y` has an open neighbourhood `V` such that
`V ≅ Spa(A, A⁺)` and `f⁻¹(V) ≅ Spa(B, B⁺)`, under which `f` restricted to `f⁻¹(V) → V` is the
morphism induced by a morphism of Huber pairs `(A, A⁺) → (B, B⁺)` satisfying `Q`. This is the shape
of Huber's finite morphisms (Huber 1996, (1.4.4); `TauCeti.AdicSpace.IsFinite`) and of
Kedlaya–Liu's finite étale morphisms (Kedlaya–Liu, Definition 8.2.16;
`TauCeti.AdicSpace.IsFiniteEtale`). Conditions on the target pair, such as being Tate, are part of
`Q`.

Unlike the chart-local conditions (`TauCeti.PreAdicSpace.chartLocally`), which are local on the
source, here the whole preimage of `V` is required to be affinoid. Such a condition is local on the
target: it descends along open covers of the target.

## Main definitions

* `TauCeti.AdicSpace.targetLocally`: the morphisms of adic spaces that are, locally on the target,
  induced by morphisms of Huber pairs satisfying a given property.

## Main results

* `TauCeti.AdicSpace.targetLocally_mono`: a weaker property of morphisms of Huber pairs gives a
  weaker target-local property, with the same neighbourhoods.
* `TauCeti.AdicSpace.targetLocally_of_iSup_eq_top`: every target-local property descends along
  open covers of the target.
* `TauCeti.AdicSpace.targetLocally_presentationLimitPreAdicSpaceComap`: the morphism
  `Spa(B, B⁺) ⟶ Spa(A, A⁺)` induced by a morphism of Huber pairs satisfying `Q` is
  target-locally `Q`.
* `TauCeti.AdicSpace.targetLocally_respectsIso`: every target-local property is invariant under
  isomorphisms of the source and of the target.
* `TauCeti.AdicSpace.targetLocally_id`: the identity of an adic space covered by open affinoids
  `Spa(A, A⁺)` for which `Q` holds for the identity of `(A, A⁺)` is target-locally `Q`.

## Implementation notes

The descent along open covers and the isomorphism-invariance proofs are adapted from those of the
target-local predicate `TauCeti.PreAdicSpace.IsClosedImmersion`
(`PreAdicSpace/ClosedImmersion/Basic.lean`, including `IsClosedImmersion.respectsIso`, and
`PreAdicSpace/ClosedImmersion/Local.lean`, including `IsClosedImmersion.of_iSup_eq_top`).

## References

* R. Huber, *Étale cohomology of rigid analytic varieties and adic spaces*, Aspects of
  Mathematics E30 (1996), §1.4, (1.4.4).
* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: foundations*, Astérisque 371 (2015),
  §8.2, Definition 8.2.16.
-/

public section

open CategoryTheory TopologicalSpace Topology

namespace TauCeti

open Huber

universe u

namespace AdicSpace

open PreAdicSpace ValuationSpectrum

/-- A morphism `f : X ⟶ Y` of adic spaces is *target-locally `Q`*, for a property `Q` of morphisms
of complete Hausdorff Huber pairs, when every point `y` of `Y` has an open neighbourhood `V`
together with complete Hausdorff Huber pairs `(A, A⁺)` and `(B, B⁺)`, `Spa(B, B⁺)` having a sheaf
as structure presheaf, a morphism `φ : (A, A⁺) → (B, B⁺)` satisfying `Q`, and isomorphisms
identifying `Y` restricted to `V` with `Spa(A, A⁺)` and `X` restricted to `f⁻¹(V)` with
`Spa(B, B⁺)`, under which `f` becomes the morphism induced by `φ`. -/
def targetLocally
    (Q : ∀ {A : Type u} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
      [CompleteSpace A] [T2Space A] [IsHuberRing A] {B : Type u} [CommRing B] [UniformSpace B]
      [IsUniformAddGroup B] [IsTopologicalRing B] [CompleteSpace B] [T2Space B] [IsHuberRing B]
      {S : Pair A} {T : Pair B}, Pair.Hom S T → Prop)
    {X Y : AdicSpace.{u}} (f : X ⟶ Y) : Prop :=
  ∀ y : Y.obj, ∃ (V : Opens Y.obj) (_ : y ∈ V) (A : Type u) (_ : CommRing A)
    (_ : UniformSpace A) (_ : IsUniformAddGroup A) (_ : IsTopologicalRing A) (_ : CompleteSpace A)
    (_ : T2Space A) (_ : IsHuberRing A) (S : Pair A) (P : PairOfDefinition A)
    (hP : P.ringOfDefinition ≤ S.plus)
    (B : Type u) (_ : CommRing B) (_ : UniformSpace B) (_ : IsUniformAddGroup B)
    (_ : IsTopologicalRing B) (_ : CompleteSpace B) (_ : T2Space B) (_ : IsHuberRing B)
    (T : Pair B) (P' : PairOfDefinition B) (hP' : P'.ringOfDefinition ≤ T.plus)
    (φ : Pair.Hom S T) (_ : Q φ)
    (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa T.plus))
      (presentationLimitPresheaf P' T.plus))
    (eV : Y.obj.restrict V.isOpenEmbedding ≅
      presentationLimitPreAdicSpace P S.plus S.isRingOfIntegralElements.isPowerBounded_of_mem hP)
    (eU : X.obj.restrict ((Opens.map f.hom.base).obj V).isOpenEmbedding ≅
      presentationLimitPreAdicSpace P' T.plus T.isRingOfIntegralElements.isPowerBounded_of_mem
        hP'),
    X.obj.ofRestrict _ ≫ f.hom =
      eU.hom ≫ presentationLimitPreAdicSpaceComap φ.toRingHom φ.continuous_toRingHom
        φ.map_mem_plus S.isRingOfIntegralElements.isPowerBounded_of_mem
        T.isRingOfIntegralElements.isPowerBounded_of_mem hP hP' hsheaf ≫ eV.inv ≫
        Y.obj.ofRestrict _

section

variable {Q Q' : ∀ {A : Type u} [CommRing A] [UniformSpace A] [IsUniformAddGroup A]
  [IsTopologicalRing A] [CompleteSpace A] [T2Space A] [IsHuberRing A] {B : Type u} [CommRing B]
  [UniformSpace B] [IsUniformAddGroup B] [IsTopologicalRing B] [CompleteSpace B] [T2Space B]
  [IsHuberRing B] {S : Pair A} {T : Pair B}, Pair.Hom S T → Prop}
  {X Y : AdicSpace.{u}}

/-- Unfolding lemma for `TauCeti.AdicSpace.targetLocally`. -/
theorem targetLocally_iff (f : X ⟶ Y) : targetLocally Q f ↔
    ∀ y : Y.obj, ∃ (V : Opens Y.obj) (_ : y ∈ V) (A : Type u) (_ : CommRing A)
      (_ : UniformSpace A) (_ : IsUniformAddGroup A) (_ : IsTopologicalRing A)
      (_ : CompleteSpace A) (_ : T2Space A) (_ : IsHuberRing A) (S : Pair A)
      (P : PairOfDefinition A) (hP : P.ringOfDefinition ≤ S.plus)
      (B : Type u) (_ : CommRing B) (_ : UniformSpace B) (_ : IsUniformAddGroup B)
      (_ : IsTopologicalRing B) (_ : CompleteSpace B) (_ : T2Space B) (_ : IsHuberRing B)
      (T : Pair B) (P' : PairOfDefinition B) (hP' : P'.ringOfDefinition ≤ T.plus)
      (φ : Pair.Hom S T) (_ : Q φ)
      (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa T.plus))
        (presentationLimitPresheaf P' T.plus))
      (eV : Y.obj.restrict V.isOpenEmbedding ≅
        presentationLimitPreAdicSpace P S.plus S.isRingOfIntegralElements.isPowerBounded_of_mem
          hP)
      (eU : X.obj.restrict ((Opens.map f.hom.base).obj V).isOpenEmbedding ≅
        presentationLimitPreAdicSpace P' T.plus T.isRingOfIntegralElements.isPowerBounded_of_mem
          hP'),
      X.obj.ofRestrict _ ≫ f.hom =
        eU.hom ≫ presentationLimitPreAdicSpaceComap φ.toRingHom φ.continuous_toRingHom
          φ.map_mem_plus S.isRingOfIntegralElements.isPowerBounded_of_mem
          T.isRingOfIntegralElements.isPowerBounded_of_mem hP hP' hsheaf ≫ eV.inv ≫
          Y.obj.ofRestrict _ :=
  Iff.rfl

/-- **Monotonicity**: if every morphism of Huber pairs satisfying `Q` satisfies `Q'`, then every
target-locally `Q` morphism is target-locally `Q'`, with the same neighbourhoods. -/
theorem targetLocally_mono
    (h : ∀ {A : Type u} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
      [CompleteSpace A] [T2Space A] [IsHuberRing A] {B : Type u} [CommRing B] [UniformSpace B]
      [IsUniformAddGroup B] [IsTopologicalRing B] [CompleteSpace B] [T2Space B] [IsHuberRing B]
      {S : Pair A} {T : Pair B} (φ : Pair.Hom S T), Q φ → Q' φ)
    {f : X ⟶ Y} (hf : targetLocally Q f) : targetLocally Q' f := fun y ↦ by
  obtain ⟨V, hy, A, _, _, _, _, _, _, _, S, P, hP, B, _, _, _, _, _, _, _, T, P', hP', φ, hφ,
    hsheaf, eV, eU, hfac⟩ := hf y
  exact ⟨V, hy, A, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, S, P, hP, B, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, T, P', hP', φ, h φ hφ, hsheaf, eV,
    eU, hfac⟩

/-! ### Descent along open covers of the target -/

/-- **Target-local properties descend along open covers of the target**: if `Y` is covered by
opens `V i` over which the restrictions `f⁻¹(V i) → V i` of `f` are target-locally `Q`, then `f` is
target-locally `Q`. A neighbourhood supplied by a restriction is an open of `V i`, hence an open of
`Y`, with the same preimage in `X`. -/
theorem targetLocally_of_iSup_eq_top {f : X ⟶ Y} {ι : Type*} (V : ι → Opens Y.obj)
    (hV : iSup V = ⊤)
    (hf : ∀ i, targetLocally Q
      (X := ⟨_, isAdic_restrict ((Opens.map f.hom.base).obj (V i)).isOpenEmbedding X.property⟩)
      (Y := ⟨_, isAdic_restrict (V i).isOpenEmbedding Y.property⟩)
      (ObjectProperty.homMk (f.hom.restrictPreimage (V i)))) :
    targetLocally Q f := by
  intro y
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hV.symm ▸ Set.mem_univ y : y ∈ iSup V)
  obtain ⟨W, hy, A, _, _, _, _, _, _, _, S, P, hP, B, _, _, _, _, _, _, _, T, P', hP', φ, hφ,
    hsheaf, eW, eU, hfac⟩ := hf i ⟨y, hi⟩
  let V' : Opens Y.obj := (V i).isOpenEmbedding.isOpenMap.functor.obj W
  let U := (Opens.map f.hom.base).obj (V i)
  let U' := (Opens.map (f.hom.restrictPreimage (V i)).base).obj W
  -- both open subspaces of `X` have precisely the points mapping into the image of `W`
  have hr : Set.range ((X.obj.restrict U.isOpenEmbedding).ofRestrict U'.isOpenEmbedding ≫
      X.obj.ofRestrict U.isOpenEmbedding).base =
      Set.range (X.obj.ofRestrict ((Opens.map f.hom.base).obj V').isOpenEmbedding).base := by
    have h := range_restrictPreimage_comp_eq_preimage_range (eV := Iso.refl _)
      (eU := Iso.refl _) (q := f.hom.restrictPreimage (V i)) (by simp) W
    simp only [Iso.refl_inv, Category.id_comp, IsOpenImmersion.range_ofRestrict_comp_base] at h ⊢
    rw [h]
    ext x
    constructor
    · rintro ⟨z, hz⟩
      exact ⟨⟨x, show f.hom.base x ∈ V' from hz ▸ z.property⟩, rfl⟩
    · rintro ⟨z, rfl⟩
      exact ⟨⟨_, z.property⟩, rfl⟩
  let e := IsOpenImmersion.isoOfRangeEq
    ((X.obj.restrict U.isOpenEmbedding).ofRestrict U'.isOpenEmbedding ≫
      X.obj.ofRestrict U.isOpenEmbedding)
    (X.obj.ofRestrict ((Opens.map f.hom.base).obj V').isOpenEmbedding) hr
  refine ⟨V', ⟨⟨y, hi⟩, hy, rfl⟩, A, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, S, P, hP, B, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, T, P', hP', φ, hφ,
    hsheaf, (PreAdicSpace.restrictRestrictIso Y.obj (V i).isOpenEmbedding W).symm ≪≫ eW,
    e.symm ≪≫ eU, ?_⟩
  -- transport the local square through the two identifications of open subspaces, composing the
  -- identities as terms: rewriting inside the restricted objects would require identifying the
  -- topology of a restriction with its underlying subtype topology
  have hsource := congrArg (fun g ↦ g ≫ f.hom)
    (IsOpenImmersion.isoOfRangeEq_inv_comp _ _ hr)
  have hsquare := congrArg (fun g ↦ g ≫ Y.obj.ofRestrict (V i).isOpenEmbedding) hfac
  have htarget := congrArg
    (fun g ↦ eU.hom ≫ presentationLimitPreAdicSpaceComap φ.toRingHom φ.continuous_toRingHom
      φ.map_mem_plus S.isRingOfIntegralElements.isPowerBounded_of_mem
      T.isRingOfIntegralElements.isPowerBounded_of_mem hP hP' hsheaf ≫ eW.inv ≫ g)
    (PreAdicSpace.restrictRestrictIso_hom_ofRestrict Y.obj (V i).isOpenEmbedding W)
  simp only [Category.assoc] at hsource htarget
  simp only [Category.assoc, ObjectProperty.homMk_hom, Hom.restrictPreimage_ofRestrict] at hsquare
  simpa only [Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Iso.symm_inv, Category.assoc] using
    hsource.symm.trans (congrArg (fun g ↦ e.inv ≫ g) (hsquare.trans htarget.symm))

/-! ### Affinoid morphisms, isomorphisms and identities -/

/-- **Affinoid morphisms**: for a morphism of Huber pairs `φ : (A, A⁺) → (B, B⁺)` satisfying `Q`,
between complete Hausdorff pairs whose adic spectra are adic spaces, the morphism
`Spa(B, B⁺) ⟶ Spa(A, A⁺)` induced by `φ` is target-locally `Q`, witnessed over the whole of
`Spa(A, A⁺)`. -/
theorem targetLocally_presentationLimitPreAdicSpaceComap {A : Type u} [CommRing A]
    [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A] [CompleteSpace A] [T2Space A]
    [IsHuberRing A] {B : Type u} [CommRing B] [UniformSpace B] [IsUniformAddGroup B]
    [IsTopologicalRing B] [CompleteSpace B] [T2Space B] [IsHuberRing B] {S : Pair A} {T : Pair B}
    (P : PairOfDefinition A) (P' : PairOfDefinition B) (hP : P.ringOfDefinition ≤ S.plus)
    (hP' : P'.ringOfDefinition ≤ T.plus)
    (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa T.plus))
      (presentationLimitPresheaf P' T.plus))
    (hA : PreAdicSpace.isAdic (presentationLimitPreAdicSpace P S.plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem hP)) (φ : Pair.Hom S T) (hφ : Q φ) :
    targetLocally Q (X := ⟨_, isAdic_presentationLimitPreAdicSpace P' T.plus
        T.isRingOfIntegralElements.isPowerBounded_of_mem hP' hsheaf⟩) (Y := ⟨_, hA⟩)
      (ObjectProperty.homMk (presentationLimitPreAdicSpaceComap φ.toRingHom
        φ.continuous_toRingHom φ.map_mem_plus S.isRingOfIntegralElements.isPowerBounded_of_mem
        T.isRingOfIntegralElements.isPowerBounded_of_mem hP hP' hsheaf)) := by
  refine fun _ ↦ ⟨⊤, trivial, A, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, S, P, hP, B, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, T, P', hP', φ, hφ,
    hsheaf, PreAdicSpace.restrictTopIso _,
    restrictIsoOfRangeEq _ _ (Opens.isOpenEmbedding ⊤) ?_ ≪≫ PreAdicSpace.restrictTopIso _, ?_⟩
  · rw [Opens.map_top]
  · simp only [Iso.trans_hom, Category.assoc, restrictIsoOfRangeEq_hom_ofRestrict_assoc,
      PreAdicSpace.restrictTopIso_hom, ObjectProperty.homMk_hom]
    simp [← PreAdicSpace.restrictTopIso_hom]

/-- Precomposing a target-locally `Q` morphism with an isomorphism gives a target-locally `Q`
morphism: over the same neighbourhoods, `e` identifies the restrictions of the two sources. -/
private theorem targetLocally_iso_hom_comp {X' : AdicSpace.{u}} (e : X' ≅ X) {f : X ⟶ Y}
    (hf : targetLocally Q f) : targetLocally Q (e.hom ≫ f) := by
  intro y
  obtain ⟨V, hy, A, _, _, _, _, _, _, _, S, P, hP, B, _, _, _, _, _, _, _, T, P', hP', φ, hφ,
    hsheaf, eV, eU, hfac⟩ := hf y
  let e' : X'.obj ≅ X.obj := (ObjectProperty.ι _).mapIso e
  -- `e⁻¹((e.hom ≫ f)⁻¹(V)) = f⁻¹(V)`
  have key := Opens.map_inv_obj_map_hom_obj (forgetToTop.mapIso e') ((Opens.map f.hom.base).obj V)
  simp only [Functor.mapIso_hom, Functor.mapIso_inv, forgetToTop_map] at key
  have hr : Set.range
      ((Opens.map e'.inv.base).obj ((Opens.map (e.hom ≫ f).hom.base).obj V)).inclusion' =
        Set.range ((Opens.map f.hom.base).obj V).inclusion' := by
    rw [Opens.set_range_inclusion', Opens.set_range_inclusion']
    exact congrArg SetLike.coe key
  refine ⟨V, hy, A, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, S, P, hP, B, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, T, P', hP', φ, hφ, hsheaf, eV,
    restrictIso e' _ ≪≫
      restrictIsoOfRangeEq _ (Opens.isOpenEmbedding _) (Opens.isOpenEmbedding _) hr ≪≫ eU, ?_⟩
  simp only [Iso.trans_hom, Category.assoc, ← hfac, restrictIsoOfRangeEq_hom_ofRestrict_assoc,
    restrictIso_hom_ofRestrict_assoc]
  simp [e']

/-- Postcomposing a target-locally `Q` morphism with an isomorphism `e : Y ≅ Y'` gives a
target-locally `Q` morphism: `e` carries the neighbourhoods of the definition to neighbourhoods in
`Y'`, identifying the restrictions of `Y` and `Y'` to them. -/
private theorem targetLocally_comp_iso_hom {Y' : AdicSpace.{u}} (e : Y ≅ Y') {f : X ⟶ Y}
    (hf : targetLocally Q f) : targetLocally Q (f ≫ e.hom) := by
  intro y
  let e' : Y.obj ≅ Y'.obj := (ObjectProperty.ι _).mapIso e
  obtain ⟨V, hy, A, _, _, _, _, _, _, _, S, P, hP, B, _, _, _, _, _, _, _, T, P', hP', φ, hφ,
    hsheaf, eV, eU, hfac⟩ := hf (e'.inv.base y)
  -- `(f ≫ e.hom)⁻¹(e(V)) = f⁻¹(V)`
  have key := Opens.map_hom_obj_map_inv_obj (forgetToTop.mapIso e') V
  simp only [Functor.mapIso_hom, Functor.mapIso_inv, forgetToTop_map] at key
  have hr : Set.range
      ((Opens.map (f ≫ e.hom).hom.base).obj ((Opens.map e'.inv.base).obj V)).inclusion' =
        Set.range ((Opens.map f.hom.base).obj V).inclusion' := by
    rw [Opens.set_range_inclusion', Opens.set_range_inclusion']
    exact congrArg (fun U ↦ ((Opens.map f.hom.base).obj U : Set X.obj)) key
  refine ⟨(Opens.map e'.inv.base).obj V, hy, A, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, S, P, hP, B, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, T, P',
    hP', φ, hφ, hsheaf, (restrictIso e' V).symm ≪≫ eV,
    restrictIsoOfRangeEq _ (Opens.isOpenEmbedding _) (Opens.isOpenEmbedding _) hr ≪≫ eU, ?_⟩
  rw [← restrictIsoOfRangeEq_hom_ofRestrict X.obj (Opens.isOpenEmbedding _)
    (Opens.isOpenEmbedding _) hr, Category.assoc]
  simp [e', reassoc_of% hfac]

/-- **Being target-locally `Q` is invariant under isomorphisms** of the source and of the target,
for every property `Q` of morphisms of Huber pairs. -/
instance targetLocally_respectsIso : MorphismProperty.RespectsIso (@targetLocally.{u} Q) :=
  MorphismProperty.RespectsIso.mk _ (fun e _ hf ↦ targetLocally_iso_hom_comp e hf)
    (fun e _ hf ↦ targetLocally_comp_iso_hom e hf)

/-- **Identities**: if every point of `X` has an open neighbourhood `V ≅ Spa(A, A⁺)`, with
`(A, A⁺)` complete and Hausdorff and `Q` holding for the identity of `(A, A⁺)`, then the identity
of `X` is target-locally `Q`: over `V` it is the morphism induced by the identity of `(A, A⁺)`. -/
theorem targetLocally_id
    (h : ∀ x : X.obj, ∃ (V : Opens X.obj) (_ : x ∈ V) (A : Type u) (_ : CommRing A)
      (_ : UniformSpace A) (_ : IsUniformAddGroup A) (_ : IsTopologicalRing A)
      (_ : CompleteSpace A) (_ : T2Space A) (_ : IsHuberRing A) (S : Pair A)
      (P : PairOfDefinition A) (hP : P.ringOfDefinition ≤ S.plus) (_ : Q (Pair.Hom.id S)),
      Nonempty (X.obj.restrict V.isOpenEmbedding ≅ presentationLimitPreAdicSpace P S.plus
        S.isRingOfIntegralElements.isPowerBounded_of_mem hP)) :
    targetLocally Q (𝟙 X) := fun x ↦ by
  obtain ⟨V, hxV, A, _, _, _, _, _, _, _, S, P, hP, hQ, ⟨eV⟩⟩ := h x
  have hsheaf := (isSheafy_presentationLimitPreAdicSpace_iff P S.plus
    S.isRingOfIntegralElements.isPowerBounded_of_mem hP).mp
      (ObjectProperty.prop_of_iso isSheafy eV
        (isSheafy_restrict V.isOpenEmbedding X.property.isSheafy))
  refine ⟨V, hxV, A, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, S, P, hP, A, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, S, P, hP, Pair.Hom.id S, hQ,
    hsheaf, eV, restrictIsoOfRangeEq _ (Opens.isOpenEmbedding _) V.isOpenEmbedding ?_ ≪≫ eV, ?_⟩
  · -- the preimage of `V` under the identity is `V`, by definition of `Opens.map`
    rw [Opens.set_range_inclusion', Opens.set_range_inclusion']
    rfl
  · simpa using (restrictIsoOfRangeEq_hom_ofRestrict X.obj _ _ _).symm

end

end AdicSpace

end TauCeti
