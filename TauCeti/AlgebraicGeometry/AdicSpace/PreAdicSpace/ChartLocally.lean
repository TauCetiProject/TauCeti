/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.Adic
public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.Comap

import TauCeti.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# Morphisms of pre-adic spaces chart-locally induced by morphisms of Huber pairs

Given a property `Q` of morphisms of Huber pairs, a morphism `f : X ⟶ Y` of pre-adic spaces is
*chart-locally `Q`* when every point of `X` has an open neighbourhood `U` mapped by `f` into an
open `V ⊆ Y` such that `U ≅ Spa(B, B⁺)` and `V ≅ Spa(A, A⁺)` for Huber pairs, `B` complete and
Hausdorff, under which `f` restricted to `U → V` is the morphism induced by a morphism of Huber
pairs `(A, A⁺) → (B, B⁺)` satisfying `Q`. This is the shape of Wedhorn's Definition 8.48 and of
Huber's definition of adic morphisms (Huber 1994, §3); the name follows Mathlib's
`AlgebraicGeometry.affineLocally` for schemes.

The morphism `Spa(B, B⁺) ⟶ Spa(A, A⁺)` induced by a morphism of Huber pairs needs the structure
presheaf of `Spa(B, B⁺)` to be a sheaf, which is part of the data of the definition.

## Main definitions

* `TauCeti.PreAdicSpace.chartLocally`: the morphisms chart-locally induced by morphisms of Huber
  pairs satisfying a given property.

## Main results

* `TauCeti.PreAdicSpace.chartLocally_mono`: a weaker property of morphisms of Huber pairs gives a
  weaker chart-local property, with the same charts.
* `TauCeti.PreAdicSpace.chartLocally_respectsIso`: every chart-local property is invariant under
  isomorphisms of the source and of the target.
* `TauCeti.ValuationSpectrum.chartLocally_presentationLimitPreAdicSpaceComap`: the morphism
  `Spa(B, B⁺) ⟶ Spa(A, A⁺)` induced by a morphism of Huber pairs satisfying `Q` is chart-locally
  `Q`.
* `TauCeti.AdicSpace.exists_complete_chart_of_chartLocally`: when `Q` cancels on the right into
  complete Hausdorff Huber pairs, every point of the source of a chart-locally `Q` morphism of adic
  spaces admits an affinoid chart in which both the target and source rings are complete and
  Hausdorff.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Definition 8.48.
* R. Huber, *A generalization of formal schemes and rigid analytic varieties*, Math. Z. 217
  (1994), §3.
-/

public section

open CategoryTheory TopologicalSpace Topology

namespace TauCeti

open Huber

universe u

namespace PreAdicSpace

open ValuationSpectrum

/-- A morphism `f : X ⟶ Y` of pre-adic spaces is *chart-locally `Q`*, for a property `Q` of
morphisms of Huber pairs, when every point `x` of `X` has an open neighbourhood `U`, mapped by `f`
into an open `V` of `Y`, together with Huber pairs `(A, A⁺)` and `(B, B⁺)`, `B` complete and
Hausdorff with `Spa(B, B⁺)` having a sheaf as structure presheaf, a morphism
`φ : (A, A⁺) → (B, B⁺)` satisfying `Q`, and isomorphisms identifying `X` restricted to `U` with
`Spa(B, B⁺)` and `Y` restricted to `V` with `Spa(A, A⁺)`, under which `f` becomes the morphism
induced by `φ`. -/
def chartLocally
    (Q : ∀ {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
      {B : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B]
      {S : Pair A} {T : Pair B}, Pair.Hom S T → Prop) :
    MorphismProperty PreAdicSpace.{u} := fun X Y f ↦
  ∀ x : X, ∃ (U : Opens X) (_ : x ∈ U) (V : Opens Y) (_ : U ≤ (Opens.map f.base).obj V)
    (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A) (_ : IsTopologicalRing A)
    (_ : IsHuberRing A) (S : Pair A) (P : PairOfDefinition A) (hP : P.ringOfDefinition ≤ S.plus)
    (B : Type u) (_ : CommRing B) (_ : UniformSpace B) (_ : IsUniformAddGroup B)
    (_ : IsTopologicalRing B) (_ : CompleteSpace B) (_ : T2Space B) (_ : IsHuberRing B)
    (T : Pair B) (P' : PairOfDefinition B) (hP' : P'.ringOfDefinition ≤ T.plus)
    (φ : Pair.Hom S T) (_ : Q φ)
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

/-- Unfolding lemma for `TauCeti.PreAdicSpace.chartLocally`. -/
theorem chartLocally_iff
    {Q : ∀ {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
      {B : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B]
      {S : Pair A} {T : Pair B}, Pair.Hom S T → Prop}
    {X Y : PreAdicSpace.{u}} (f : X ⟶ Y) : chartLocally Q f ↔
    ∀ x : X, ∃ (U : Opens X) (_ : x ∈ U) (V : Opens Y) (_ : U ≤ (Opens.map f.base).obj V)
      (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A) (_ : IsTopologicalRing A)
      (_ : IsHuberRing A) (S : Pair A) (P : PairOfDefinition A) (hP : P.ringOfDefinition ≤ S.plus)
      (B : Type u) (_ : CommRing B) (_ : UniformSpace B) (_ : IsUniformAddGroup B)
      (_ : IsTopologicalRing B) (_ : CompleteSpace B) (_ : T2Space B) (_ : IsHuberRing B)
      (T : Pair B) (P' : PairOfDefinition B) (hP' : P'.ringOfDefinition ≤ T.plus)
      (φ : Pair.Hom S T) (_ : Q φ)
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

section

variable {Q Q' : ∀ {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsHuberRing A] {B : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
  [IsHuberRing B] {S : Pair A} {T : Pair B}, Pair.Hom S T → Prop}

/-- **Monotonicity**: if every morphism of Huber pairs satisfying `Q` satisfies `Q'`, then every
chart-locally `Q` morphism is chart-locally `Q'`, with the same charts. -/
theorem chartLocally_mono
    (h : ∀ {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
      {B : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B]
      {S : Pair A} {T : Pair B} (φ : Pair.Hom S T), Q φ → Q' φ)
    {X Y : PreAdicSpace.{u}} {f : X ⟶ Y} (hf : chartLocally Q f) : chartLocally Q' f := by
  refine (chartLocally_iff _).mpr fun x ↦ ?_
  obtain ⟨U, hx, V, hUV, A, _, _, _, _, S, P, hP, B, _, _, _, _, _, _, _, T, P', hP', φ, hφ,
    hsheaf, eU, eV, hfac⟩ := (chartLocally_iff _).mp hf x
  exact ⟨U, hx, V, hUV, A, inferInstance, inferInstance, inferInstance, inferInstance, S, P, hP,
    B, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, T, P', hP', φ, h φ hφ, hsheaf, eU, eV, hfac⟩

variable {X Y : PreAdicSpace.{u}}

/-- Precomposing a chart-locally `Q` morphism with an isomorphism gives a chart-locally `Q`
morphism: over the same opens of the target, `e` identifies the restrictions of the two sources. -/
private theorem chartLocally_iso_hom_comp {X' : PreAdicSpace.{u}} (e : X' ≅ X) {f : X ⟶ Y}
    (hf : chartLocally Q f) : chartLocally Q (e.hom ≫ f) := by
  refine (chartLocally_iff _).mpr fun x ↦ ?_
  obtain ⟨U, hx, V, hUV, A, _, _, _, _, S, P, hP, B, _, _, _, _, _, _, _, T, P', hP', φ, hφ,
    hsheaf, eU, eV, hfac⟩ := (chartLocally_iff _).mp hf (e.hom.base x)
  refine ⟨(Opens.map e.hom.base).obj U, hx, V, fun y hy ↦ hUV hy, A, inferInstance,
    inferInstance, inferInstance, inferInstance, S, P, hP, B, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, T, P', hP', φ, hφ,
    hsheaf, (restrictIso e.symm U).symm ≪≫ eU, eV, ?_⟩
  rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, ← hfac, restrictIso_inv_ofRestrict_assoc]
  -- `e.symm.inv` is `e.hom` (`Iso.symm_inv`, a `rfl`-lemma); it also occurs in the open restricted
  -- to, so `rw` cannot rewrite it on one side only
  rfl

/-- Postcomposing a chart-locally `Q` morphism with an isomorphism `e : Y ≅ Y'` gives a
chart-locally `Q` morphism: `e` carries the opens of the definition to opens of `Y'`, identifying
the restrictions of `Y` and `Y'` to them. -/
private theorem chartLocally_comp_iso_hom {Y' : PreAdicSpace.{u}} (e : Y ≅ Y') {f : X ⟶ Y}
    (hf : chartLocally Q f) : chartLocally Q (f ≫ e.hom) := by
  refine (chartLocally_iff _).mpr fun x ↦ ?_
  obtain ⟨U, hx, V, hUV, A, _, _, _, _, S, P, hP, B, _, _, _, _, _, _, _, T, P', hP', φ, hφ,
    hsheaf, eU, eV, hfac⟩ := (chartLocally_iff _).mp hf x
  -- `e⁻¹(e(V)) = V`
  have key := Opens.map_hom_obj_map_inv_obj (forgetToTop.mapIso e) V
  simp only [Functor.mapIso_hom, Functor.mapIso_inv, forgetToTop_map] at key
  refine ⟨U, hx, (Opens.map e.inv.base).obj V, fun y hy ↦ ?_, A, inferInstance, inferInstance,
    inferInstance, inferInstance, S, P, hP, B, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, T, P', hP', φ, hφ, hsheaf, eU,
    (restrictIso e V).symm ≪≫ eV, ?_⟩
  · have hy' : f.base y ∈ ((Opens.map e.hom.base).obj ((Opens.map e.inv.base).obj V)) :=
      key.symm ▸ hUV hy
    exact hy'
  · rw [reassoc_of% hfac]
    simp

/-- **Being chart-locally `Q` is invariant under isomorphisms** of the source and of the target,
for every property `Q` of morphisms of Huber pairs. -/
instance chartLocally_respectsIso : MorphismProperty.RespectsIso (chartLocally.{u} Q) :=
  MorphismProperty.RespectsIso.mk _ (fun e _ hf ↦ chartLocally_iso_hom_comp e hf)
    (fun e _ hf ↦ chartLocally_comp_iso_hom e hf)

end

end PreAdicSpace

namespace ValuationSpectrum

open PreAdicSpace

variable {Q : ∀ {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsHuberRing A] {B : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
  [IsHuberRing B] {S : Pair A} {T : Pair B}, Pair.Hom S T → Prop}
  {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
  {B : Type u} [CommRing B] [UniformSpace B] [IsUniformAddGroup B] [IsTopologicalRing B]
  [CompleteSpace B] [T2Space B] [IsHuberRing B]
  {S : Pair A} {T : Pair B} (P : PairOfDefinition A) (P' : PairOfDefinition B)
  (hP : P.ringOfDefinition ≤ S.plus) (hP' : P'.ringOfDefinition ≤ T.plus)
  (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa T.plus))
    (presentationLimitPresheaf P' T.plus))

/-- **The morphism of adic spectra induced by a morphism of Huber pairs satisfying `Q` is
chart-locally `Q`**, witnessed over the whole of `Spa(B, B⁺)` and `Spa(A, A⁺)`, for `B` complete
and Hausdorff with sheafy structure presheaf. -/
theorem chartLocally_presentationLimitPreAdicSpaceComap (φ : Pair.Hom S T) (hφ : Q φ) :
    chartLocally Q (presentationLimitPreAdicSpaceComap φ.toRingHom φ.continuous_toRingHom
      φ.map_mem_plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem
      T.isRingOfIntegralElements.isPowerBounded_of_mem hP hP' hsheaf) := by
  refine (chartLocally_iff _).mpr fun _ ↦ ⟨⊤, trivial, ⊤, le_top, A, inferInstance,
    inferInstance, inferInstance, inferInstance, S, P, hP, B, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, T, P', hP', φ, hφ,
    hsheaf, restrictTopIso _, restrictTopIso _, ?_⟩
  rw [← restrictTopIso_hom, ← restrictTopIso_hom, Iso.inv_hom_id, Category.comp_id]

end ValuationSpectrum

namespace AdicSpace

open PairOfDefinition PreAdicSpace ValuationSpectrum

/-- **Complete Hausdorff charts for chart-local morphisms of adic spaces**: if `Q` is a property of
morphisms of Huber pairs that cancels on the right (`Q (φ₁.comp ιA) → Q φ₁`) whenever `S₁` and `T`
are complete Hausdorff Huber pairs, then every point `x` of the source of a morphism `f : X ⟶ Y` of
adic spaces satisfying `chartLocally Q f.hom` admits an affinoid chart `(U, V)` around `x` in which
both the target ring `A` and the source ring `B` are complete and Hausdorff and the inducing Huber
pair morphism satisfies `Q`. -/
theorem exists_complete_chart_of_chartLocally
    (Q : ∀ {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
      {B : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B]
      {S : Pair A} {T : Pair B}, Pair.Hom S T → Prop)
    (hQ : ∀ {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
      {S : Pair A}
      {A₁ : Type u} [CommRing A₁] [UniformSpace A₁] [IsUniformAddGroup A₁]
      [IsTopologicalRing A₁] [CompleteSpace A₁] [T2Space A₁] [IsHuberRing A₁] {S₁ : Pair A₁}
      {B : Type u} [CommRing B] [UniformSpace B] [IsUniformAddGroup B]
      [IsTopologicalRing B] [CompleteSpace B] [T2Space B] [IsHuberRing B] {T : Pair B}
      {ιA : Pair.Hom S S₁} {φ₁ : Pair.Hom S₁ T},
      Q (φ₁.comp ιA) → Q φ₁)
    {X Y : AdicSpace.{u}} {f : X ⟶ Y} (hf : chartLocally Q f.hom) (x : X.obj) :
    ∃ (U : Opens X.obj) (_ : x ∈ U) (V : Opens Y.obj) (_ : U ≤ (Opens.map f.hom.base).obj V)
      (A : Type u) (_ : CommRing A) (_ : UniformSpace A) (_ : IsUniformAddGroup A)
      (_ : IsTopologicalRing A) (_ : CompleteSpace A) (_ : T2Space A) (_ : IsHuberRing A)
      (S : Pair A) (P : PairOfDefinition A) (hP : P.ringOfDefinition ≤ S.plus)
      (B : Type u) (_ : CommRing B) (_ : UniformSpace B) (_ : IsUniformAddGroup B)
      (_ : IsTopologicalRing B) (_ : CompleteSpace B) (_ : T2Space B) (_ : IsHuberRing B)
      (T : Pair B) (P' : PairOfDefinition B) (hP' : P'.ringOfDefinition ≤ T.plus)
      (φ : Pair.Hom S T) (_ : Q φ)
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
          T.isRingOfIntegralElements.isPowerBounded_of_mem hP hP' hsheaf ≫
          eV.inv ≫ Y.obj.ofRestrict _ := by
  classical
  obtain ⟨U, hxU, V, hUV, A, _, _, _, _, S, P, hP, B, _, _, _, _, _, _, _, T, P', hP', φ, hφ,
    hsheafB, eU, eV, hfac⟩ := (chartLocally_iff f.hom).mp hf x
  -- 1. Form the `{1} / 1` rational localisation `(A₁, S₁)` of `(A, S)`.
  have hT1 : IsOpen (Ideal.span (({1} : Finset A) : Set A) : Set A) := by simp
  let L := Localization.Away (1 : A)
  have hden := P.hasDenominatorPower_denom_one ({1} : Finset A) L
  let _ := P.locUniformSpace ({1} : Finset A) 1 L hden
  have _ := P.isUniformAddGroup_locUniformSpace ({1} : Finset A) 1 L hden
  have _ := P.isTopologicalRing_locUniformSpace ({1} : Finset A) 1 L hden
  have _ := P.isHuberRing_completion_locTopology ({1} : Finset A) 1 L hden
  let S₁ := P.rationalLocalizationPair S hP ({1} : Finset A) 1 L hden
  let P₁ := P.completionLocalization ({1} : Finset A) 1 L hden
  have hP₁ : P₁.ringOfDefinition ≤ S₁.plus := by
    rw [rationalLocalizationPair_plus]
    exact P.completionLocalization_ringOfDefinition_le_completedPlusSubring S.plus hP _ _ L hden
  let ιA : Pair.Hom S S₁ := P.toCompletionLocHom S hP ({1} : Finset A) 1 L hden
  -- 2. Since `B` is already complete and Hausdorff, factor `φ : S → T` directly through `ιA`.
  have := P'.toNonarchimedeanRing
  have hs1 : IsUnit (φ.toRingHom 1) := by simp
  have hunit : ((hs1.unit⁻¹ : Bˣ) : B) = 1 := by simp
  obtain ⟨g, ⟨hgc, hge⟩, -⟩ :=
    P.existsUnique_continuous_ringHom_completion_locTopology ({1} : Finset A) 1 L hden
      φ.continuous_toRingHom.continuousAt hs1 fun t ht ↦ by
        rw [Finset.mem_singleton.mp ht, hunit, mul_one, map_one]
        exact isPowerBounded_one
  have hgplus : ∀ x ∈ S₁.plus, g x ∈ T.plus := by
    have hTclosed : IsClosed (T.plus : Set B) :=
      AddSubgroup.isClosed_of_isOpen T.plus.toAddSubgroup T.isRingOfIntegralElements.isOpen
    have hclosed : IsClosed ((T.plus.comap g : Subring _) : Set (UniformSpace.Completion L)) :=
      hTclosed.preimage hgc
    have := T.isRingOfIntegralElements.isIntegrallyClosedIn
    let f₀ : L →+* B := g.comp UniformSpace.Completion.coeRingHom
    intro x hx
    rw [rationalLocalizationPair_plus] at hx
    refine (P.completedPlusSubring_le_iff S.plus ({1} : Finset A) 1 L hden hclosed).mpr
      (fun c hc ↦ ?_) hx
    have hle : (Algebra.adjoin S.plus
        (Set.range fun t : ({1} : Finset A) ↦ (Localization.divBy (t : A) 1 : L))).toSubring ≤
        T.plus.comap f₀ := by
      rw [Algebra.adjoin_eq_ring_closure, Subring.closure_le]
      rintro _ (⟨a, rfl⟩ | ⟨⟨t, ht⟩, rfl⟩)
      · rw [SetLike.mem_coe, Subring.mem_comap]
        dsimp only [f₀]
        rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply S.plus A L,
          Algebra.algebraMap_ofSubsemiring_apply, UniformSpace.Completion.coe_coeRingHom,
          ← P.toCompletionLoc_apply ({1} : Finset A) 1 L hden, ← RingHom.comp_apply, hge]
        exact φ.map_mem_plus a.val a.property
      · rw [SetLike.mem_coe, Subring.mem_comap]
        dsimp only
        have ht1 : (t : A) = 1 := Finset.mem_singleton.mp ht
        have hdiv : (Localization.divBy (t : A) 1 : L) = 1 := by
          rw [ht1, ← one_mul (Localization.divBy (1 : A) 1 : L), ← map_one (algebraMap A L),
            Localization.algebraMap_mul_divBy, map_one]
        rw [hdiv, map_one]
        exact T.plus.one_mem
    have hle' : (integralClosure ↥(Algebra.adjoin S.plus
        (Set.range fun t : ({1} : Finset A) ↦ (Localization.divBy (t : A) 1 : L))) L).toSubring ≤
        T.plus.comap f₀ :=
      Subring.integralClosure_subring_le_iff.mpr fun _ hz ↦ hle hz
    exact hle' hc
  let φ₁ : Pair.Hom S₁ T :=
    { toRingHom := g
      continuous_toRingHom := hgc
      map_mem_plus := hgplus }
  have hcomp : φ₁.comp ιA = φ := by
    apply Pair.Hom.ext
    rw [Pair.Hom.toRingHom_comp, toRingHom_toCompletionLocHom]
    exact hge
  have hφ₁ : Q φ₁ := hQ (hcomp.symm ▸ hφ)
  -- 3. `R({1} / 1) = ⊤` gives `Spa(A₁, S₁⁺) ≅ Spa(A, S⁺)` compatible with `ιA`.
  have hsheafA : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa S.plus))
      (presentationLimitPresheaf P S.plus) :=
    (isSheafy_presentationLimitPreAdicSpace_iff P S.plus _ hP).mp
      (ObjectProperty.prop_of_iso isSheafy eV (isSheafy_restrict _ Y.property.isSheafy))
  have hsheafA₁ : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa S₁.plus))
      (presentationLimitPresheaf P₁ S₁.plus) :=
    isSheaf_presentationLimitPresheaf_rationalLocalizationPair P S hP ({1} : Finset A) 1 L hden
      hT1 hsheafA
  obtain ⟨eA, heA⟩ :=
    exists_iso_presentationLimitPreAdicSpaceComap_toCompletionLocHom_of_forall_mem P hP
      ({1} : Finset A) 1 L hden hT1 (fun y ↦ by rw [rationalSubset_singleton_one]; exact y.property)
      hsheafA₁
  have hfac₁ : presentationLimitPreAdicSpaceComap φ.toRingHom φ.continuous_toRingHom
      φ.map_mem_plus S.isRingOfIntegralElements.isPowerBounded_of_mem
      T.isRingOfIntegralElements.isPowerBounded_of_mem hP hP' hsheafB =
      presentationLimitPreAdicSpaceComap φ₁.toRingHom φ₁.continuous_toRingHom
        φ₁.map_mem_plus S₁.isRingOfIntegralElements.isPowerBounded_of_mem
        T.isRingOfIntegralElements.isPowerBounded_of_mem hP₁ hP' hsheafB ≫ eA.hom := by
    have hcomp_spa := presentationLimitPreAdicSpaceComap_comp
      ιA.toRingHom ιA.continuous_toRingHom ιA.map_mem_plus
      φ₁.toRingHom φ₁.continuous_toRingHom φ₁.map_mem_plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem
      S₁.isRingOfIntegralElements.isPowerBounded_of_mem
      T.isRingOfIntegralElements.isPowerBounded_of_mem
      hP hP₁ hP' hsheafA₁ hsheafB
    have hlhs : presentationLimitPreAdicSpaceComap φ.toRingHom φ.continuous_toRingHom
        φ.map_mem_plus S.isRingOfIntegralElements.isPowerBounded_of_mem
        T.isRingOfIntegralElements.isPowerBounded_of_mem hP hP' hsheafB =
        presentationLimitPreAdicSpaceComap (φ₁.toRingHom.comp ιA.toRingHom)
          (φ₁.continuous_toRingHom.comp ιA.continuous_toRingHom)
          (fun a ha ↦ φ₁.map_mem_plus (ιA.toRingHom a) (ιA.map_mem_plus a ha))
          S.isRingOfIntegralElements.isPowerBounded_of_mem
          T.isRingOfIntegralElements.isPowerBounded_of_mem hP hP' hsheafB := by
      congr 1
      rw [← Pair.Hom.toRingHom_comp, hcomp]
    rw [hlhs, hcomp_spa, heA]
  refine ⟨U, hxU, V, hUV, UniformSpace.Completion L, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, S₁, P₁, hP₁,
    B, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, T, P', hP', φ₁, hφ₁, hsheafB, eU, eV ≪≫ eA.symm, ?_⟩
  rw [Iso.trans_inv, Iso.symm_inv, hfac, hfac₁]
  simp only [Category.assoc]

end AdicSpace

end TauCeti

end
