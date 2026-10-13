/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.BaseChange
public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.LocallyOfFiniteType.Basic
public import TauCeti.RingTheory.Huber.LocalizationTopology.FiniteType

/-!
# Restricting morphisms locally of finite type over opens of the target

A morphism `f : X ⟶ Y` of pre-adic spaces is locally of finite type
(`TauCeti.PreAdicSpace.LocallyOfFiniteType`, Wedhorn, Definition 8.48) when it is, near every
point, the morphism of adic spectra induced by a morphism of Huber pairs topologically of finite
type. This file shows how such charts behave when the target chart is shrunk.

A chart morphism restricts over rational subsets of its target. Let
`φ : (A, A⁺) → (B, B⁺)` be topologically of finite type, with `Spa(B, B⁺)` sheafy. The restriction
of `Spa(φ) : Spa(B, B⁺) ⟶ Spa(A, A⁺)` over a rational subset `R(T/s)` is the morphism induced by
the base change `(A⟨T/s⟩, A_U⁺) → (B⟨φ(T)/φ(s)⟩, B_V⁺)`
(`TauCeti.ValuationSpectrum.prop_restrictPreimage_presentationLimitPreAdicSpaceComap_iff`). When
`A` is a Tate ring, this base change is again topologically of finite type
(`TauCeti.Huber.PairOfDefinition.isTopologicallyFiniteType_completionLocPairMap`), so the
restriction is locally of finite type. Rational subsets form a basis of `Spa(A, A⁺)`, and being
locally of finite type can be checked over an open cover of the target
(`TauCeti.PreAdicSpace.LocallyOfFiniteType.of_iSup_eq_top_restrictPreimage`), which gives the same
over every open of the target. The Tate hypothesis enters only through the stability of
topological finite type under the base change. The chart rings `B⟨φ(T)/φ(s)⟩` are completions, so
`B` itself need not be complete.

## Main results

* `locallyOfFiniteType_restrictPreimage_presentationLimitPreAdicSpaceComap_spaBasicOpen`:
  over a Tate ring `A`, the morphism induced by a morphism of Huber pairs topologically of finite
  type restricts to a morphism locally of finite type over every rational subset of `Spa(A, A⁺)`.
* `locallyOfFiniteType_restrictPreimage_presentationLimitPreAdicSpaceComap`: the same over
  every open of a sheafy `Spa(A, A⁺)`.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Lemma 7.46, Remark 8.8, Definitions 8.42 and
  8.48, and Proposition 8.46.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology

namespace TauCeti

open Huber Huber.PairOfDefinition

universe u

namespace ValuationSpectrum

open PreAdicSpace

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsTateRing A]
  {B : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B]
  {U : Pair A} {U' : Pair B} (P : PairOfDefinition A) (P' : PairOfDefinition B)
  (hP : P.ringOfDefinition ≤ U.plus) (hP' : P'.ringOfDefinition ≤ U'.plus) (φ : Pair.Hom U U')
  (hφ : φ.IsTopologicallyFiniteType)
  (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa U'.plus))
    (presentationLimitPresheaf P' U'.plus))

/-- **A finite-type morphism over a Tate ring restricts over rational subsets**: let
`φ : (A, A⁺) → (B, B⁺)` be topologically of finite type, with `A` a Tate ring and `Spa(B, B⁺)`
sheafy. For a rational subset `R(T/s)` of `Spa(A, A⁺)`, with `T`
spanning an open ideal and `Spa(A⟨T/s⟩, A_U⁺)` sheafy, the restriction of
`Spa(φ) : Spa(B, B⁺) ⟶ Spa(A, A⁺)` over `R(T/s)` is locally of finite type. It is the morphism
induced by the base change `(A⟨T/s⟩, A_U⁺) → (B⟨φ(T)/φ(s)⟩, B_V⁺)`, which is topologically of
finite type. -/
theorem locallyOfFiniteType_restrictPreimage_presentationLimitPreAdicSpaceComap_spaBasicOpen
    {T : Finset A} {s : A} (hT : IsOpen (Ideal.span (T : Set A) : Set A)) (L : Type u)
    [CommRing L] [Algebra A L] [IsLocalization.Away s L] (hden : P.HasDenominatorPower T s L)
    (hsheafU : letI := P.locUniformSpace T s L hden
      letI := P.isUniformAddGroup_locUniformSpace T s L hden
      letI := P.isTopologicalRing_locUniformSpace T s L hden
      letI := P.isHuberRing_completion_locTopology T s L hden
      Presheaf.IsSheaf
        (Opens.grothendieckTopology ↥(spa (P.rationalLocalizationPair U hP T s L hden).plus))
        (presentationLimitPresheaf (P.completionLocalization T s L hden)
          (P.rationalLocalizationPair U hP T s L hden).plus)) :
    LocallyOfFiniteType ((presentationLimitPreAdicSpaceComap φ.toRingHom φ.continuous_toRingHom
      (fun _ hJ ↦ hφ.isTopologicallyFiniteType_toRingHom.isOpen_map hJ) φ.map_mem_plus
      U.isRingOfIntegralElements.isPowerBounded_of_mem
      U'.isRingOfIntegralElements.isPowerBounded_of_mem hP hP' hsheaf).restrictPreimage
        (spaBasicOpen U.plus T s)) := by
  classical
  have hopen : ∀ ⦃J : Ideal A⦄, IsOpen (J : Set A) → IsOpen (J.map φ.toRingHom : Set B) :=
    fun _ hJ ↦ hφ.isTopologicallyFiniteType_toRingHom.isOpen_map hJ
  let L' := Localization.Away (φ.toRingHom s)
  let T' : Finset B := T.image φ.toRingHom
  have hT' : IsOpen (Ideal.span (T' : Set B) : Set B) := by
    rw [Finset.coe_image, ← Ideal.map_span]
    exact hopen hT
  have hden' := P'.hasDenominatorPower_of_isOpen_span T' (φ.toRingHom s) L' hT'
  let _ := P.locUniformSpace T s L hden
  have _ := P.isUniformAddGroup_locUniformSpace T s L hden
  have _ := P.isTopologicalRing_locUniformSpace T s L hden
  have _ := P.isHuberRing_completion_locTopology T s L hden
  let _ := P'.locUniformSpace T' (φ.toRingHom s) L' hden'
  have _ := P'.isUniformAddGroup_locUniformSpace T' (φ.toRingHom s) L' hden'
  have _ := P'.isTopologicalRing_locUniformSpace T' (φ.toRingHom s) L' hden'
  have _ := P'.isHuberRing_completion_locTopology T' (φ.toRingHom s) L' hden'
  -- over a Tate ring `T` generates the unit ideal, hence so do `φ(T)` and `φ(s)`
  have hspanA : Ideal.span (insert s (T : Set A)) = ⊤ :=
    IsTateRing.eq_top_of_isOpen (AddSubgroup.isOpen_mono
      (H₁ := (Ideal.span (T : Set A)).toAddSubgroup)
      (H₂ := (Ideal.span (insert s (T : Set A))).toAddSubgroup)
      (Ideal.span_mono (Set.subset_insert s _)) hT)
  have hspan : Ideal.span (insert (φ.toRingHom s) (T' : Set B)) = ⊤ := by
    rw [Finset.coe_image, ← Set.image_insert_eq, ← Ideal.map_span, hspanA, Ideal.map_top]
  have hψ := P.isTopologicallyFiniteType_completionLocPairMap U hP T s L hden P' U' hP' φ T'
    (φ.toRingHom s) L' hden' rfl (fun _ ht ↦ Finset.mem_image_of_mem _ ht) hφ hspan
  refine (prop_restrictPreimage_presentationLimitPreAdicSpaceComap_iff P P' hP hP' φ hopen hsheaf
    T s L hden L' (@LocallyOfFiniteType.{u}) hden' hT hsheafU).mpr ?_
  exact locallyOfFiniteType_presentationLimitPreAdicSpaceComap _ _ _ _ _ _ hψ

/-- **A finite-type morphism over a Tate ring restricts over every open of a sheafy target**: let
`φ : (A, A⁺) → (B, B⁺)` be topologically of finite type, with `A` a Tate ring and both `Spa(A, A⁺)`
and `Spa(B, B⁺)` sheafy. Then for every open `W` of `Spa(A, A⁺)`, the restriction
`Spa(φ)⁻¹(W) → W` of `Spa(φ) : Spa(B, B⁺) ⟶ Spa(A, A⁺)` is locally of finite type. The open `W`
is covered by rational subsets, over each of which this is
`locallyOfFiniteType_restrictPreimage_presentationLimitPreAdicSpaceComap_spaBasicOpen`. -/
theorem locallyOfFiniteType_restrictPreimage_presentationLimitPreAdicSpaceComap
    (hsheafA : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa U.plus))
      (presentationLimitPresheaf P U.plus))
    (W : Opens (presentationLimitPreAdicSpace P U.plus
      U.isRingOfIntegralElements.isPowerBounded_of_mem hP)) :
    LocallyOfFiniteType ((presentationLimitPreAdicSpaceComap φ.toRingHom φ.continuous_toRingHom
      (fun _ hJ ↦ hφ.isTopologicallyFiniteType_toRingHom.isOpen_map hJ) φ.map_mem_plus
      U.isRingOfIntegralElements.isPowerBounded_of_mem
      U'.isRingOfIntegralElements.isPowerBounded_of_mem hP hP' hsheaf).restrictPreimage W) := by
  set f := presentationLimitPreAdicSpaceComap φ.toRingHom φ.continuous_toRingHom
    (fun _ hJ ↦ hφ.isTopologicallyFiniteType_toRingHom.isOpen_map hJ) φ.map_mem_plus
    U.isRingOfIntegralElements.isPowerBounded_of_mem
    U'.isRingOfIntegralElements.isPowerBounded_of_mem hP hP' hsheaf
  refine Hom.prop_restrictPreimage_of_forall_exists_le f (@LocallyOfFiniteType.{u})
    (fun _ ↦ LocallyOfFiniteType.of_iSup_eq_top_restrictPreimage) W fun y ↦ ?_
  -- every point of `W` lies in a rational subset `R(T/s)` contained in `W`
  obtain ⟨R, hR, hyR, hRW⟩ := Opens.isBasis_iff_nbhd.mp (isBasis_spaRationalOpens U.plus) y.2
  obtain ⟨T, s, hT, rfl⟩ := mem_spaRationalOpens_iff_exists_spaBasicOpen.mp hR
  refine ⟨_, hyR, hRW, ?_⟩
  have hden := P.hasDenominatorPower_of_isOpen_span T s (Localization.Away s) hT
  refine locallyOfFiniteType_restrictPreimage_presentationLimitPreAdicSpaceComap_spaBasicOpen P P'
    hP hP' φ hφ hsheaf hT _ hden ?_
  rw [rationalLocalizationPair_plus]
  exact isSheaf_presentationLimitPresheaf_completionLocalization P U.plus
    U.isRingOfIntegralElements.isPowerBounded_of_mem hP _ _ _ hden hT hsheafA

end ValuationSpectrum

end TauCeti
