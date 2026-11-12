/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.Affinoid.Comap
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.HuberPair

/-!
# Morphisms of affinoid pre-adic spaces and morphisms of Huber pairs

For Huber pairs `S = (A, A⁺)` and `T = (B, B⁺)` with compatible pairs of definition and a sheafy
structure presheaf on `Spa(B, B⁺)`, a morphism of Huber pairs `φ : (A, A⁺) → (B, B⁺)` induces a
morphism of pre-adic spaces `Spa(B, B⁺) ⟶ Spa(A, A⁺)`
(`TauCeti.ValuationSpectrum.presentationLimitPreAdicSpacePairComap`). When `A` and `B` are complete
and Hausdorff, pullback on global sections (`TauCeti.ValuationSpectrum.presentationLimitHomPairHom`)
is its two-sided inverse, giving Huber's contravariant bijection between morphisms of affinoid adic
spaces and morphisms of complete Hausdorff Huber pairs
(`TauCeti.ValuationSpectrum.presentationLimitPreAdicSpaceHomEquiv`).

## Main definitions

* `TauCeti.ValuationSpectrum.presentationLimitPreAdicSpacePairComap`: the morphism
  `Spa(B, B⁺) ⟶ Spa(A, A⁺)` of pre-adic spaces induced by a morphism of Huber pairs.
* `TauCeti.ValuationSpectrum.presentationLimitPreAdicSpaceHomEquiv`: for complete Hausdorff `A` and
  `B` with sheafy `Spa(B, B⁺)`, the equivalence `(Spa(B, B⁺) ⟶ Spa(A, A⁺)) ≃ Pair.Hom S T`.

## Main results

* `TauCeti.ValuationSpectrum.presentationLimitPreAdicSpacePairComap_id`,
  `TauCeti.ValuationSpectrum.presentationLimitPreAdicSpacePairComap_comp`: contravariant
  functoriality with respect to `Pair.Hom.id` and `Pair.Hom.comp`.
* `TauCeti.ValuationSpectrum.presentationLimitHomPairHom_presentationLimitPreAdicSpacePairComap`,
  `TauCeti.ValuationSpectrum.presentationLimitPreAdicSpacePairComap_presentationLimitHomPairHom`:
  the two inverse identities for complete Hausdorff Huber pairs.
* `TauCeti.ValuationSpectrum.presentationLimitPreAdicSpace_hom_ext_pairHom`: morphisms between
  complete Hausdorff affinoid spectra with sheafy source are determined by their induced morphism of
  Huber pairs.

## References

* R. Huber, *A generalization of formal schemes and rigid analytic varieties*, Math. Z. 217
  (1994), §2, Proposition 2.1(i).
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), §8.1, Theorem 8.12.
-/

public section

open CategoryTheory TopologicalSpace

namespace TauCeti.ValuationSpectrum

open TauCeti.Huber

universe u

section PairComap

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
  {B : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B]
  {C : Type u} [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsHuberRing C]

/-- The morphism `Spa(B, B⁺) ⟶ Spa(A, A⁺)` of pre-adic spaces induced by a morphism of Huber pairs
`φ : (A, A⁺) → (B, B⁺)`, for compatible pairs of definition `P` and `P'` when the structure
presheaf of `Spa(B, B⁺)` is a sheaf. Neither completeness of `A` or `B` nor a sheaf condition on
`Spa(A, A⁺)` is required. -/
noncomputable def presentationLimitPreAdicSpacePairComap
    (P : PairOfDefinition A) (P' : PairOfDefinition B) {S : Pair A} {T : Pair B}
    (hS : P.ringOfDefinition ≤ S.plus) (hT : P'.ringOfDefinition ≤ T.plus)
    (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa T.plus))
      (presentationLimitPresheaf P' T.plus))
    (φ : Pair.Hom S T) :
    presentationLimitPreAdicSpace P' T.plus
      T.isRingOfIntegralElements.isPowerBounded_of_mem hT ⟶
      presentationLimitPreAdicSpace P S.plus
        S.isRingOfIntegralElements.isPowerBounded_of_mem hS :=
  presentationLimitPreAdicSpaceComap φ.toRingHom φ.continuous_toRingHom φ.map_mem_plus
    S.isRingOfIntegralElements.isPowerBounded_of_mem
    T.isRingOfIntegralElements.isPowerBounded_of_mem hS hT hsheaf

/-- Unfolding lemma for `TauCeti.ValuationSpectrum.presentationLimitPreAdicSpacePairComap`. -/
theorem presentationLimitPreAdicSpacePairComap_def
    (P : PairOfDefinition A) (P' : PairOfDefinition B) {S : Pair A} {T : Pair B}
    (hS : P.ringOfDefinition ≤ S.plus) (hT : P'.ringOfDefinition ≤ T.plus)
    (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa T.plus))
      (presentationLimitPresheaf P' T.plus))
    (φ : Pair.Hom S T) :
    presentationLimitPreAdicSpacePairComap P P' hS hT hsheaf φ =
      presentationLimitPreAdicSpaceComap φ.toRingHom φ.continuous_toRingHom φ.map_mem_plus
        S.isRingOfIntegralElements.isPowerBounded_of_mem
        T.isRingOfIntegralElements.isPowerBounded_of_mem hS hT hsheaf :=
  (rfl)

/-- On points, `presentationLimitPreAdicSpacePairComap` acts as `Pair.Hom.spaComap`. -/
theorem presentationLimitPreAdicSpacePairComap_base_apply
    (P : PairOfDefinition A) (P' : PairOfDefinition B) {S : Pair A} {T : Pair B}
    (hS : P.ringOfDefinition ≤ S.plus) (hT : P'.ringOfDefinition ≤ T.plus)
    (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa T.plus))
      (presentationLimitPresheaf P' T.plus))
    (φ : Pair.Hom S T)
    (x : presentationLimitPreAdicSpace P' T.plus
      T.isRingOfIntegralElements.isPowerBounded_of_mem hT) :
    ((presentationLimitPreAdicSpacePairComap P P' hS hT hsheaf φ).base x : spa S.plus) =
      φ.spaComap x :=
  Subtype.ext <|
    (presentationLimitPreAdicSpaceComap_base_val φ.toRingHom φ.continuous_toRingHom
      φ.map_mem_plus S.isRingOfIntegralElements.isPowerBounded_of_mem
      T.isRingOfIntegralElements.isPowerBounded_of_mem hS hT hsheaf x).trans
      (Pair.Hom.spaComap_val φ x).symm

/-- The identity morphism of a Huber pair induces the identity morphism of `Spa(A, A⁺)`. -/
@[simp]
theorem presentationLimitPreAdicSpacePairComap_id
    (P : PairOfDefinition A) {S : Pair A} (hS : P.ringOfDefinition ≤ S.plus)
    (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa S.plus))
      (presentationLimitPresheaf P S.plus)) :
    presentationLimitPreAdicSpacePairComap P P hS hS hsheaf (Pair.Hom.id S) = 𝟙 _ := by
  rw [presentationLimitPreAdicSpacePairComap_def,
    presentationLimitPreAdicSpaceComap_congr (Pair.Hom.toRingHom_id S) _ continuous_id _
      (fun _ ha ↦ ha)]
  exact presentationLimitPreAdicSpaceComap_id
    S.isRingOfIntegralElements.isPowerBounded_of_mem hS hsheaf

/-- Contravariant functoriality of `presentationLimitPreAdicSpacePairComap` with respect to
composition of morphisms of Huber pairs. -/
@[reassoc]
theorem presentationLimitPreAdicSpacePairComap_comp
    (P : PairOfDefinition A) (P' : PairOfDefinition B) (P'' : PairOfDefinition C)
    {S : Pair A} {T : Pair B} {U : Pair C}
    (hS : P.ringOfDefinition ≤ S.plus) (hT : P'.ringOfDefinition ≤ T.plus)
    (hU : P''.ringOfDefinition ≤ U.plus)
    (hsheafT : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa T.plus))
      (presentationLimitPresheaf P' T.plus))
    (hsheafU : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa U.plus))
      (presentationLimitPresheaf P'' U.plus))
    (φ : Pair.Hom S T) (ψ : Pair.Hom T U) :
    presentationLimitPreAdicSpacePairComap P P'' hS hU hsheafU (ψ.comp φ) =
      presentationLimitPreAdicSpacePairComap P' P'' hT hU hsheafU ψ ≫
        presentationLimitPreAdicSpacePairComap P P' hS hT hsheafT φ := by
  rw [presentationLimitPreAdicSpacePairComap_def, presentationLimitPreAdicSpacePairComap_def,
    presentationLimitPreAdicSpacePairComap_def,
    presentationLimitPreAdicSpaceComap_congr (Pair.Hom.toRingHom_comp ψ φ) _
      (ψ.continuous_toRingHom.comp φ.continuous_toRingHom) _
      (fun a ha ↦ ψ.map_mem_plus _ (φ.map_mem_plus a ha))]
  exact presentationLimitPreAdicSpaceComap_comp φ.toRingHom φ.continuous_toRingHom φ.map_mem_plus
    ψ.toRingHom ψ.continuous_toRingHom ψ.map_mem_plus
    S.isRingOfIntegralElements.isPowerBounded_of_mem
    T.isRingOfIntegralElements.isPowerBounded_of_mem
    U.isRingOfIntegralElements.isPowerBounded_of_mem hS hT hU hsheafT hsheafU

/-- For a Huber pair `(A, A⁺)` whose structure presheaf is a sheaf, any two compatible pairs of
definition yield canonically isomorphic presentation-limit pre-adic spaces via the morphisms
induced by `Pair.Hom.id`. -/
noncomputable def presentationLimitPreAdicSpacePairChangeIso
    (P P' : PairOfDefinition A) {S : Pair A}
    (hP : P.ringOfDefinition ≤ S.plus) (hP' : P'.ringOfDefinition ≤ S.plus)
    (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa S.plus))
      (presentationLimitPresheaf P S.plus))
    (hsheaf' : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa S.plus))
      (presentationLimitPresheaf P' S.plus)) :
    presentationLimitPreAdicSpace P S.plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem hP ≅
      presentationLimitPreAdicSpace P' S.plus
        S.isRingOfIntegralElements.isPowerBounded_of_mem hP' where
  hom := presentationLimitPreAdicSpacePairComap P' P hP' hP hsheaf (Pair.Hom.id S)
  inv := presentationLimitPreAdicSpacePairComap P P' hP hP' hsheaf' (Pair.Hom.id S)
  hom_inv_id := by
    rw [← presentationLimitPreAdicSpacePairComap_comp, Pair.Hom.id_comp,
      presentationLimitPreAdicSpacePairComap_id]
  inv_hom_id := by
    rw [← presentationLimitPreAdicSpacePairComap_comp, Pair.Hom.id_comp,
      presentationLimitPreAdicSpacePairComap_id]

@[simp]
theorem presentationLimitPreAdicSpacePairChangeIso_hom
    (P P' : PairOfDefinition A) {S : Pair A}
    (hP : P.ringOfDefinition ≤ S.plus) (hP' : P'.ringOfDefinition ≤ S.plus)
    (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa S.plus))
      (presentationLimitPresheaf P S.plus))
    (hsheaf' : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa S.plus))
      (presentationLimitPresheaf P' S.plus)) :
    (presentationLimitPreAdicSpacePairChangeIso P P' hP hP' hsheaf hsheaf').hom =
      presentationLimitPreAdicSpacePairComap P' P hP' hP hsheaf (Pair.Hom.id S) :=
  (rfl)

@[simp]
theorem presentationLimitPreAdicSpacePairChangeIso_inv
    (P P' : PairOfDefinition A) {S : Pair A}
    (hP : P.ringOfDefinition ≤ S.plus) (hP' : P'.ringOfDefinition ≤ S.plus)
    (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa S.plus))
      (presentationLimitPresheaf P S.plus))
    (hsheaf' : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa S.plus))
      (presentationLimitPresheaf P' S.plus)) :
    (presentationLimitPreAdicSpacePairChangeIso P P' hP hP' hsheaf hsheaf').inv =
      presentationLimitPreAdicSpacePairComap P P' hP hP' hsheaf' (Pair.Hom.id S) :=
  (rfl)

end PairComap

section Complete

variable {A : Type u} [CommRing A] [UniformSpace A] [IsUniformAddGroup A]
  [IsTopologicalRing A] [CompleteSpace A] [T0Space A] [IsHuberRing A]
  {B : Type u} [CommRing B] [UniformSpace B] [IsUniformAddGroup B]
  [IsTopologicalRing B] [CompleteSpace B] [T0Space B] [IsHuberRing B]
  (P : PairOfDefinition A) (P' : PairOfDefinition B)
  (S : Pair A) (T : Pair B)
  (hS : P.ringOfDefinition ≤ S.plus) (hT : P'.ringOfDefinition ≤ T.plus)
  (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa T.plus))
    (presentationLimitPresheaf P' T.plus))

/-- **Pullback on global sections recovers the morphism of Huber pairs**: for complete Hausdorff
`A` and `B` and sheafy `Spa(B, B⁺)`, recovering the pair morphism from the pre-adic morphism
induced by `φ : (A, A⁺) → (B, B⁺)` gives back `φ`. -/
@[simp]
theorem presentationLimitHomPairHom_presentationLimitPreAdicSpacePairComap (φ : Pair.Hom S T) :
    presentationLimitHomPairHom P P' S T hS hT
      (presentationLimitPreAdicSpacePairComap P P' hS hT hsheaf φ) = φ := by
  apply Pair.Hom.ext
  rw [presentationLimitHomPairHom_toRingHom, presentationLimitPreAdicSpacePairComap_def]
  exact presentationLimitHomRingHom_presentationLimitPreAdicSpaceComap
    P S.plus S.isRingOfIntegralElements.isPowerBounded_of_mem hS
    P' T.plus T.isRingOfIntegralElements.isPowerBounded_of_mem hT
    φ.toRingHom φ.continuous_toRingHom φ.map_mem_plus hsheaf

/-- **Every morphism into a complete Hausdorff affinoid spectrum is induced by its pair morphism**:
for complete Hausdorff `A` and `B` and sheafy `Spa(B, B⁺)`, a pre-adic morphism
`f : Spa(B, B⁺) ⟶ Spa(A, A⁺)` equals the morphism induced by `presentationLimitHomPairHom`. -/
@[simp]
theorem presentationLimitPreAdicSpacePairComap_presentationLimitHomPairHom
    (f : presentationLimitPreAdicSpace P' T.plus
      T.isRingOfIntegralElements.isPowerBounded_of_mem hT ⟶
      presentationLimitPreAdicSpace P S.plus
        S.isRingOfIntegralElements.isPowerBounded_of_mem hS) :
    presentationLimitPreAdicSpacePairComap P P' hS hT hsheaf
      (presentationLimitHomPairHom P P' S T hS hT f) = f := by
  have hplus : ∀ a ∈ S.plus,
      presentationLimitHomRingHom P S.plus S.isRingOfIntegralElements.isPowerBounded_of_mem hS
        P' T.plus T.isRingOfIntegralElements.isPowerBounded_of_mem hT f a ∈ T.plus := by
    rw [← presentationLimitHomPairHom_toRingHom P P' S T hS hT f]
    exact (presentationLimitHomPairHom P P' S T hS hT f).map_mem_plus
  rw [presentationLimitPreAdicSpacePairComap_def,
    presentationLimitPreAdicSpaceComap_congr
      (presentationLimitHomPairHom_toRingHom P P' S T hS hT f) _
      (continuous_presentationLimitHomRingHom P S.plus
        S.isRingOfIntegralElements.isPowerBounded_of_mem hS P' T.plus
        T.isRingOfIntegralElements.isPowerBounded_of_mem hT f) _ hplus]
  exact presentationLimitPreAdicSpaceComap_presentationLimitHomRingHom
    P S.plus S.isRingOfIntegralElements.isPowerBounded_of_mem hS
    P' T.plus T.isRingOfIntegralElements.isPowerBounded_of_mem hT hsheaf f hplus

include hsheaf in
/-- **Morphisms between complete Hausdorff affinoid spectra are determined by their pair
morphisms**, provided the source spectrum is sheafy. -/
theorem presentationLimitPreAdicSpace_hom_ext_pairHom
    {f g : presentationLimitPreAdicSpace P' T.plus
      T.isRingOfIntegralElements.isPowerBounded_of_mem hT ⟶
      presentationLimitPreAdicSpace P S.plus
        S.isRingOfIntegralElements.isPowerBounded_of_mem hS}
    (h : presentationLimitHomPairHom P P' S T hS hT f =
      presentationLimitHomPairHom P P' S T hS hT g) : f = g := by
  refine presentationLimitPreAdicSpace_hom_ext
    P S.plus S.isRingOfIntegralElements.isPowerBounded_of_mem hS
    P' T.plus T.isRingOfIntegralElements.isPowerBounded_of_mem hT hsheaf ?_
  simpa only [presentationLimitHomPairHom_toRingHom] using congrArg Pair.Hom.toRingHom h

/-- **Huber's bijection between morphisms of complete affinoid spectra and morphisms of Huber
pairs** (Huber 1994, Proposition 2.1(i); Wedhorn, Theorem 8.12): for complete Hausdorff Huber pairs
`S = (A, A⁺)` and `T = (B, B⁺)` with sheafy `Spa(B, B⁺)`, morphisms `Spa(B, B⁺) ⟶ Spa(A, A⁺)` of
pre-adic spaces correspond bijectively to morphisms of Huber pairs `S → T`. -/
noncomputable def presentationLimitPreAdicSpaceHomEquiv :
    (presentationLimitPreAdicSpace P' T.plus
      T.isRingOfIntegralElements.isPowerBounded_of_mem hT ⟶
      presentationLimitPreAdicSpace P S.plus
        S.isRingOfIntegralElements.isPowerBounded_of_mem hS) ≃ Pair.Hom S T where
  toFun := presentationLimitHomPairHom P P' S T hS hT
  invFun := presentationLimitPreAdicSpacePairComap P P' hS hT hsheaf
  left_inv := presentationLimitPreAdicSpacePairComap_presentationLimitHomPairHom P P' S T hS hT
    hsheaf
  right_inv := presentationLimitHomPairHom_presentationLimitPreAdicSpacePairComap P P' S T hS hT
    hsheaf

@[simp]
theorem presentationLimitPreAdicSpaceHomEquiv_apply
    (f : presentationLimitPreAdicSpace P' T.plus
      T.isRingOfIntegralElements.isPowerBounded_of_mem hT ⟶
      presentationLimitPreAdicSpace P S.plus
        S.isRingOfIntegralElements.isPowerBounded_of_mem hS) :
    presentationLimitPreAdicSpaceHomEquiv P P' S T hS hT hsheaf f =
      presentationLimitHomPairHom P P' S T hS hT f :=
  (rfl)

@[simp]
theorem presentationLimitPreAdicSpaceHomEquiv_symm_apply (φ : Pair.Hom S T) :
    (presentationLimitPreAdicSpaceHomEquiv P P' S T hS hT hsheaf).symm φ =
      presentationLimitPreAdicSpacePairComap P P' hS hT hsheaf φ :=
  (rfl)

end Complete

end TauCeti.ValuationSpectrum
