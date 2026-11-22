/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.LocalProperties.Basic
public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.Adic
public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.Affinoid.PairEquiv
public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.RationalOpen
public import TauCeti.RingTheory.Huber.TopologicallyFiniteType.Pair

import TauCeti.AlgebraicGeometry.AdicSpace.Spa.RationalSubset.Discrete
import TauCeti.RingTheory.Huber.LocalizationTopology.Discrete
import TauCeti.RingTheory.Huber.LocalizationTopology.FiniteType

/-!
# Complete affinoid open immersions and rational chart refinement

This module bundles a complete Hausdorff sheafy affinoid open immersion `Spa(A, A⁺) ⟶ X` as
`TauCeti.PreAdicSpace.CompleteAffinoidOpen X` and develops the presentation-level chart API shared
across local morphism properties:

* `CompleteAffinoidOpen.space`, `pairComap`, `ofRestrictIso`, `ofDiscrete`, `compOpenImmersion`,
  `ringEquivOfIso`, and `coe_ringEquivOfIso`: categorical, open-restriction, and
  global-sections interface.
* `CompleteAffinoidOpen.ofRationalLocalization`, `toRationalLocalizationHom`,
  `rationalLocalization`, `rationalLocalizationHom`,
  `pairComap_comp_rationalLocalizationHom_comp_hom`, `exists_ofRationalLocalization_lift`,
  `exists_rationalLocalization_lift_sq`, `pairComap_comp_rationalLocalization_sq`,
  `ofRationalLocalizationAwayEquiv`, and `ringHom_prop_rationalLocalizationHom_of_discreteTopology`:
  rational localisation shrinking, lifting, finite-type / discrete finite-presentation preservation,
  and discrete `Localization.Away` transport.
* `ringHom_prop_of_forall_rational_chart_discrete`: descends local ring-homomorphism properties
  (e.g. `RingHom.FiniteType`, `RingHom.FinitePresentation`) from pointwise discrete rational charts
  over `Spa(A, A⁺)` to the global ring homomorphism `φ : A →+* B`.

For the `{1} / 1` completion package (`ofCompletion`, `ofCompletionMap`) see
`TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.Affinoid.CompleteChart`.

## References

* R. Huber, *A generalization of formal schemes and rigid analytic varieties*, Math. Z. 217
  (1994), §2–§3.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Remarks 8.4 and 8.8,
  Theorem 8.12, and Definition 8.48.
-/

public section

open CategoryTheory TopologicalSpace Topology

namespace TauCeti.PreAdicSpace

open Huber Huber.PairOfDefinition ValuationSpectrum

universe u

/-- A complete Hausdorff sheafy affinoid open immersion `Spa(A, A⁺) ⟶ X` into a pre-adic space `X`.
Bundling the ring, Huber pair, compatible pair of definition, sheafiness, and open immersion
avoids threading a dozen presentation arguments through chart-refinement and composition proofs. -/
structure CompleteAffinoidOpen (X : PreAdicSpace.{u}) where
  /-- Underlying complete Hausdorff Huber ring. -/
  Ring : Type u
  [commRing : CommRing Ring]
  [uniformSpace : UniformSpace Ring]
  [isUniformAddGroup : IsUniformAddGroup Ring]
  [isTopologicalRing : IsTopologicalRing Ring]
  [completeSpace : CompleteSpace Ring]
  [t2Space : T2Space Ring]
  [isHuberRing : IsHuberRing Ring]
  /-- Underlying Huber pair `(A, A⁺)`. -/
  pair : Pair Ring
  /-- Compatible pair of definition of `Ring`. -/
  pairOfDefinition : PairOfDefinition Ring
  /-- Compatibility `A₀ ≤ A⁺`. -/
  le_plus : pairOfDefinition.ringOfDefinition ≤ pair.plus
  /-- Sheafiness of the presentation-limit structure presheaf on `Spa(A, A⁺)`. -/
  isSheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa pair.plus))
    (presentationLimitPresheaf pairOfDefinition pair.plus)
  /-- Open immersion `Spa(A, A⁺) ⟶ X`. -/
  hom : presentationLimitPreAdicSpace pairOfDefinition pair.plus
    pair.isRingOfIntegralElements.isPowerBounded_of_mem le_plus ⟶ X
  [isOpenImmersion : IsOpenImmersion hom]

attribute [instance] CompleteAffinoidOpen.commRing CompleteAffinoidOpen.uniformSpace
  CompleteAffinoidOpen.isUniformAddGroup CompleteAffinoidOpen.isTopologicalRing
  CompleteAffinoidOpen.completeSpace CompleteAffinoidOpen.t2Space CompleteAffinoidOpen.isHuberRing
  CompleteAffinoidOpen.isOpenImmersion

namespace CompleteAffinoidOpen

/-- Underlying affinoid `PreAdicSpace` `Spa(C.Ring, C.pair.plus)` of a `CompleteAffinoidOpen`. -/
noncomputable abbrev space {X : PreAdicSpace.{u}} (C : CompleteAffinoidOpen X) :
    PreAdicSpace.{u} :=
  presentationLimitPreAdicSpace C.pairOfDefinition C.pair.plus
    C.pair.isRingOfIntegralElements.isPowerBounded_of_mem C.le_plus

/-- Morphism `CX.space ⟶ CY.space` induced contravariantly by a Huber-pair morphism
`CY.pair → CX.pair`. -/
noncomputable abbrev pairComap {X Y : PreAdicSpace.{u}}
    (CY : CompleteAffinoidOpen Y) (CX : CompleteAffinoidOpen X)
    (φ : Pair.Hom CY.pair CX.pair) : CX.space ⟶ CY.space :=
  presentationLimitPreAdicSpacePairComap CY.pairOfDefinition CX.pairOfDefinition
    CY.le_plus CX.le_plus CX.isSheaf φ

/-- The identity Huber-pair morphism induces the identity morphism on `C.space`. -/
theorem pairComap_id {X : PreAdicSpace.{u}} (C : CompleteAffinoidOpen X) :
    C.pairComap C (Pair.Hom.id C.pair) = 𝟙 C.space :=
  presentationLimitPreAdicSpacePairComap_id C.pairOfDefinition C.le_plus C.isSheaf

/-- Contravariant functoriality of `CompleteAffinoidOpen.pairComap` with respect to composition
of Huber-pair morphisms. -/
@[reassoc, simp]
theorem pairComap_comp {X Y Z : PreAdicSpace.{u}} (CZ : CompleteAffinoidOpen Z)
    (CY : CompleteAffinoidOpen Y) (CX : CompleteAffinoidOpen X)
    (ψ : Pair.Hom CZ.pair CY.pair) (φ : Pair.Hom CY.pair CX.pair) :
    CZ.pairComap CX (φ.comp ψ) = CY.pairComap CX φ ≫ CZ.pairComap CY ψ :=
  presentationLimitPreAdicSpacePairComap_comp CZ.pairOfDefinition CY.pairOfDefinition
    CX.pairOfDefinition CZ.le_plus CY.le_plus CX.le_plus CY.isSheaf CX.isSheaf ψ φ

/-- `CompleteAffinoidOpen.pairComap` is injective: two Huber-pair morphisms `CY.pair → CX.pair`
inducing the same morphism `CX.space ⟶ CY.space` are equal. -/
theorem pairComap_injective {X Y : PreAdicSpace.{u}}
    (CY : CompleteAffinoidOpen Y) (CX : CompleteAffinoidOpen X) :
    Function.Injective (CY.pairComap CX) := Function.LeftInverse.injective
  (presentationLimitHomPairHom_presentationLimitPreAdicSpacePairComap
    CY.pairOfDefinition CX.pairOfDefinition CY.pair CX.pair CY.le_plus CX.le_plus CX.isSheaf)

/-- Pointwise evaluation of a commuting square `CY.pairComap CX φ ≫ CY.hom = CX.hom ≫ f`. -/
theorem pairComap_comp_hom_base {X Y : PreAdicSpace.{u}} (CY : CompleteAffinoidOpen Y)
    (CX : CompleteAffinoidOpen X) (φ : Pair.Hom CY.pair CX.pair) {f : X ⟶ Y}
    (hsq : CY.pairComap CX φ ≫ CY.hom = CX.hom ≫ f) (c : CX.space) :
    CY.hom.base ((CY.pairComap CX φ).base c) = f.base (CX.hom.base c) := by
  have h := congrArg (fun m : CX.space ⟶ Y ↦ m.base c) hsq
  rwa [PreAdicSpace.comp_base, PreAdicSpace.comp_base, TopCat.coe_comp, TopCat.coe_comp,
    Function.comp_apply, Function.comp_apply] at h

section OfRestrictIso

variable {X : PreAdicSpace.{u}} {U : Opens X} {A : Type u} [CommRing A] [UniformSpace A]
  [IsUniformAddGroup A] [IsTopologicalRing A] [CompleteSpace A] [T2Space A] [IsHuberRing A]
  (S : Pair A) (P : PairOfDefinition A) (hP : P.ringOfDefinition ≤ S.plus)
  (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa S.plus))
    (presentationLimitPresheaf P S.plus)) (eU : X.restrict U.isOpenEmbedding ≅
    presentationLimitPreAdicSpace P S.plus S.isRingOfIntegralElements.isPowerBounded_of_mem hP)

/-- Package an open restriction isomorphism `X|_U ≅ Spa(A, A⁺)` for a complete Hausdorff sheafy
Huber pair `(A, A⁺)` as a `CompleteAffinoidOpen X` with immersion `eU.inv ≫ X.ofRestrict _`. -/
@[expose]
noncomputable def ofRestrictIso : CompleteAffinoidOpen X where
  Ring := A; pair := S; pairOfDefinition := P; le_plus := hP; isSheaf := hsheaf
  hom := eU.inv ≫ X.ofRestrict U.isOpenEmbedding; isOpenImmersion := IsOpenImmersion.comp _ _

/-- The open immersion of `ofRestrictIso` is `eU.inv ≫ X.ofRestrict U.isOpenEmbedding`. -/
@[simp]
theorem ofRestrictIso_hom :
    (ofRestrictIso S P hP hsheaf eU).hom = eU.inv ≫ X.ofRestrict U.isOpenEmbedding := rfl

/-- On points of `U`, the open immersion of `ofRestrictIso` sends `eU.hom.base ⟨x, hx⟩` back to
`x`. -/
theorem ofRestrictIso_hom_base {x : X} (hx : x ∈ U) :
    (ofRestrictIso S P hP hsheaf eU).hom.base (eU.hom.base ⟨x, hx⟩) = x := by
  let u : X.restrict U.isOpenEmbedding := ⟨x, hx⟩
  have hpt := congrArg (fun m : X.restrict U.isOpenEmbedding ⟶ X ↦ m.base u)
    (Iso.hom_inv_id_assoc eU (X.ofRestrict U.isOpenEmbedding))
  rw [PreAdicSpace.comp_base, TopCat.coe_comp, Function.comp_apply,
    ← ofRestrictIso_hom S P hP hsheaf eU, PreAdicSpace.ofRestrict_base] at hpt
  exact hpt

/-- On points of `Spa(A, A⁺)`, `(ofRestrictIso ...).hom.base` sends `b` to `(eU.inv.base b).val`.
-/
theorem ofRestrictIso_hom_base_apply (b : (ofRestrictIso S P hP hsheaf eU).space) :
    (ofRestrictIso S P hP hsheaf eU).hom.base b = (eU.inv.base b).val :=
  (congrArg (fun m : _ ⟶ X ↦ m.base b) (ofRestrictIso_hom S P hP hsheaf eU)).trans <| by
    let b' : presentationLimitPreAdicSpace P S.plus
        S.isRingOfIntegralElements.isPowerBounded_of_mem hP := b
    change (eU.inv ≫ X.ofRestrict U.isOpenEmbedding).base b' = (eU.inv.base b').val
    rw [PreAdicSpace.comp_base, TopCat.coe_comp, Function.comp_apply,
      PreAdicSpace.ofRestrict_base]; rfl

variable {Y : PreAdicSpace.{u}} {V : Opens Y} {B : Type u} [CommRing B] [UniformSpace B]
  [IsUniformAddGroup B] [IsTopologicalRing B] [CompleteSpace B] [T2Space B] [IsHuberRing B]
  (T : Pair B) (P' : PairOfDefinition B) (hP' : P'.ringOfDefinition ≤ T.plus)
  (hsheafB : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa T.plus))
    (presentationLimitPresheaf P' T.plus)) (eV : Y.restrict V.isOpenEmbedding ≅
    presentationLimitPreAdicSpace P' T.plus T.isRingOfIntegralElements.isPowerBounded_of_mem hP')

/-- The induced morphism `pairComap` between two `ofRestrictIso` charts is
`presentationLimitPreAdicSpacePairComap`. -/
@[simp]
theorem ofRestrictIso_pairComap (φ : Pair.Hom S T) :
    (ofRestrictIso S P hP hsheaf eU).pairComap (ofRestrictIso T P' hP' hsheafB eV) φ =
      presentationLimitPreAdicSpacePairComap P P' hP hP' hsheafB φ := rfl

/-- A chart factorisation `Y.ofRestrict _ ≫ f = eV.hom ≫ Spa(φ) ≫ eU.inv ≫ X.ofRestrict _`
translates directly into a commuting open-immersion square between `ofRestrictIso` charts. -/
theorem ofRestrictIso_pairComap_comp_hom (φ : Pair.Hom S T) {f : Y ⟶ X}
    (hfac : Y.ofRestrict V.isOpenEmbedding ≫ f =
      eV.hom ≫ presentationLimitPreAdicSpaceComap φ.toRingHom φ.continuous_toRingHom
        φ.map_mem_plus S.isRingOfIntegralElements.isPowerBounded_of_mem
        T.isRingOfIntegralElements.isPowerBounded_of_mem hP hP' hsheafB ≫
        eU.inv ≫ X.ofRestrict U.isOpenEmbedding) :
    (ofRestrictIso S P hP hsheaf eU).pairComap (ofRestrictIso T P' hP' hsheafB eV) φ ≫
        (ofRestrictIso S P hP hsheaf eU).hom = (ofRestrictIso T P' hP' hsheafB eV).hom ≫ f := by
  have h : (eV.inv ≫ Y.ofRestrict V.isOpenEmbedding) ≫ f =
      presentationLimitPreAdicSpaceComap φ.toRingHom φ.continuous_toRingHom
        φ.map_mem_plus S.isRingOfIntegralElements.isPowerBounded_of_mem
        T.isRingOfIntegralElements.isPowerBounded_of_mem hP hP' hsheafB ≫
        eU.inv ≫ X.ofRestrict U.isOpenEmbedding := by
    rw [Category.assoc, hfac, Iso.inv_hom_id_assoc]
  rw [ofRestrictIso_pairComap, ofRestrictIso_hom, ofRestrictIso_hom,
    presentationLimitPreAdicSpacePairComap_def]
  exact h.symm

end OfRestrictIso

/-- Package a discrete Huber ring `A` with a sheafy presentation `(P, S)` as a self-chart
`CompleteAffinoidOpen` via the identity open immersion `𝟙 Spa(S)`. -/
noncomputable abbrev ofDiscrete {A : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [DiscreteTopology A] [IsHuberRing A]
    (S : Pair A) (P : PairOfDefinition A) (hP : P.ringOfDefinition ≤ S.plus)
    (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa S.plus))
      (presentationLimitPresheaf P S.plus)) :
    CompleteAffinoidOpen (presentationLimitPreAdicSpace P S.plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem hP) :=
  letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
  haveI : IsUniformAddGroup A := isUniformAddGroup_of_addCommGroup
  haveI : DiscreteUniformity A := IsRightUniformAddGroup.discreteUniformity
  { Ring := A, pair := S, pairOfDefinition := P, le_plus := hP, isSheaf := hsheaf, hom := 𝟙 _ }

/-- Postcompose a `CompleteAffinoidOpen X` with an open immersion `g : X ⟶ Y` to obtain a
`CompleteAffinoidOpen Y` with the same underlying complete Hausdorff Huber pair. -/
@[expose]
noncomputable def compOpenImmersion {X Y : PreAdicSpace.{u}} (C : CompleteAffinoidOpen X)
    (g : X ⟶ Y) [IsOpenImmersion g] : CompleteAffinoidOpen Y where
  Ring := C.Ring; pair := C.pair; pairOfDefinition := C.pairOfDefinition; le_plus := C.le_plus
  isSheaf := C.isSheaf; hom := C.hom ≫ g; isOpenImmersion := IsOpenImmersion.comp _ _

/-- The open immersion of `C.compOpenImmersion g` is `C.hom ≫ g`. -/
@[simp]
theorem compOpenImmersion_hom {X Y : PreAdicSpace.{u}} (C : CompleteAffinoidOpen X)
    (g : X ⟶ Y) [IsOpenImmersion g] : (C.compOpenImmersion g).hom = C.hom ≫ g := rfl

/-- On underlying points, `(C.compOpenImmersion g).hom.base` acts as `g.base (C.hom.base x)`. -/
theorem compOpenImmersion_hom_base {X Y : PreAdicSpace.{u}} (C : CompleteAffinoidOpen X)
    (g : X ⟶ Y) [IsOpenImmersion g] (x : C.space) :
    (C.compOpenImmersion g).hom.base x = g.base (C.hom.base x) :=
  (congrArg (fun m : C.space ⟶ Y ↦ m.base x) (compOpenImmersion_hom C g)).trans
    (by rw [PreAdicSpace.comp_base, TopCat.coe_comp, Function.comp_apply])

/-- Postcomposing the target chart with an open immersion `g` leaves `pairComap` unchanged. -/
theorem compOpenImmersion_pairComap_left {X Y Y' : PreAdicSpace.{u}}
    (CY : CompleteAffinoidOpen Y) (CX : CompleteAffinoidOpen X) (g : Y ⟶ Y')
    [IsOpenImmersion g] (φ : Pair.Hom CY.pair CX.pair) :
    (CY.compOpenImmersion g).pairComap CX φ = CY.pairComap CX φ := rfl

/-- Postcomposing the target chart with an open immersion `g` transforms
`CY.pairComap CX φ ≫ CY.hom` by postcomposing with `g`. -/
theorem pairComap_compOpenImmersion_left_comp_hom {X Y Y' : PreAdicSpace.{u}}
    (CY : CompleteAffinoidOpen Y) (CX : CompleteAffinoidOpen X) (g : Y ⟶ Y')
    [IsOpenImmersion g] (φ : Pair.Hom CY.pair CX.pair) :
    (CY.compOpenImmersion g).pairComap CX φ ≫ (CY.compOpenImmersion g).hom =
      CY.pairComap CX φ ≫ CY.hom ≫ g := by
  rw [compOpenImmersion_hom, compOpenImmersion_pairComap_left]; rfl

/-- A commuting square with source chart `CX.compOpenImmersion g` and morphism `f : X' ⟶ Z`
is equivalent to the corresponding square for `CX` and `g ≫ f`. -/
theorem pairComap_compOpenImmersion_right_eq_comp_iff {X X' Y Z : PreAdicSpace.{u}}
    (CY : CompleteAffinoidOpen Y) (CX : CompleteAffinoidOpen X) (g : X ⟶ X')
    [IsOpenImmersion g] (φ : Pair.Hom CY.pair CX.pair) (f : X' ⟶ Z) (h : CY.space ⟶ Z) :
    CY.pairComap (CX.compOpenImmersion g) φ ≫ h = (CX.compOpenImmersion g).hom ≫ f ↔
      CY.pairComap CX φ ≫ h = CX.hom ≫ g ≫ f :=
  ⟨fun H ↦ H.trans (Category.assoc ..), fun H ↦ H.trans (Category.assoc ..).symm⟩

/-- An isomorphism `e : C₁.space ≅ C₂.space` between complete Hausdorff affinoid pre-adic spaces
induces a ring isomorphism `C₂.Ring ≃+* C₁.Ring` on global sections via
`presentationLimitHomPairHom`. -/
@[expose]
noncomputable def ringEquivOfIso {X Y : PreAdicSpace.{u}} (C₁ : CompleteAffinoidOpen X)
    (C₂ : CompleteAffinoidOpen Y) (e : C₁.space ≅ C₂.space) : C₂.Ring ≃+* C₁.Ring :=
  RingEquiv.ofRingHom (presentationLimitHomPairHom C₂.pairOfDefinition C₁.pairOfDefinition
      C₂.pair C₁.pair C₂.le_plus C₁.le_plus e.hom).toRingHom
    (presentationLimitHomPairHom C₁.pairOfDefinition C₂.pairOfDefinition
      C₁.pair C₂.pair C₁.le_plus C₂.le_plus e.inv).toRingHom
    (by rw [← Pair.Hom.toRingHom_comp, ← presentationLimitHomPairHom_comp, e.hom_inv_id,
      presentationLimitHomPairHom_id, Pair.Hom.toRingHom_id])
    (by rw [← Pair.Hom.toRingHom_comp, ← presentationLimitHomPairHom_comp, e.inv_hom_id,
      presentationLimitHomPairHom_id, Pair.Hom.toRingHom_id])

/-- The underlying ring homomorphism of `ringEquivOfIso C₁ C₂ e` is the global-sections
homomorphism induced by `e.hom`. -/
@[simp]
theorem coe_ringEquivOfIso {X Y : PreAdicSpace.{u}} (C₁ : CompleteAffinoidOpen X)
    (C₂ : CompleteAffinoidOpen Y) (e : C₁.space ≅ C₂.space) :
    (ringEquivOfIso C₁ C₂ e : C₂.Ring →+* C₁.Ring) =
      (presentationLimitHomPairHom C₂.pairOfDefinition C₁.pairOfDefinition
        C₂.pair C₁.pair C₂.le_plus C₁.le_plus e.hom).toRingHom := by ext; rfl

section OfRationalLocalization

variable {Y : PreAdicSpace.{u}} {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsHuberRing A] {S : Pair A} (P : PairOfDefinition A) (hP : P.ringOfDefinition ≤ S.plus)
  (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa S.plus))
    (presentationLimitPresheaf P S.plus)) (kY : presentationLimitPreAdicSpace P S.plus
    S.isRingOfIntegralElements.isPowerBounded_of_mem hP ⟶ Y) [IsOpenImmersion kY]
  (T : Finset A) (s : A) (hT : IsOpen (Ideal.span (T : Set A) : Set A))

/-- Complete affinoid open obtained by restricting an affinoid open immersion `kY : Spa(S) ⟶ Y`
to the rational subset `R(T / s)`. -/
@[expose]
noncomputable def ofRationalLocalization : CompleteAffinoidOpen Y :=
  let L := Localization.Away s; let hden := P.hasDenominatorPower_of_isOpen_span T s L hT
  letI := P.locUniformSpace T s L hden; haveI := P.isUniformAddGroup_locUniformSpace T s L hden
  haveI := P.isTopologicalRing_locUniformSpace T s L hden
  haveI := P.isHuberRing_completion_locTopology T s L hden
  let S₁ := P.rationalLocalizationPair S hP T s L hden
  let P₁ := P.completionLocalization T s L hden
  have hP₁ : P₁.ringOfDefinition ≤ S₁.plus := by
    rw [rationalLocalizationPair_plus]
    exact P.completionLocalization_ringOfDefinition_le_completedPlusSubring S.plus hP T s L hden
  have hsheaf₁ :=
    isSheaf_presentationLimitPresheaf_rationalLocalizationPair P S hP T s L hden hT hsheaf
  let ι := presentationLimitPreAdicSpacePairComap P P₁ hP hP₁ hsheaf₁
    (P.toCompletionLocHom S hP T s L hden)
  haveI : IsOpenImmersion ι := by
    dsimp only [ι]; rw [presentationLimitPreAdicSpacePairComap_def]
    exact isOpenImmersion_presentationLimitPreAdicSpaceComap_toCompletionLocHom P hP T s L hden hT
      hsheaf₁
  { Ring := UniformSpace.Completion L, pair := S₁, pairOfDefinition := P₁, le_plus := hP₁,
    isSheaf := hsheaf₁, hom := ι ≫ kY, isOpenImmersion := IsOpenImmersion.comp ι kY }

/-- Canonical Huber-pair morphism `S → (ofRationalLocalization P hP hsheaf kY T s hT).pair` into
the completed rational localisation at `R(T / s)`. -/
@[expose]
noncomputable def toRationalLocalizationHom :
    Pair.Hom S (ofRationalLocalization P hP hsheaf kY T s hT).pair :=
  let L := Localization.Away s; let hden := P.hasDenominatorPower_of_isOpen_span T s L hT
  letI := P.locUniformSpace T s L hden; haveI := P.isUniformAddGroup_locUniformSpace T s L hden
  haveI := P.isTopologicalRing_locUniformSpace T s L hden
  haveI := P.isHuberRing_completion_locTopology T s L hden
  P.toCompletionLocHom S hP T s L hden

/-- Unfolding lemma identifying `toRationalLocalizationHom` with
`PairOfDefinition.toCompletionLocHom` at `Localization.Away s`. -/
theorem toRationalLocalizationHom_def :
    let L := Localization.Away s; let hden := P.hasDenominatorPower_of_isOpen_span T s L hT
    letI := P.locUniformSpace T s L hden; letI := P.isUniformAddGroup_locUniformSpace T s L hden
    letI := P.isTopologicalRing_locUniformSpace T s L hden
    letI := P.isHuberRing_completion_locTopology T s L hden
    toRationalLocalizationHom P hP hsheaf kY T s hT = P.toCompletionLocHom S hP T s L hden := rfl

/-- Open immersion `(ofRationalLocalization ...).space ⟶ Spa(S)` induced by
`toRationalLocalizationHom`. -/
noncomputable abbrev toRationalLocalizationComap :
    (ofRationalLocalization P hP hsheaf kY T s hT).space ⟶
      presentationLimitPreAdicSpace P S.plus S.isRingOfIntegralElements.isPowerBounded_of_mem hP :=
  let C := ofRationalLocalization P hP hsheaf kY T s hT
  presentationLimitPreAdicSpacePairComap P C.pairOfDefinition hP C.le_plus C.isSheaf
    (toRationalLocalizationHom P hP hsheaf kY T s hT)

/-- The open immersion of `ofRationalLocalization` factors as `toRationalLocalizationComap ≫ kY`. -/
@[reassoc, simp]
theorem ofRationalLocalization_hom :
    (ofRationalLocalization P hP hsheaf kY T s hT).hom =
      toRationalLocalizationComap P hP hsheaf kY T s hT ≫ kY := rfl

/-- The image of `toRationalLocalizationComap` in `Spa(S)` is the rational basic open
`spaBasicOpen S.plus T s`. -/
theorem range_toRationalLocalizationComap_base :
    Set.range (toRationalLocalizationComap P hP hsheaf kY T s hT).base =
      (spaBasicOpen S.plus T s : Set (spa S.plus)) := by
  rw [toRationalLocalizationComap, presentationLimitPreAdicSpacePairComap_def]
  exact range_presentationLimitPreAdicSpaceComap_toCompletionLocHom_base P hP T s _ _ _

/-- The image of `(ofRationalLocalization ...).hom` in `Y` is the image of `spaBasicOpen S.plus T s`
under `kY`. -/
theorem range_ofRationalLocalization_hom_base :
    Set.range (ofRationalLocalization P hP hsheaf kY T s hT).hom.base =
      kY.base '' (spaBasicOpen S.plus T s : Set (spa S.plus)) := by
  rw [ofRationalLocalization_hom, PreAdicSpace.comp_base, TopCat.coe_comp, Set.range_comp,
    range_toRationalLocalizationComap_base]

/-- **Pointwise rational-localisation lifting**: if `kY : Spa(S) ⟶ Y` composed with `g : Y ⟶ Z`
maps a point `a₀ ∈ Spa(S)` into the image of a complete affinoid open `D` of `Z`, then there is a
rational basic open `R(T/s)` around `a₀` on which `kY ≫ g` lifts through `D.hom`, induced by a
Huber-pair morphism `D.pair → (ofRationalLocalization ...).pair`. -/
theorem exists_ofRationalLocalization_lift {Z : PreAdicSpace.{u}}
    (D : CompleteAffinoidOpen Z) (g : Y ⟶ Z)
    {a₀ : presentationLimitPreAdicSpace P S.plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem hP} {d₀ : D.space}
    (had : (kY ≫ g).base a₀ = D.hom.base d₀) :
    ∃ (T : Finset A) (s : A) (hT : IsOpen (Ideal.span (T : Set A) : Set A)),
      a₀ ∈ spaBasicOpen S.plus T s ∧
      let CY₁ := ofRationalLocalization P hP hsheaf kY T s hT
      ∃ (a₁ : CY₁.space) (α : Pair.Hom D.pair CY₁.pair),
        CY₁.hom.base a₁ = kY.base a₀ ∧ D.pairComap CY₁ α ≫ D.hom = CY₁.hom ≫ g := by
  let OA : Opens (presentationLimitPreAdicSpace P S.plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem hP) :=
    ⟨(kY ≫ g).base ⁻¹' Set.range D.hom.base,
      D.hom.isOpenEmbedding.isOpen_range.preimage (kY ≫ g).base.hom.continuous_toFun⟩
  have ha₀O : a₀ ∈ OA := Set.mem_preimage.mpr (Set.mem_range.mpr ⟨d₀, had.symm⟩)
  obtain ⟨RA, hRA, ha₀R, hRAO⟩ := Opens.isBasis_iff_nbhd.mp (isBasis_spaRationalOpens S.plus) ha₀O
  obtain ⟨T, s, hT, rfl⟩ := mem_spaRationalOpens_iff_exists_spaBasicOpen.mp hRA
  let CY₁ := ofRationalLocalization P hP hsheaf kY T s hT
  let ι := toRationalLocalizationComap P hP hsheaf kY T s hT
  have hrange_ι := range_toRationalLocalizationComap_base P hP hsheaf kY T s hT
  obtain ⟨a₁, ha₁⟩ : (a₀ : spa S.plus) ∈ Set.range ι.base :=
    hrange_ι.symm ▸ (ha₀R : (a₀ : spa S.plus) ∈ (spaBasicOpen S.plus T s : Set (spa S.plus)))
  have hsub : Set.range (CY₁.hom ≫ g).base ⊆ Set.range D.hom.base := by
    rintro _ ⟨z, rfl⟩
    rw [ofRationalLocalization_hom_assoc, PreAdicSpace.comp_base, TopCat.coe_comp,
      Function.comp_apply]
    exact hRAO (hrange_ι ▸ ⟨z, rfl⟩ :
      (ι.base z : spa S.plus) ∈ (spaBasicOpen S.plus T s : Set (spa S.plus)))
  let l := IsOpenImmersion.lift D.hom (CY₁.hom ≫ g) hsub
  refine ⟨T, s, hT, ha₀R, a₁, presentationLimitHomPairHom D.pairOfDefinition CY₁.pairOfDefinition
    D.pair CY₁.pair D.le_plus CY₁.le_plus l, ?_, ?_⟩
  · rw [ofRationalLocalization_hom, PreAdicSpace.comp_base, TopCat.coe_comp, Function.comp_apply]
    exact congrArg kY.base ha₁
  · rw [pairComap, presentationLimitPreAdicSpacePairComap_presentationLimitHomPairHom
      D.pairOfDefinition CY₁.pairOfDefinition D.pair CY₁.pair D.le_plus CY₁.le_plus CY₁.isSheaf]
    exact IsOpenImmersion.lift_fac D.hom (CY₁.hom ≫ g) hsub

/-- The canonical Huber-pair morphism `S → (ofRationalLocalization P hP hsheaf kY T s hT).pair`
into the completed rational localisation at `R(T / s)` is topologically of finite type. -/
theorem isTopologicallyFiniteType_toRationalLocalizationHom :
    (toRationalLocalizationHom P hP hsheaf kY T s hT).IsTopologicallyFiniteType := by
  let L := Localization.Away s; have hden := P.hasDenominatorPower_of_isOpen_span T s L hT
  let _ := P.locUniformSpace T s L hden; have _ := P.isUniformAddGroup_locUniformSpace T s L hden
  have _ := P.isTopologicalRing_locUniformSpace T s L hden
  have _ := P.isHuberRing_completion_locTopology T s L hden
  exact P.isTopologicallyFiniteType_toCompletionLocHom S hP T s L hden
    (Submodule.isOpen_mono (Ideal.span_mono (Set.subset_insert _ _)) hT)

/-- Over a discrete ring `A`, any ring-homomorphism property `R` that respects isomorphisms and
holds for localisations away from an element holds for
`(toRationalLocalizationHom P hP hsheaf kY T s hT).toRingHom`. -/
theorem ringHom_prop_toRationalLocalizationHom_of_discreteTopology
    {R : ∀ {X Y : Type u} [CommRing X] [CommRing Y], (X →+* Y) → Prop}
    (hiso : RingHom.RespectsIso @R) (hloc : RingHom.HoldsForLocalizationAway @R)
    [DiscreteTopology A] : R (toRationalLocalizationHom P hP hsheaf kY T s hT).toRingHom := by
  rw [toRationalLocalizationHom_def, toRingHom_toCompletionLocHom]
  exact P.ringHom_prop_toCompletionLoc_of_discreteTopology hiso hloc (T : Set A) s _ _

/-- When `A` is discrete, the canonical ring homomorphism
`(toRationalLocalizationHom P hP hsheaf kY T s hT).toRingHom` into the rational localisation
`A⟨T/s⟩` is algebraically of finite presentation (`RingHom.FinitePresentation`). -/
theorem finitePresentation_toRationalLocalizationHom [DiscreteTopology A] :
    (toRationalLocalizationHom P hP hsheaf kY T s hT).toRingHom.FinitePresentation := by
  rw [toRationalLocalizationHom_def, toRingHom_toCompletionLocHom]
  exact P.finitePresentation_toCompletionLoc_of_discreteTopology (T : Set A) s _ _

/-- Over a discrete ring `A`, the coordinate ring of the rational localisation
`ofRationalLocalization P hP hsheaf kY T s hT` is canonically isomorphic to
`Localization.Away s`. -/
noncomputable def ofRationalLocalizationAwayEquiv [DiscreteTopology A] :
    (ofRationalLocalization P hP hsheaf kY T s hT).Ring ≃+* Localization.Away s :=
  let L := Localization.Away s; let hden := P.hasDenominatorPower_of_isOpen_span T s L hT
  letI := P.locUniformSpace T s L hden; haveI := P.isUniformAddGroup_locUniformSpace T s L hden
  haveI := P.isTopologicalRing_locUniformSpace T s L hden
  (P.completionLocEquivOfDiscreteTopology (T : Set A) s L hden).symm

/-- Over a discrete ring `A`, `ofRationalLocalizationAwayEquiv` intertwines
`toRationalLocalizationHom` with `algebraMap A (Localization.Away s)`. -/
@[simp]
theorem ofRationalLocalizationAwayEquiv_comp_toRationalLocalizationHom [DiscreteTopology A] :
    (ofRationalLocalizationAwayEquiv P hP hsheaf kY T s hT : _ →+* Localization.Away s).comp
        (toRationalLocalizationHom P hP hsheaf kY T s hT).toRingHom =
      algebraMap A (Localization.Away s) := by
  rw [← RingEquiv.toRingHom_eq_coe, ofRationalLocalizationAwayEquiv, toRationalLocalizationHom_def,
    toRingHom_toCompletionLocHom]
  exact P.completionLocEquivOfDiscreteTopology_symm_comp_toCompletionLoc (T : Set A) s _ _

end OfRationalLocalization

/-- Restrict a `CompleteAffinoidOpen X` to the rational basic open `R(T / s)`. -/
noncomputable abbrev rationalLocalization {X : PreAdicSpace.{u}}
    (C : CompleteAffinoidOpen X) (T : Finset C.Ring) (s : C.Ring)
    (hT : IsOpen (Ideal.span (T : Set C.Ring) : Set C.Ring)) : CompleteAffinoidOpen X :=
  ofRationalLocalization C.pairOfDefinition C.le_plus C.isSheaf C.hom T s hT

/-- Canonical Huber-pair morphism `C.pair → (C.rationalLocalization T s hT).pair`. -/
noncomputable abbrev rationalLocalizationHom {X : PreAdicSpace.{u}}
    (C : CompleteAffinoidOpen X) (T : Finset C.Ring) (s : C.Ring)
    (hT : IsOpen (Ideal.span (T : Set C.Ring) : Set C.Ring)) :
    Pair.Hom C.pair (C.rationalLocalization T s hT).pair :=
  toRationalLocalizationHom C.pairOfDefinition C.le_plus C.isSheaf C.hom T s hT

/-- The open immersion of `C.rationalLocalization T s hT` factors as
`C.pairComap (C.rationalLocalization T s hT) (C.rationalLocalizationHom T s hT) ≫ C.hom`. -/
@[reassoc]
theorem rationalLocalization_hom {X : PreAdicSpace.{u}} (C : CompleteAffinoidOpen X)
    (T : Finset C.Ring) (s : C.Ring) (hT : IsOpen (Ideal.span (T : Set C.Ring) : Set C.Ring)) :
    (C.rationalLocalization T s hT).hom =
      C.pairComap (C.rationalLocalization T s hT) (C.rationalLocalizationHom T s hT) ≫ C.hom := rfl

/-- Reassociated rational-localisation square for precomposing a Huber-pair morphism `ψ` with
`CY.rationalLocalizationHom TA sA hTA` on the target chart `CY`. -/
theorem pairComap_comp_rationalLocalizationHom_comp_hom {X Y : PreAdicSpace.{u}}
    (CY : CompleteAffinoidOpen Y) {TA : Finset CY.Ring} {sA : CY.Ring}
    {hTA : IsOpen (Ideal.span (TA : Set CY.Ring) : Set CY.Ring)} (CX : CompleteAffinoidOpen X)
    (ψ : Pair.Hom (CY.rationalLocalization TA sA hTA).pair CX.pair) :
    CY.pairComap CX (ψ.comp (CY.rationalLocalizationHom TA sA hTA)) ≫ CY.hom =
      (CY.rationalLocalization TA sA hTA).pairComap CX ψ ≫
        (CY.rationalLocalization TA sA hTA).hom := by
  rw [CY.pairComap_comp (CY.rationalLocalization TA sA hTA) CX, Category.assoc,
    ← rationalLocalization_hom]

/-- The canonical Huber-pair morphism `C.pair → (C.rationalLocalization T s hT).pair` attached to a
rational localisation of a complete affinoid open is topologically of finite type. -/
theorem isTopologicallyFiniteType_rationalLocalizationHom {X : PreAdicSpace.{u}}
    (C : CompleteAffinoidOpen X) (T : Finset C.Ring) (s : C.Ring)
    (hT : IsOpen (Ideal.span (T : Set C.Ring) : Set C.Ring)) :
    (C.rationalLocalizationHom T s hT).IsTopologicallyFiniteType :=
  isTopologicallyFiniteType_toRationalLocalizationHom _ _ _ C.hom T s hT

/-- Over a complete affinoid open `C` with discrete underlying ring `C.Ring`, any ring-homomorphism
property `R` that respects isomorphisms and holds for localisations away from an element holds for
`(C.rationalLocalizationHom T s hT).toRingHom`. -/
theorem ringHom_prop_rationalLocalizationHom_of_discreteTopology
    {R : ∀ {X Y : Type u} [CommRing X] [CommRing Y], (X →+* Y) → Prop}
    (hiso : RingHom.RespectsIso @R) (hloc : RingHom.HoldsForLocalizationAway @R)
    {X : PreAdicSpace.{u}} (C : CompleteAffinoidOpen X) [DiscreteTopology C.Ring]
    (T : Finset C.Ring) (s : C.Ring) (hT : IsOpen (Ideal.span (T : Set C.Ring) : Set C.Ring)) :
    R (C.rationalLocalizationHom T s hT).toRingHom :=
  ringHom_prop_toRationalLocalizationHom_of_discreteTopology _ _ _ C.hom T s hT hiso hloc

/-- Over a complete affinoid open `C` with discrete underlying ring `C.Ring`, the canonical ring
homomorphism `(C.rationalLocalizationHom T s hT).toRingHom` into the rational localisation
`C.Ring⟨T/s⟩` is algebraically of finite presentation (`RingHom.FinitePresentation`). -/
theorem finitePresentation_rationalLocalizationHom {X : PreAdicSpace.{u}}
    (C : CompleteAffinoidOpen X) [DiscreteTopology C.Ring] (T : Finset C.Ring) (s : C.Ring)
    (hT : IsOpen (Ideal.span (T : Set C.Ring) : Set C.Ring)) :
    (C.rationalLocalizationHom T s hT).toRingHom.FinitePresentation :=
  finitePresentation_toRationalLocalizationHom C.pairOfDefinition C.le_plus C.isSheaf C.hom T s hT

/-- **Composed rational-refinement square**: given a chart square `CZ → CY` over `g : Y ⟶ Z` and
a chart square `(CY.rationalLocalization TB sB hTB) → CX` over `f : X ⟶ Y`, the composite
Huber-pair morphism `β.comp ((CY.rationalLocalizationHom TB sB hTB).comp ψ)` induces a chart
square `CZ → CX` over `f ≫ g`. -/
theorem pairComap_comp_rationalLocalization_sq {X Y Z : PreAdicSpace.{u}}
    {f : X ⟶ Y} {g : Y ⟶ Z} (CZ : CompleteAffinoidOpen Z) (CY : CompleteAffinoidOpen Y)
    {TB : Finset CY.Ring} {sB : CY.Ring}
    (hTB : IsOpen (Ideal.span (TB : Set CY.Ring) : Set CY.Ring))
    (CX : CompleteAffinoidOpen X) (ψ : Pair.Hom CZ.pair CY.pair)
    (β : Pair.Hom (CY.rationalLocalization TB sB hTB).pair CX.pair)
    (hsq_g : CZ.pairComap CY ψ ≫ CZ.hom = CY.hom ≫ g)
    (hsq_f : (CY.rationalLocalization TB sB hTB).pairComap CX β ≫
      (CY.rationalLocalization TB sB hTB).hom = CX.hom ≫ f) :
    CZ.pairComap CX (β.comp ((CY.rationalLocalizationHom TB sB hTB).comp ψ)) ≫ CZ.hom =
      CX.hom ≫ f ≫ g := by
  let CY₁ := CY.rationalLocalization TB sB hTB; let ιB := CY.rationalLocalizationHom TB sB hTB
  calc
    CZ.pairComap CX (β.comp (ιB.comp ψ)) ≫ CZ.hom
      = CY₁.pairComap CX β ≫ CY.pairComap CY₁ ιB ≫ (CZ.pairComap CY ψ ≫ CZ.hom) := by
          simp only [CY₁, ιB, pairComap_comp_assoc]
    _ = CY₁.pairComap CX β ≫ CY.pairComap CY₁ ιB ≫ (CY.hom ≫ g) := by rw [hsq_g]
    _ = (CY₁.pairComap CX β ≫ (CY.pairComap CY₁ ιB ≫ CY.hom)) ≫ g := by simp only [Category.assoc]
    _ = (CY₁.pairComap CX β ≫ CY₁.hom) ≫ g := by rw [← rationalLocalization_hom]
    _ = (CX.hom ≫ f) ≫ g := by rw [hsq_f]
    _ = CX.hom ≫ f ≫ g := by simp only [Category.assoc]

/-- **Lifting a compatible chart over a rational localisation of the source**: given chart squares
`CZ → CY` over `g : Y ⟶ Z` and `CZ → CX` over `f ≫ g` with `x ∈ X` covered by `c₀ ∈ CX` and
`f(x)` covered by `b₀ ∈ CY`, there is a rational localisation `CX₁ = CX.rationalLocalization TC sC`
around `x` and a Huber-pair morphism `φ : CY.pair → CX₁.pair` making the chart square over `f`
commute and satisfying `φ.comp ψ = (CX.rationalLocalizationHom TC sC hTC).comp χ`. -/
theorem exists_rationalLocalization_lift_sq {X Y Z : PreAdicSpace.{u}}
    {f : X ⟶ Y} {g : Y ⟶ Z} {x : X}
    (CZ : CompleteAffinoidOpen Z) (CY : CompleteAffinoidOpen Y) (CX : CompleteAffinoidOpen X)
    (ψ : Pair.Hom CZ.pair CY.pair) (χ : Pair.Hom CZ.pair CX.pair) {b₀ : CY.space}
    (hb₀ : CY.hom.base b₀ = f.base x) {c₀ : CX.space} (hc₀ : CX.hom.base c₀ = x)
    (hsq_g : CZ.pairComap CY ψ ≫ CZ.hom = CY.hom ≫ g)
    (hsq_fg : CZ.pairComap CX χ ≫ CZ.hom = CX.hom ≫ f ≫ g) : ∃ (TC : Finset CX.Ring) (sC : CX.Ring)
      (hTC : IsOpen (Ideal.span (TC : Set CX.Ring) : Set CX.Ring)),
      let CX₁ := CX.rationalLocalization TC sC hTC
      ∃ (φ : Pair.Hom CY.pair CX₁.pair) (c₁ : CX₁.space),
        CX₁.hom.base c₁ = x ∧ CY.pairComap CX₁ φ ≫ CY.hom = CX₁.hom ≫ f ∧
        φ.comp ψ = (CX.rationalLocalizationHom TC sC hTC).comp χ := by
  obtain ⟨TC, sC, hTC, -, c₁, φ, hc₁, hsq_f⟩ :=
    exists_ofRationalLocalization_lift CX.pairOfDefinition CX.le_plus CX.isSheaf CX.hom CY f
      (a₀ := c₀) (d₀ := b₀)
      (by rw [PreAdicSpace.comp_base, TopCat.coe_comp, Function.comp_apply, hc₀]; exact hb₀.symm)
  let CX₁ := CX.rationalLocalization TC sC hTC; let ιC := CX.rationalLocalizationHom TC sC hTC
  have hφψ : φ.comp ψ = ιC.comp χ := by
    apply CZ.pairComap_injective CX₁
    rw [← cancel_mono CZ.hom]
    calc
      CZ.pairComap CX₁ (φ.comp ψ) ≫ CZ.hom
        = CY.pairComap CX₁ φ ≫ (CZ.pairComap CY ψ ≫ CZ.hom) := by simp only [pairComap_comp_assoc]
      _ = CY.pairComap CX₁ φ ≫ (CY.hom ≫ g) := by rw [hsq_g]
      _ = (CY.pairComap CX₁ φ ≫ CY.hom) ≫ g := by simp only [Category.assoc]
      _ = (CX₁.hom ≫ f) ≫ g := by rw [hsq_f]
      _ = CX.pairComap CX₁ ιC ≫ (CX.hom ≫ f ≫ g) := by
          simp only [CX₁, ιC, ofRationalLocalization_hom, Category.assoc]
      _ = CX.pairComap CX₁ ιC ≫ (CZ.pairComap CX χ ≫ CZ.hom) := by rw [hsq_fg]
      _ = CZ.pairComap CX₁ (ιC.comp χ) ≫ CZ.hom := by simp only [pairComap_comp_assoc]
  exact ⟨TC, sC, hTC, φ, c₁, hc₁.trans hc₀, hsq_f, hφψ⟩

end CompleteAffinoidOpen

section DiscreteDescent

open CompleteAffinoidOpen

/-- **Rational-open chart comparison**: given a discrete affinoid open `CX` of `CB.space` whose
image contains the rational basic open `R(TB / sB)` and a commuting chart `α : CA.pair → CX.pair`
over `φ : CA.pair → CB.pair`, pulling back `R(TB / sB)` to `CX` yields a rational localisation
`CX₁` of `CX` whose coordinate ring is isomorphic to
`(ofRationalLocalization CB.pairOfDefinition CB.le_plus CB.isSheaf (𝟙 _) TB sB hTB).Ring`
intertwining the localisation maps. -/
private theorem exists_rationalLocalization_ringEquiv_of_subset
    {X₀ Y₀ : PreAdicSpace.{u}} (CA : CompleteAffinoidOpen X₀) (CB : CompleteAffinoidOpen Y₀)
    (φ : Pair.Hom CA.pair CB.pair) (CX : CompleteAffinoidOpen CB.space) [DiscreteTopology CX.Ring]
    (α : Pair.Hom CA.pair CX.pair) (hsq_α : CA.pairComap CX α = CX.hom ≫ CA.pairComap CB φ)
    (TB : Finset CB.Ring) (sB : CB.Ring)
    (hTB : IsOpen (Ideal.span (TB : Set CB.Ring) : Set CB.Ring))
    (hsub : (spaBasicOpen CB.pair.plus TB sB : Set (spa CB.pair.plus)) ⊆ Set.range CX.hom.base) :
    ∃ (TC : Finset CX.Ring) (sC : CX.Ring)
      (hTC : IsOpen (Ideal.span (TC : Set CX.Ring) : Set CX.Ring))
      (eγ : (CX.rationalLocalization TC sC hTC).Ring ≃+*
        (ofRationalLocalization CB.pairOfDefinition CB.le_plus CB.isSheaf (𝟙 _) TB sB hTB).Ring),
      eγ.toRingHom.comp ((CX.rationalLocalizationHom TC sC hTC).comp α).toRingHom =
        ((toRationalLocalizationHom CB.pairOfDefinition CB.le_plus CB.isSheaf
          (𝟙 _) TB sB hTB).comp φ).toRingHom := by
  classical
  let CT := ofRationalLocalization CB.pairOfDefinition CB.le_plus CB.isSheaf (𝟙 CB.space) TB sB hTB
  let ιB := toRationalLocalizationHom CB.pairOfDefinition CB.le_plus CB.isSheaf (𝟙 _) TB sB hTB
  have hCT_range : Set.range CT.hom.base =
      (spaBasicOpen CB.pair.plus TB sB : Set (spa CB.pair.plus)) := by
    rw [ofRationalLocalization_hom, Category.comp_id]
    exact range_toRationalLocalizationComap_base ..
  let δ := presentationLimitHomPairHom CB.pairOfDefinition CX.pairOfDefinition CB.pair CX.pair
    CB.le_plus CX.le_plus CX.hom
  let TC : Finset CX.Ring := TB.image δ.toRingHom; let sC : CX.Ring := δ.toRingHom sB
  have hTC : IsOpen (Ideal.span (TC : Set CX.Ring) : Set CX.Ring) := isOpen_discrete _
  let CX₁ := CX.rationalLocalization TC sC hTC; let ιC := CX.rationalLocalizationHom TC sC hTC
  have hpre_eq : (spaBasicOpen CX.pair.plus TC sC : Set (spa CX.pair.plus)) =
      CX.hom.base ⁻¹' (spaBasicOpen CB.pair.plus TB sB : Set (spa CB.pair.plus)) := by
    have hCX : CX.hom = CB.pairComap CX δ :=
      (presentationLimitPreAdicSpacePairComap_presentationLimitHomPairHom ..).symm
    rw [hCX, pairComap, presentationLimitPreAdicSpacePairComap_base]
    exact congrArg SetLike.coe (map_spaComapTopHom_obj_spaBasicOpen δ.toRingHom
      δ.continuous_toRingHom δ.map_mem_plus TB sB).symm
  have hrange_eq : Set.range CX₁.hom.base = Set.range CT.hom.base := by
    rw [range_ofRationalLocalization_hom_base, hpre_eq, hCT_range]
    exact Set.image_preimage_eq_iff.mpr hsub
  let eCB := IsOpenImmersion.isoOfRangeEq CX₁.hom CT.hom hrange_eq
  let eγ := ringEquivOfIso CT CX₁ eCB.symm
  let γ := presentationLimitHomPairHom CX₁.pairOfDefinition CT.pairOfDefinition
    CX₁.pair CT.pair CX₁.le_plus CT.le_plus eCB.symm.hom
  have heCB' : eCB.symm.hom ≫ CX₁.hom = CT.hom := IsOpenImmersion.isoOfRangeEq_inv_comp ..
  have hγ : CX₁.pairComap CT γ = eCB.symm.hom :=
    presentationLimitPreAdicSpacePairComap_presentationLimitHomPairHom ..
  have hpath : γ.comp (ιC.comp α) = ιB.comp φ := by
    apply CA.pairComap_injective CT
    calc
      CA.pairComap CT (γ.comp (ιC.comp α))
        = eCB.symm.hom ≫ CX.pairComap CX₁ ιC ≫ CA.pairComap CX α := by
            rw [CA.pairComap_comp CX₁ CT, CA.pairComap_comp CX CX₁, hγ]
      _ = eCB.symm.hom ≫ CX.pairComap CX₁ ιC ≫ CX.hom ≫ CA.pairComap CB φ := by rw [hsq_α]
      _ = (eCB.symm.hom ≫ (CX.pairComap CX₁ ιC ≫ CX.hom)) ≫ CA.pairComap CB φ := by
            simp only [Category.assoc]
      _ = (eCB.symm.hom ≫ CX₁.hom) ≫ CA.pairComap CB φ := by rw [← rationalLocalization_hom]
      _ = CT.hom ≫ CA.pairComap CB φ := by rw [heCB']
      _ = CB.pairComap CT ιB ≫ CA.pairComap CB φ := by
            rw [ofRationalLocalization_hom, Category.comp_id]
      _ = CA.pairComap CT (ιB.comp φ) := by rw [CA.pairComap_comp CB CT]
  refine ⟨TC, sC, hTC, eγ, ?_⟩
  rw [RingEquiv.toRingHom_eq_coe, coe_ringEquivOfIso, ← Pair.Hom.toRingHom_comp]
  exact congrArg Pair.Hom.toRingHom hpath

/-- Pointwise discrete rational-chart comparison: given a rational chart `CY₁ → CX` covering a
point `y` of `Spa(T)` over a discrete Huber-pair morphism `φ : S → T`, with `CX.Ring` discrete and
`R β.toRingHom`, there exists a rational basic open `R(TB / sB)` containing `y` on which
`(algebraMap B (Localization.Away sB)).comp φ.toRingHom` satisfies `R`. -/
private theorem exists_away_comp_of_rational_chart_discrete
    {R : ∀ {X Y : Type u} [CommRing X] [CommRing Y], (X →+* Y) → Prop}
    (hcomp : RingHom.StableUnderComposition @R) (hiso : RingHom.RespectsIso @R)
    (hloc : RingHom.HoldsForLocalizationAway @R)
    {A B : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [DiscreteTopology A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [DiscreteTopology B]
    {S : Pair A} (P : PairOfDefinition A) (hP : P.ringOfDefinition ≤ S.plus)
    (hsheafA : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa S.plus))
      (presentationLimitPresheaf P S.plus))
    {T : Pair B} (P' : PairOfDefinition B) (hP' : P'.ringOfDefinition ≤ T.plus)
    (hsheafB : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa T.plus))
      (presentationLimitPresheaf P' T.plus)) (φ : Pair.Hom S T)
    (y : presentationLimitPreAdicSpace P' T.plus
      T.isRingOfIntegralElements.isPowerBounded_of_mem hP')
    (TA : Finset A) (sA : A) (hTA : IsOpen (Ideal.span (TA : Set A) : Set A))
    (CX : CompleteAffinoidOpen (presentationLimitPreAdicSpace P' T.plus
      T.isRingOfIntegralElements.isPowerBounded_of_mem hP')) [DiscreteTopology CX.Ring]
    (β : Pair.Hom (ofRationalLocalization P hP hsheafA (𝟙 _) TA sA hTA).pair CX.pair)
    (hRβ : R β.toRingHom) (c₀ : CX.space) (hc₀ : CX.hom.base c₀ = y)
    (hsq : (ofRationalLocalization P hP hsheafA (𝟙 _) TA sA hTA).pairComap CX β ≫
      (ofRationalLocalization P hP hsheafA (𝟙 _) TA sA hTA).hom =
      CX.hom ≫ presentationLimitPreAdicSpacePairComap P P' hP hP' hsheafB φ) :
    ∃ (TB : Finset B) (sB : B), y.val ∈ rationalSubset T.plus TB sB ∧
      R ((algebraMap B (Localization.Away sB)).comp φ.toRingHom) := by
  classical
  let CA := ofDiscrete S P hP hsheafA
  let CB := ofDiscrete T P' hP' hsheafB
  let ιA := toRationalLocalizationHom P hP hsheafA (𝟙 _) TA sA hTA
  have hsq_α : CA.pairComap CX (β.comp ιA) = CX.hom ≫ CA.pairComap CB φ :=
    (Category.comp_id _).symm.trans
      ((CA.pairComap_comp_rationalLocalizationHom_comp_hom CX β).trans hsq)
  let OB : Opens (presentationLimitPreAdicSpace P' T.plus
      T.isRingOfIntegralElements.isPowerBounded_of_mem hP') :=
    ⟨Set.range CX.hom.base, CX.hom.isOpenEmbedding.isOpen_range⟩
  have hyO : y ∈ OB := Set.mem_range.mpr ⟨c₀, hc₀⟩
  obtain ⟨RB, hRB, hyR, hRBO⟩ := Opens.isBasis_iff_nbhd.mp (isBasis_spaRationalOpens T.plus) hyO
  obtain ⟨TB, sB, hTB, rfl⟩ := mem_spaRationalOpens_iff_exists_spaBasicOpen.mp hRB
  obtain ⟨TC, sC, hTC, eγ, he_comp⟩ :=
    exists_rationalLocalization_ringEquiv_of_subset CA CB φ CX (β.comp ιA) hsq_α TB sB hTB hRBO
  let ιC := CX.rationalLocalizationHom TC sC hTC
  let ιB := toRationalLocalizationHom P' hP' hsheafB (𝟙 _) TB sB hTB
  let eB := ofRationalLocalizationAwayEquiv P' hP' hsheafB (𝟙 _) TB sB hTB; let e := eγ.trans eB
  have hmap_eq : (algebraMap B (Localization.Away sB)).comp φ.toRingHom =
      e.toRingHom.comp (ιC.comp (β.comp ιA)).toRingHom := by
    calc
      (algebraMap B (Localization.Away sB)).comp φ.toRingHom
        = (eB.toRingHom.comp ιB.toRingHom).comp φ.toRingHom := by
            rw [RingEquiv.toRingHom_eq_coe,
              ofRationalLocalizationAwayEquiv_comp_toRationalLocalizationHom]
      _ = eB.toRingHom.comp (ιB.comp φ).toRingHom := by
            rw [RingHom.comp_assoc, Pair.Hom.toRingHom_comp]
      _ = eB.toRingHom.comp (eγ.toRingHom.comp (ιC.comp (β.comp ιA)).toRingHom) := by rw [he_comp]
      _ = (eB.toRingHom.comp eγ.toRingHom).comp (ιC.comp (β.comp ιA)).toRingHom := by
            rw [← RingHom.comp_assoc]
      _ = e.toRingHom.comp (ιC.comp (β.comp ιA)).toRingHom := by rw [← RingEquiv.toRingHom_trans']
  have hRA : R ιA.toRingHom :=
    ringHom_prop_toRationalLocalizationHom_of_discreteTopology _ _ _ _ _ _ _ hiso hloc
  have hRC := CX.ringHom_prop_rationalLocalizationHom_of_discreteTopology hiso hloc TC sC hTC
  refine ⟨TB, sB, mem_spaBasicOpen.mp hyR, ?_⟩
  rw [hmap_eq, Pair.Hom.toRingHom_comp, Pair.Hom.toRingHom_comp]
  exact hiso.1 _ e (hcomp _ _ (hcomp _ _ hRA hRβ) hRC)

/-- **Discrete rational-chart descent for local ring-homomorphism properties**: let `R` be a
property of ring homomorphisms that is stable under composition, respects isomorphisms, holds for
localisations away from an element, and satisfies `RingHom.OfLocalizationSpanTarget` (for instance
`RingHom.FiniteType` or `RingHom.FinitePresentation`). Let `φ : S → T` be a morphism of discrete
Huber pairs with sheafy presentations `P, P'`. If every point of `Spa(T)` is covered by a discrete
complete affinoid open chart `CX` over some rational localisation `R(TA / sA)` of `Spa(S)` whose
induced ring map satisfies `R`, then `R φ.toRingHom` holds globally. -/
theorem ringHom_prop_of_forall_rational_chart_discrete
    {R : ∀ {X Y : Type u} [CommRing X] [CommRing Y], (X →+* Y) → Prop}
    (hcomp : RingHom.StableUnderComposition @R) (hiso : RingHom.RespectsIso @R)
    (hloc : RingHom.HoldsForLocalizationAway @R) (hspan : RingHom.OfLocalizationSpanTarget @R)
    {A B : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [DiscreteTopology A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [DiscreteTopology B]
    {S : Pair A} (P : PairOfDefinition A) (hP : P.ringOfDefinition ≤ S.plus)
    (hsheafA : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa S.plus))
      (presentationLimitPresheaf P S.plus))
    {T : Pair B} (P' : PairOfDefinition B) (hP' : P'.ringOfDefinition ≤ T.plus)
    (hsheafB : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa T.plus))
      (presentationLimitPresheaf P' T.plus)) (φ : Pair.Hom S T)
    (hchart : ∀ y : presentationLimitPreAdicSpace P' T.plus
        T.isRingOfIntegralElements.isPowerBounded_of_mem hP',
      ∃ (TA : Finset A) (sA : A) (hTA : IsOpen (Ideal.span (TA : Set A) : Set A)),
        let CY₁ := ofRationalLocalization P hP hsheafA (𝟙 _) TA sA hTA
        ∃ (CX : CompleteAffinoidOpen (presentationLimitPreAdicSpace P' T.plus
            T.isRingOfIntegralElements.isPowerBounded_of_mem hP')) (_ : DiscreteTopology CX.Ring)
          (β : Pair.Hom CY₁.pair CX.pair) (_ : R β.toRingHom) (c₀ : CX.space), CX.hom.base c₀ = y ∧
          CY₁.pairComap CX β ≫ CY₁.hom =
            CX.hom ≫ presentationLimitPreAdicSpacePairComap P P' hP hP' hsheafB φ) :
    R φ.toRingHom := by
  classical
  have hpt (y : spa T.plus) : ∃ (TB : Finset B) (sB : B), y.val ∈ rationalSubset T.plus TB sB ∧
      R ((algebraMap B (Localization.Away sB)).comp φ.toRingHom) := by
    obtain ⟨TA, sA, hTA, CX, _, β, hRβ, c₀, hc₀, hsq⟩ := hchart y
    exact exists_away_comp_of_rational_chart_discrete hcomp hiso hloc P hP hsheafA P' hP' hsheafB
      φ y TA sA hTA CX β hRβ c₀ hc₀ hsq
  choose TB sB hyR hR using hpt
  have : IsLocalization.Away (1 : B) B := IsLocalization.self (by rintro _ ⟨n, rfl⟩; simp)
  have hcov : rationalSubset T.plus ({1} : Finset B) 1 ⊆
      ⋃ y : spa T.plus, rationalSubset T.plus (TB y) (sB y) := fun v hv ↦ by
    rw [rationalSubset_singleton_one] at hv; exact Set.mem_iUnion.mpr ⟨⟨v, hv⟩, hyR ⟨v, hv⟩⟩
  have hspan_top : Ideal.span (Set.range sB) = ⊤ := by
    simpa using span_eq_top_of_rationalSubset_subset_iUnion (Aplus := T.plus) (T := {1}) (s := 1) B
      (fun _ _ ↦ isOpen_discrete _) hcov
  exact hspan φ.toRingHom (Set.range sB) hspan_top (by rintro ⟨_, y, rfl⟩; exact hR y)

end DiscreteDescent

end TauCeti.PreAdicSpace
