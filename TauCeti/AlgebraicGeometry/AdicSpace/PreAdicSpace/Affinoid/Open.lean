/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LocalProperties.Basic
public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.Affinoid.PairEquiv
public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.ChartLocally
public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.RationalOpen
public import TauCeti.RingTheory.Huber.LocalizationTopology.BaseChange

import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.BaseChange
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.RationalSubset.Discrete
import TauCeti.RingTheory.Huber.LocalizationTopology.Discrete

/-!
# Complete affinoid open immersions and rational chart refinement

This module bundles a complete Hausdorff sheafy affinoid open immersion `Spa(A, A⁺) ⟶ X` into a
pre-adic space `X` as `TauCeti.PreAdicSpace.CompleteAffinoidOpen X` and develops the
presentation-level chart API shared across local morphism properties (such as morphisms locally of
weakly finite type, locally of finite type, and locally of finite presentation):

* **Categorical and open-restriction interface**: `CompleteAffinoidOpen.space`,
  `CompleteAffinoidOpen.pairComap` (with identity and composition laws `pairComap_id` and
  `pairComap_comp`), `CompleteAffinoidOpen.ofRestrictIso`
  (packaging an affinoid restriction isomorphism `X|_U ≅ Spa(A, A⁺)` as an open immersion),
  `CompleteAffinoidOpen.compOpenImmersion`, and `CompleteAffinoidOpen.ringEquivOfIso` (extracting
  the global-sections `RingEquiv` from an isomorphism `C₁.space ≅ C₂.space`).
* **Rational localisation shrinking and lifting**: `CompleteAffinoidOpen.ofRationalLocalization`,
  `CompleteAffinoidOpen.toRationalLocalizationHom`, `CompleteAffinoidOpen.rationalLocalization`,
  and `CompleteAffinoidOpen.rationalLocalizationHom`, together with
  `CompleteAffinoidOpen.exists_ofRationalLocalization_lift`,
  `CompleteAffinoidOpen.exists_rationalLocalization_lift_sq`, and the composed refinement-square
  identity `CompleteAffinoidOpen.pairComap_comp_rationalLocalization_sq`.
* **Chart completion via `{1} / 1`**: `chartLocally.exists_complete_chart` and
  `chartLocally.exists_complete_openImmersion_chart` upgrade any chart-local property `Q` preserved
  by `{1} / 1` rational base change so that both the target and source rings of the chart are
  complete and Hausdorff.
* **Discrete rational-chart descent**: `ringHom_prop_of_forall_rational_chart_discrete` descends
  any ring-homomorphism property `R` that is stable under composition, respects isomorphisms, holds
  for localisations away from an element, and satisfies `RingHom.OfLocalizationSpanTarget` (in
  particular `RingHom.FiniteType` and `RingHom.FinitePresentation`) from pointwise discrete
  rational charts over `Spa(A, A⁺)` to the global ring homomorphism `φ : A →+* B`.

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

/-- Package an open restriction isomorphism `X|_U ≅ Spa(A, A⁺)` for a complete Hausdorff sheafy
Huber pair `(A, A⁺)` as a `CompleteAffinoidOpen X` with immersion `eU.inv ≫ X.ofRestrict _`. -/
@[expose]
noncomputable def ofRestrictIso {X : PreAdicSpace.{u}} {U : Opens X}
    {A : Type u} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
    [CompleteSpace A] [T2Space A] [IsHuberRing A]
    (S : Pair A) (P : PairOfDefinition A) (hP : P.ringOfDefinition ≤ S.plus)
    (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa S.plus))
      (presentationLimitPresheaf P S.plus))
    (eU : X.restrict U.isOpenEmbedding ≅
      presentationLimitPreAdicSpace P S.plus S.isRingOfIntegralElements.isPowerBounded_of_mem hP) :
    CompleteAffinoidOpen X where
  Ring := A
  pair := S
  pairOfDefinition := P
  le_plus := hP
  isSheaf := hsheaf
  hom := eU.inv ≫ X.ofRestrict U.isOpenEmbedding
  isOpenImmersion := IsOpenImmersion.comp _ _

/-- The open immersion of `ofRestrictIso` is `eU.inv ≫ X.ofRestrict U.isOpenEmbedding`. -/
@[simp]
theorem ofRestrictIso_hom {X : PreAdicSpace.{u}} {U : Opens X}
    {A : Type u} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
    [CompleteSpace A] [T2Space A] [IsHuberRing A]
    (S : Pair A) (P : PairOfDefinition A) (hP : P.ringOfDefinition ≤ S.plus)
    (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa S.plus))
      (presentationLimitPresheaf P S.plus))
    (eU : X.restrict U.isOpenEmbedding ≅
      presentationLimitPreAdicSpace P S.plus S.isRingOfIntegralElements.isPowerBounded_of_mem hP) :
    (ofRestrictIso S P hP hsheaf eU).hom = eU.inv ≫ X.ofRestrict U.isOpenEmbedding :=
  rfl

/-- On points of `U`, the open immersion of `ofRestrictIso` sends `eU.hom.base ⟨x, hx⟩` back to
`x`. -/
theorem ofRestrictIso_hom_base {X : PreAdicSpace.{u}} {U : Opens X}
    {A : Type u} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
    [CompleteSpace A] [T2Space A] [IsHuberRing A]
    (S : Pair A) (P : PairOfDefinition A) (hP : P.ringOfDefinition ≤ S.plus)
    (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa S.plus))
      (presentationLimitPresheaf P S.plus))
    (eU : X.restrict U.isOpenEmbedding ≅
      presentationLimitPreAdicSpace P S.plus S.isRingOfIntegralElements.isPowerBounded_of_mem hP)
    {x : X} (hx : x ∈ U) :
    (ofRestrictIso S P hP hsheaf eU).hom.base (eU.hom.base ⟨x, hx⟩) = x := by
  let u : X.restrict U.isOpenEmbedding := ⟨x, hx⟩
  have h : eU.hom ≫ eU.inv ≫ X.ofRestrict U.isOpenEmbedding = X.ofRestrict U.isOpenEmbedding :=
    Iso.hom_inv_id_assoc eU _
  have hpt := congrArg (fun m : X.restrict U.isOpenEmbedding ⟶ X ↦ m.base u) h
  rw [PreAdicSpace.comp_base, TopCat.coe_comp, Function.comp_apply,
    PreAdicSpace.ofRestrict_base] at hpt
  exact hpt

/-- The induced morphism `pairComap` between two `ofRestrictIso` charts is
`presentationLimitPreAdicSpacePairComap`. -/
@[simp]
theorem ofRestrictIso_pairComap {X Y : PreAdicSpace.{u}} {U : Opens X} {V : Opens Y}
    {A : Type u} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
    [CompleteSpace A] [T2Space A] [IsHuberRing A] (S : Pair A) (P : PairOfDefinition A)
    (hP : P.ringOfDefinition ≤ S.plus)
    (hsheafA : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa S.plus))
      (presentationLimitPresheaf P S.plus))
    (eV : Y.restrict V.isOpenEmbedding ≅
      presentationLimitPreAdicSpace P S.plus S.isRingOfIntegralElements.isPowerBounded_of_mem hP)
    {B : Type u} [CommRing B] [UniformSpace B] [IsUniformAddGroup B] [IsTopologicalRing B]
    [CompleteSpace B] [T2Space B] [IsHuberRing B] (T : Pair B) (P' : PairOfDefinition B)
    (hP' : P'.ringOfDefinition ≤ T.plus)
    (hsheafB : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa T.plus))
      (presentationLimitPresheaf P' T.plus))
    (eU : X.restrict U.isOpenEmbedding ≅
      presentationLimitPreAdicSpace P' T.plus T.isRingOfIntegralElements.isPowerBounded_of_mem hP')
    (φ : Pair.Hom S T) :
    (ofRestrictIso S P hP hsheafA eV).pairComap (ofRestrictIso T P' hP' hsheafB eU) φ =
      presentationLimitPreAdicSpacePairComap P P' hP hP' hsheafB φ :=
  rfl

/-- A chart factorisation `X.ofRestrict _ ≫ f = eU.hom ≫ Spa(φ) ≫ eV.inv ≫ Y.ofRestrict _`
translates directly into a commuting open-immersion square between `ofRestrictIso` charts. -/
theorem ofRestrictIso_pairComap_comp_hom {X Y : PreAdicSpace.{u}} {U : Opens X} {V : Opens Y}
    {A : Type u} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
    [CompleteSpace A] [T2Space A] [IsHuberRing A] (S : Pair A) (P : PairOfDefinition A)
    (hP : P.ringOfDefinition ≤ S.plus)
    (hsheafA : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa S.plus))
      (presentationLimitPresheaf P S.plus))
    (eV : Y.restrict V.isOpenEmbedding ≅
      presentationLimitPreAdicSpace P S.plus S.isRingOfIntegralElements.isPowerBounded_of_mem hP)
    {B : Type u} [CommRing B] [UniformSpace B] [IsUniformAddGroup B] [IsTopologicalRing B]
    [CompleteSpace B] [T2Space B] [IsHuberRing B] (T : Pair B) (P' : PairOfDefinition B)
    (hP' : P'.ringOfDefinition ≤ T.plus)
    (hsheafB : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa T.plus))
      (presentationLimitPresheaf P' T.plus))
    (eU : X.restrict U.isOpenEmbedding ≅
      presentationLimitPreAdicSpace P' T.plus T.isRingOfIntegralElements.isPowerBounded_of_mem hP')
    (φ : Pair.Hom S T) {f : X ⟶ Y}
    (hfac : X.ofRestrict U.isOpenEmbedding ≫ f =
      eU.hom ≫ presentationLimitPreAdicSpaceComap φ.toRingHom φ.continuous_toRingHom
        φ.map_mem_plus S.isRingOfIntegralElements.isPowerBounded_of_mem
        T.isRingOfIntegralElements.isPowerBounded_of_mem hP hP' hsheafB ≫
        eV.inv ≫ Y.ofRestrict V.isOpenEmbedding) :
    (ofRestrictIso S P hP hsheafA eV).pairComap (ofRestrictIso T P' hP' hsheafB eU) φ ≫
        (ofRestrictIso S P hP hsheafA eV).hom =
      (ofRestrictIso T P' hP' hsheafB eU).hom ≫ f := by
  -- `ofRestrictIso` preserves `space` definitionally; `rfl` aligns the implicit objects of `≫`.
  have h1 : (ofRestrictIso S P hP hsheafA eV).pairComap (ofRestrictIso T P' hP' hsheafB eU) φ ≫
      (ofRestrictIso S P hP hsheafA eV).hom =
      presentationLimitPreAdicSpacePairComap P P' hP hP' hsheafB φ ≫
        eV.inv ≫ Y.ofRestrict V.isOpenEmbedding := by
    rw [ofRestrictIso_pairComap, ofRestrictIso_hom]
    rfl
  have h2 : presentationLimitPreAdicSpacePairComap P P' hP hP' hsheafB φ ≫
      eV.inv ≫ Y.ofRestrict V.isOpenEmbedding =
      (eU.inv ≫ X.ofRestrict U.isOpenEmbedding) ≫ f := by
    rw [presentationLimitPreAdicSpacePairComap_def, Category.assoc, hfac, Iso.inv_hom_id_assoc]
  have h3 : (eU.inv ≫ X.ofRestrict U.isOpenEmbedding) ≫ f =
      (ofRestrictIso T P' hP' hsheafB eU).hom ≫ f := by
    rw [ofRestrictIso_hom]
    rfl
  exact h1.trans (h2.trans h3)

/-- Postcompose a `CompleteAffinoidOpen X` with an open immersion `g : X ⟶ Y` to obtain a
`CompleteAffinoidOpen Y` with the same underlying complete Hausdorff Huber pair. -/
@[expose]
noncomputable def compOpenImmersion {X Y : PreAdicSpace.{u}} (C : CompleteAffinoidOpen X)
    (g : X ⟶ Y) [IsOpenImmersion g] : CompleteAffinoidOpen Y where
  Ring := C.Ring
  pair := C.pair
  pairOfDefinition := C.pairOfDefinition
  le_plus := C.le_plus
  isSheaf := C.isSheaf
  hom := C.hom ≫ g
  isOpenImmersion := IsOpenImmersion.comp _ _

/-- The open immersion of `C.compOpenImmersion g` is `C.hom ≫ g`. -/
@[simp]
theorem compOpenImmersion_hom {X Y : PreAdicSpace.{u}} (C : CompleteAffinoidOpen X)
    (g : X ⟶ Y) [IsOpenImmersion g] : (C.compOpenImmersion g).hom = C.hom ≫ g :=
  rfl

/-- On underlying points, `(C.compOpenImmersion g).hom.base` acts as `g.base (C.hom.base x)`. -/
theorem compOpenImmersion_hom_base {X Y : PreAdicSpace.{u}} (C : CompleteAffinoidOpen X)
    (g : X ⟶ Y) [IsOpenImmersion g] (x : C.space) :
    (C.compOpenImmersion g).hom.base x = g.base (C.hom.base x) := by
  have h : (C.hom ≫ g).base x = g.base (C.hom.base x) := by
    rw [PreAdicSpace.comp_base, TopCat.coe_comp, Function.comp_apply]
  exact h

/-- Postcomposing the target chart with an open immersion `g` transforms
`CY.pairComap CX φ ≫ CY.hom` by postcomposing with `g`. -/
theorem pairComap_compOpenImmersion_left_comp_hom {X Y Y' : PreAdicSpace.{u}}
    (CY : CompleteAffinoidOpen Y) (CX : CompleteAffinoidOpen X) (g : Y ⟶ Y')
    [IsOpenImmersion g] (φ : Pair.Hom CY.pair CX.pair) :
    (CY.compOpenImmersion g).pairComap CX φ ≫ (CY.compOpenImmersion g).hom =
      CY.pairComap CX φ ≫ CY.hom ≫ g :=
  rfl

/-- A commuting square with source chart `CX.compOpenImmersion g` and morphism `f : X' ⟶ Z`
is equivalent to the corresponding square for `CX` and `g ≫ f`. -/
theorem pairComap_compOpenImmersion_right_eq_comp_iff {X X' Y Z : PreAdicSpace.{u}}
    (CY : CompleteAffinoidOpen Y) (CX : CompleteAffinoidOpen X) (g : X ⟶ X')
    [IsOpenImmersion g] (φ : Pair.Hom CY.pair CX.pair) (f : X' ⟶ Z) (h : CY.space ⟶ Z) :
    CY.pairComap (CX.compOpenImmersion g) φ ≫ h = (CX.compOpenImmersion g).hom ≫ f ↔
      CY.pairComap CX φ ≫ h = CX.hom ≫ g ≫ f :=
  ⟨fun H ↦ H.trans (Category.assoc CX.hom g f),
    fun H ↦ H.trans (Category.assoc CX.hom g f).symm⟩

/-- An isomorphism `e : C₁.space ≅ C₂.space` between complete Hausdorff affinoid pre-adic spaces
induces a ring isomorphism `C₂.Ring ≃+* C₁.Ring` on global sections via
`presentationLimitHomPairHom`. -/
noncomputable def ringEquivOfIso {X Y : PreAdicSpace.{u}} (C₁ : CompleteAffinoidOpen X)
    (C₂ : CompleteAffinoidOpen Y) (e : C₁.space ≅ C₂.space) : C₂.Ring ≃+* C₁.Ring :=
  let φ := presentationLimitHomPairHom C₂.pairOfDefinition C₁.pairOfDefinition
    C₂.pair C₁.pair C₂.le_plus C₁.le_plus e.hom
  let ψ := presentationLimitHomPairHom C₁.pairOfDefinition C₂.pairOfDefinition
    C₁.pair C₂.pair C₁.le_plus C₂.le_plus e.inv
  RingEquiv.ofRingHom φ.toRingHom ψ.toRingHom
    (by
      rw [← Pair.Hom.toRingHom_comp,
        ← presentationLimitHomPairHom_comp C₁.pairOfDefinition C₂.pairOfDefinition
          C₁.pairOfDefinition C₁.pair C₂.pair C₁.pair C₁.le_plus C₂.le_plus C₁.le_plus e.hom e.inv,
        e.hom_inv_id, presentationLimitHomPairHom_id, Pair.Hom.toRingHom_id])
    (by
      rw [← Pair.Hom.toRingHom_comp,
        ← presentationLimitHomPairHom_comp C₂.pairOfDefinition C₁.pairOfDefinition
          C₂.pairOfDefinition C₂.pair C₁.pair C₂.pair C₂.le_plus C₁.le_plus C₂.le_plus e.inv e.hom,
        e.inv_hom_id, presentationLimitHomPairHom_id, Pair.Hom.toRingHom_id])

/-- The underlying ring homomorphism of `ringEquivOfIso C₁ C₂ e` is the global-sections ring map
induced by `e.hom`. -/
@[simp]
theorem coe_ringEquivOfIso {X Y : PreAdicSpace.{u}} (C₁ : CompleteAffinoidOpen X)
    (C₂ : CompleteAffinoidOpen Y) (e : C₁.space ≅ C₂.space) :
    (ringEquivOfIso C₁ C₂ e : C₂.Ring →+* C₁.Ring) =
      (presentationLimitHomPairHom C₂.pairOfDefinition C₁.pairOfDefinition
        C₂.pair C₁.pair C₂.le_plus C₁.le_plus e.hom).toRingHom := by
  ext x
  rfl

section OfRationalLocalization

variable {Y : PreAdicSpace.{u}} {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsHuberRing A] {S : Pair A} (P : PairOfDefinition A) (hP : P.ringOfDefinition ≤ S.plus)
  (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa S.plus))
    (presentationLimitPresheaf P S.plus))
  (kY : presentationLimitPreAdicSpace P S.plus
    S.isRingOfIntegralElements.isPowerBounded_of_mem hP ⟶ Y) [IsOpenImmersion kY]
  (T : Finset A) (s : A) (hT : IsOpen (Ideal.span (T : Set A) : Set A))

/-- Complete affinoid open obtained by restricting an affinoid open immersion `kY : Spa(S) ⟶ Y`
to the rational subset `R(T / s)`. -/
@[expose]
noncomputable def ofRationalLocalization : CompleteAffinoidOpen Y :=
  let L := Localization.Away s
  let hden := P.hasDenominatorPower_of_isOpen_span T s L hT
  letI := P.locUniformSpace T s L hden
  haveI := P.isUniformAddGroup_locUniformSpace T s L hden
  haveI := P.isTopologicalRing_locUniformSpace T s L hden
  haveI := P.isHuberRing_completion_locTopology T s L hden
  let S₁ := P.rationalLocalizationPair S hP T s L hden
  let P₁ := P.completionLocalization T s L hden
  have hP₁ : P₁.ringOfDefinition ≤ S₁.plus := by
    rw [rationalLocalizationPair_plus]
    exact P.completionLocalization_ringOfDefinition_le_completedPlusSubring S.plus hP T s L hden
  have hsheaf₁ := isSheaf_presentationLimitPresheaf_rationalLocalizationPair P S hP T s L hden hT
    hsheaf
  let ι := presentationLimitPreAdicSpacePairComap P P₁ hP hP₁ hsheaf₁
    (P.toCompletionLocHom S hP T s L hden)
  haveI : IsOpenImmersion ι := by
    dsimp only [ι]
    rw [presentationLimitPreAdicSpacePairComap_def]
    exact isOpenImmersion_presentationLimitPreAdicSpaceComap_toCompletionLocHom P hP T s L hden hT
      hsheaf₁
  { Ring := UniformSpace.Completion L, pair := S₁, pairOfDefinition := P₁, le_plus := hP₁,
    isSheaf := hsheaf₁, hom := ι ≫ kY, isOpenImmersion := IsOpenImmersion.comp ι kY }

/-- The underlying ring of `ofRationalLocalization` is
`UniformSpace.Completion (Localization.Away s)` with its rational-localisation uniformity. -/
theorem ofRationalLocalization_Ring :
    let L := Localization.Away s
    let hden := P.hasDenominatorPower_of_isOpen_span T s L hT
    letI := P.locUniformSpace T s L hden
    (ofRationalLocalization P hP hsheaf kY T s hT).Ring = UniformSpace.Completion L :=
  rfl

/-- The underlying Huber pair of `ofRationalLocalization` is
`P.rationalLocalizationPair S hP T s (Localization.Away s) _`. -/
theorem ofRationalLocalization_pair :
    let L := Localization.Away s
    let hden := P.hasDenominatorPower_of_isOpen_span T s L hT
    letI := P.locUniformSpace T s L hden
    letI := P.isUniformAddGroup_locUniformSpace T s L hden
    letI := P.isTopologicalRing_locUniformSpace T s L hden
    letI := P.isHuberRing_completion_locTopology T s L hden
    (ofRationalLocalization P hP hsheaf kY T s hT).pair =
      P.rationalLocalizationPair S hP T s L hden :=
  rfl

/-- The pair of definition of `ofRationalLocalization` is
`P.completionLocalization T s (Localization.Away s) _`. -/
theorem ofRationalLocalization_pairOfDefinition :
    let L := Localization.Away s
    let hden := P.hasDenominatorPower_of_isOpen_span T s L hT
    letI := P.locUniformSpace T s L hden
    letI := P.isUniformAddGroup_locUniformSpace T s L hden
    letI := P.isTopologicalRing_locUniformSpace T s L hden
    (ofRationalLocalization P hP hsheaf kY T s hT).pairOfDefinition =
      P.completionLocalization T s L hden :=
  rfl

/-- Canonical Huber-pair morphism `S → (ofRationalLocalization P hP hsheaf kY T s hT).pair` into
the completed rational localisation at `R(T / s)`. -/
@[expose]
noncomputable def toRationalLocalizationHom :
    Pair.Hom S (ofRationalLocalization P hP hsheaf kY T s hT).pair :=
  let L := Localization.Away s
  let hden := P.hasDenominatorPower_of_isOpen_span T s L hT
  letI := P.locUniformSpace T s L hden
  haveI := P.isUniformAddGroup_locUniformSpace T s L hden
  haveI := P.isTopologicalRing_locUniformSpace T s L hden
  haveI := P.isHuberRing_completion_locTopology T s L hden
  P.toCompletionLocHom S hP T s L hden

/-- Unfolding lemma identifying `toRationalLocalizationHom` with
`PairOfDefinition.toCompletionLocHom` at `Localization.Away s`. -/
theorem toRationalLocalizationHom_def :
    let L := Localization.Away s
    let hden := P.hasDenominatorPower_of_isOpen_span T s L hT
    letI := P.locUniformSpace T s L hden
    letI := P.isUniformAddGroup_locUniformSpace T s L hden
    letI := P.isTopologicalRing_locUniformSpace T s L hden
    letI := P.isHuberRing_completion_locTopology T s L hden
    toRationalLocalizationHom P hP hsheaf kY T s hT = P.toCompletionLocHom S hP T s L hden :=
  rfl

/-- Open immersion `(ofRationalLocalization ...).space ⟶ Spa(S)` induced by
`toRationalLocalizationHom`. -/
noncomputable abbrev toRationalLocalizationComap :
    (ofRationalLocalization P hP hsheaf kY T s hT).space ⟶
      presentationLimitPreAdicSpace P S.plus S.isRingOfIntegralElements.isPowerBounded_of_mem hP :=
  presentationLimitPreAdicSpacePairComap P
    (ofRationalLocalization P hP hsheaf kY T s hT).pairOfDefinition hP
    (ofRationalLocalization P hP hsheaf kY T s hT).le_plus
    (ofRationalLocalization P hP hsheaf kY T s hT).isSheaf
    (toRationalLocalizationHom P hP hsheaf kY T s hT)

/-- The open immersion of `ofRationalLocalization` factors as `toRationalLocalizationComap ≫ kY`. -/
@[reassoc, simp]
theorem ofRationalLocalization_hom :
    (ofRationalLocalization P hP hsheaf kY T s hT).hom =
      toRationalLocalizationComap P hP hsheaf kY T s hT ≫ kY :=
  rfl

/-- The image of `toRationalLocalizationComap` in `Spa(S)` is the rational basic open
`spaBasicOpen S.plus T s`. -/
theorem range_toRationalLocalizationComap_base :
    Set.range (toRationalLocalizationComap P hP hsheaf kY T s hT).base =
      (spaBasicOpen S.plus T s : Set (spa S.plus)) := by
  rw [toRationalLocalizationComap, presentationLimitPreAdicSpacePairComap_def]
  exact range_presentationLimitPreAdicSpaceComap_toCompletionLocHom_base P hP T s
    (Localization.Away s) (P.hasDenominatorPower_of_isOpen_span T s (Localization.Away s) hT) _

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
      D.hom.isOpenEmbedding.isOpen_range.preimage (kY ≫ g).base.hom.2⟩
  have ha₀O : a₀ ∈ OA := ⟨d₀, had.symm⟩
  obtain ⟨RA, hRA, ha₀R, hRAO⟩ := Opens.isBasis_iff_nbhd.mp (isBasis_spaRationalOpens S.plus) ha₀O
  obtain ⟨T, s, hT, rfl⟩ := mem_spaRationalOpens_iff_exists_spaBasicOpen.mp hRA
  refine ⟨T, s, hT, ha₀R, ?_⟩
  let CY₁ := ofRationalLocalization P hP hsheaf kY T s hT
  let ι := toRationalLocalizationComap P hP hsheaf kY T s hT
  have hrange_ι := range_toRationalLocalizationComap_base P hP hsheaf kY T s hT
  obtain ⟨a₁, ha₁⟩ : (a₀ : spa S.plus) ∈ Set.range ι.base :=
    hrange_ι.symm ▸ (ha₀R : (a₀ : spa S.plus) ∈ (spaBasicOpen S.plus T s : Set (spa S.plus)))
  have hsub : Set.range (CY₁.hom ≫ g).base ⊆ Set.range D.hom.base := by
    rintro _ ⟨z, rfl⟩
    rw [ofRationalLocalization_hom_assoc]
    exact hRAO (hrange_ι ▸ ⟨z, rfl⟩ :
      (ι.base z : spa S.plus) ∈ (spaBasicOpen S.plus T s : Set (spa S.plus)))
  let l := IsOpenImmersion.lift D.hom (CY₁.hom ≫ g) hsub
  refine ⟨a₁, presentationLimitHomPairHom D.pairOfDefinition CY₁.pairOfDefinition D.pair CY₁.pair
      D.le_plus CY₁.le_plus l,
    by rw [ofRationalLocalization_hom]; exact congrArg kY.base ha₁, ?_⟩
  rw [pairComap, presentationLimitPreAdicSpacePairComap_presentationLimitHomPairHom
    D.pairOfDefinition CY₁.pairOfDefinition D.pair CY₁.pair D.le_plus CY₁.le_plus CY₁.isSheaf]
  exact IsOpenImmersion.lift_fac D.hom (CY₁.hom ≫ g) hsub

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
  simp only [pairComap_comp_assoc, hsq_g]
  rw [← Category.assoc _ CY.hom, ← ofRationalLocalization_hom, ← Category.assoc, hsq_f,
    Category.assoc]

/-- **Lifting a compatible chart over a rational localisation of the source**: given chart squares
`CZ → CY` over `g : Y ⟶ Z` and `CZ → CX` over `f ≫ g` with `x ∈ X` covered by `c₀ ∈ CX` and
`f(x)` covered by `b₀ ∈ CY`, there is a rational localisation `CX₁ = CX.rationalLocalization TC sC`
around `x` and a Huber-pair morphism `φ : CY.pair → CX₁.pair` making the chart square over `f`
commute and satisfying `φ.comp ψ = (CX.rationalLocalizationHom TC sC hTC).comp χ`. -/
theorem exists_rationalLocalization_lift_sq {X Y Z : PreAdicSpace.{u}}
    {f : X ⟶ Y} {g : Y ⟶ Z} {x : X}
    (CZ : CompleteAffinoidOpen Z) (CY : CompleteAffinoidOpen Y) (CX : CompleteAffinoidOpen X)
    (ψ : Pair.Hom CZ.pair CY.pair) (χ : Pair.Hom CZ.pair CX.pair)
    {b₀ : CY.space} (hb₀ : CY.hom.base b₀ = f.base x)
    {c₀ : CX.space} (hc₀ : CX.hom.base c₀ = x)
    (hsq_g : CZ.pairComap CY ψ ≫ CZ.hom = CY.hom ≫ g)
    (hsq_fg : CZ.pairComap CX χ ≫ CZ.hom = CX.hom ≫ f ≫ g) :
    ∃ (TC : Finset CX.Ring) (sC : CX.Ring)
      (hTC : IsOpen (Ideal.span (TC : Set CX.Ring) : Set CX.Ring)),
      let CX₁ := CX.rationalLocalization TC sC hTC
      ∃ (φ : Pair.Hom CY.pair CX₁.pair) (c₁ : CX₁.space),
        CX₁.hom.base c₁ = x ∧ CY.pairComap CX₁ φ ≫ CY.hom = CX₁.hom ≫ f ∧
        φ.comp ψ = (CX.rationalLocalizationHom TC sC hTC).comp χ := by
  obtain ⟨TC, sC, hTC, -, c₁, φ, hc₁, hsq_f⟩ :=
    exists_ofRationalLocalization_lift CX.pairOfDefinition CX.le_plus CX.isSheaf CX.hom CY f
      (a₀ := c₀) (d₀ := b₀) (by simpa [hc₀] using hb₀.symm)
  let CX₁ := CX.rationalLocalization TC sC hTC
  have hqψ : CY.pairComap CX₁ φ ≫ CZ.pairComap CY ψ =
      CX.pairComap CX₁ (CX.rationalLocalizationHom TC sC hTC) ≫ CZ.pairComap CX χ := by
    rw [← cancel_mono CZ.hom, Category.assoc, hsq_g, ← Category.assoc, hsq_f,
      ofRationalLocalization_hom_assoc, Category.assoc, Category.assoc, ← hsq_fg, Category.assoc]
  have hφψ : φ.comp ψ = (CX.rationalLocalizationHom TC sC hTC).comp χ := by
    have h := congrArg (presentationLimitHomPairHom CZ.pairOfDefinition CX₁.pairOfDefinition
      CZ.pair CX₁.pair CZ.le_plus CX₁.le_plus) hqψ
    rwa [← CZ.pairComap_comp CY CX₁ ψ φ, ← CZ.pairComap_comp CX CX₁ χ _,
      presentationLimitHomPairHom_presentationLimitPreAdicSpacePairComap CZ.pairOfDefinition
        CX₁.pairOfDefinition CZ.pair CX₁.pair CZ.le_plus CX₁.le_plus CX₁.isSheaf,
      presentationLimitHomPairHom_presentationLimitPreAdicSpacePairComap CZ.pairOfDefinition
        CX₁.pairOfDefinition CZ.pair CX₁.pair CZ.le_plus CX₁.le_plus CX₁.isSheaf] at h
  exact ⟨TC, sC, hTC, φ, c₁, hc₁.trans hc₀, hsq_f, hφψ⟩

end CompleteAffinoidOpen

section DiscreteDescent

open CompleteAffinoidOpen

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
      (presentationLimitPresheaf P' T.plus))
    (φ : Pair.Hom S T)
    (y : presentationLimitPreAdicSpace P' T.plus
      T.isRingOfIntegralElements.isPowerBounded_of_mem hP')
    (TA : Finset A) (sA : A) (hTA : IsOpen (Ideal.span (TA : Set A) : Set A))
    (CX : CompleteAffinoidOpen (presentationLimitPreAdicSpace P' T.plus
      T.isRingOfIntegralElements.isPowerBounded_of_mem hP'))
    [DiscreteTopology CX.Ring]
    (β : Pair.Hom (ofRationalLocalization P hP hsheafA (𝟙 _) TA sA hTA).pair CX.pair)
    (hRβ : R β.toRingHom) (c₀ : CX.space) (hc₀ : CX.hom.base c₀ = y)
    (hsq : (ofRationalLocalization P hP hsheafA (𝟙 _) TA sA hTA).pairComap CX β ≫
      (ofRationalLocalization P hP hsheafA (𝟙 _) TA sA hTA).hom =
      CX.hom ≫ presentationLimitPreAdicSpacePairComap P P' hP hP' hsheafB φ) :
    ∃ (TB : Finset B) (sB : B),
      y.1 ∈ rationalSubset T.plus TB sB ∧
      R ((algebraMap B (Localization.Away sB)).comp φ.toRingHom) := by
  classical
  let _ : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
  have : IsUniformAddGroup A := isUniformAddGroup_of_addCommGroup
  have : DiscreteUniformity A := IsRightUniformAddGroup.discreteUniformity
  let _ : UniformSpace B := IsTopologicalAddGroup.rightUniformSpace B
  have : IsUniformAddGroup B := isUniformAddGroup_of_addCommGroup
  have : DiscreteUniformity B := IsRightUniformAddGroup.discreteUniformity
  let CY₁ := ofRationalLocalization P hP hsheafA (𝟙 _) TA sA hTA
  let ιA := toRationalLocalizationHom P hP hsheafA (𝟙 _) TA sA hTA
  let α := β.comp ιA
  have hsq_α : presentationLimitPreAdicSpacePairComap P CX.pairOfDefinition hP CX.le_plus
      CX.isSheaf α = CX.hom ≫ presentationLimitPreAdicSpacePairComap P P' hP hP' hsheafB φ := by
    dsimp only [α]
    rw [presentationLimitPreAdicSpacePairComap_comp P CY₁.pairOfDefinition CX.pairOfDefinition
      hP CY₁.le_plus CX.le_plus CY₁.isSheaf CX.isSheaf]
    rw [ofRationalLocalization_hom, Category.comp_id] at hsq
    exact hsq
  let OB : Opens (presentationLimitPreAdicSpace P' T.plus
      T.isRingOfIntegralElements.isPowerBounded_of_mem hP') :=
    ⟨Set.range CX.hom.base, CX.hom.isOpenEmbedding.isOpen_range⟩
  have hyO : y ∈ OB := ⟨c₀, hc₀⟩
  obtain ⟨RB, hRB, hyR, hRBO⟩ :=
    Opens.isBasis_iff_nbhd.mp (isBasis_spaRationalOpens T.plus) hyO
  obtain ⟨TB, sB, hTB, rfl⟩ := mem_spaRationalOpens_iff_exists_spaBasicOpen.mp hRB
  let CT := ofRationalLocalization P' hP' hsheafB (𝟙 _) TB sB hTB
  have hCT_range : Set.range CT.hom.base = (spaBasicOpen T.plus TB sB : Set (spa T.plus)) := by
    rw [ofRationalLocalization_hom, Category.comp_id]
    exact range_toRationalLocalizationComap_base P' hP' hsheafB (𝟙 _) TB sB hTB
  let δ := presentationLimitHomPairHom P' CX.pairOfDefinition T CX.pair hP' CX.le_plus CX.hom
  have hkX_eq := (presentationLimitPreAdicSpacePairComap_presentationLimitHomPairHom
    P' CX.pairOfDefinition T CX.pair hP' CX.le_plus CX.isSheaf CX.hom).symm
  let TC : Finset CX.Ring := TB.image δ.toRingHom
  let sC : CX.Ring := δ.toRingHom sB
  have hTC : IsOpen (Ideal.span (TC : Set CX.Ring) : Set CX.Ring) := isOpen_discrete _
  let CX₁ := CX.rationalLocalization TC sC hTC
  let ιC := toRationalLocalizationComap CX.pairOfDefinition CX.le_plus CX.isSheaf CX.hom TC sC hTC
  have hpre_eq : (spaBasicOpen CX.pair.plus TC sC : Set (spa CX.pair.plus)) =
      CX.hom.base ⁻¹' (spaBasicOpen T.plus TB sB : Set (spa T.plus)) := by
    rw [hkX_eq, presentationLimitPreAdicSpacePairComap_def,
      presentationLimitPreAdicSpaceComap_toHom, presentationLimitPresheafedSpaceComap_base]
    exact congrArg SetLike.coe (map_spaComapTopHom_obj_spaBasicOpen δ.toRingHom
      δ.continuous_toRingHom δ.map_mem_plus TB sB).symm
  have hrange_eq : Set.range CX₁.hom.base = Set.range CT.hom.base := by
    rw [range_ofRationalLocalization_hom_base, hpre_eq, hCT_range]
    exact Set.image_preimage_eq_iff.mpr hRBO
  let eCB := IsOpenImmersion.isoOfRangeEq CX₁.hom CT.hom hrange_eq
  have heCB_inv := IsOpenImmersion.isoOfRangeEq_inv_comp CX₁.hom CT.hom hrange_eq
  let eγ := ringEquivOfIso CT CX₁ eCB.symm
  have hpath : (presentationLimitHomPairHom CX₁.pairOfDefinition CT.pairOfDefinition
      CX₁.pair CT.pair CX₁.le_plus CT.le_plus eCB.inv).comp
      ((CX.rationalLocalizationHom TC sC hTC).comp α) =
      (toRationalLocalizationHom P' hP' hsheafB (𝟙 _) TB sB hTB).comp φ := by
    have hsq' : eCB.inv ≫ ιC ≫
        presentationLimitPreAdicSpacePairComap P CX.pairOfDefinition hP CX.le_plus CX.isSheaf α =
        toRationalLocalizationComap P' hP' hsheafB (𝟙 _) TB sB hTB ≫
          presentationLimitPreAdicSpacePairComap P P' hP hP' hsheafB φ := by
      have heCB' : eCB.inv ≫ ιC ≫ CX.hom =
          toRationalLocalizationComap P' hP' hsheafB (𝟙 _) TB sB hTB :=
        heCB_inv.trans
          (Category.comp_id (toRationalLocalizationComap P' hP' hsheafB (𝟙 _) TB sB hTB))
      rw [hsq_α, ← Category.assoc ιC, ← Category.assoc eCB.inv, heCB']
    have h := congrArg (presentationLimitHomPairHom P CT.pairOfDefinition S CT.pair hP CT.le_plus)
      hsq'
    dsimp only [ιC, toRationalLocalizationComap] at h ⊢
    rwa [← presentationLimitPreAdicSpacePairComap_comp P CX.pairOfDefinition CX₁.pairOfDefinition
        hP CX.le_plus CX₁.le_plus CX.isSheaf CX₁.isSheaf,
      presentationLimitHomPairHom_comp P CX₁.pairOfDefinition CT.pairOfDefinition S CX₁.pair
        CT.pair hP CX₁.le_plus CT.le_plus,
      presentationLimitHomPairHom_presentationLimitPreAdicSpacePairComap P CX₁.pairOfDefinition S
        CX₁.pair hP CX₁.le_plus CX₁.isSheaf,
      ← presentationLimitPreAdicSpacePairComap_comp P P' CT.pairOfDefinition hP hP' CT.le_plus
        hsheafB CT.isSheaf,
      presentationLimitHomPairHom_presentationLimitPreAdicSpacePairComap P CT.pairOfDefinition S
        CT.pair hP CT.le_plus CT.isSheaf] at h
  let LB := Localization.Away sB
  let hdenB := P'.hasDenominatorPower_of_isOpen_span TB sB LB hTB
  let _ := P'.locUniformSpace TB sB LB hdenB
  have _ := P'.isUniformAddGroup_locUniformSpace TB sB LB hdenB
  have _ := P'.isTopologicalRing_locUniformSpace TB sB LB hdenB
  have _ := P'.isHuberRing_completion_locTopology TB sB LB hdenB
  let eB : LB ≃+* CT.Ring := P'.completionLocEquivOfDiscreteTopology (TB : Set B) sB LB hdenB
  have heB : eB.symm.toRingHom.comp
      (toRationalLocalizationHom P' hP' hsheafB (𝟙 _) TB sB hTB).toRingHom =
      algebraMap B LB := by
    rw [toRationalLocalizationHom_def, toRingHom_toCompletionLocHom]
    exact P'.completionLocEquivOfDiscreteTopology_symm_comp_toCompletionLoc (TB : Set B) sB LB hdenB
  have heq : (algebraMap B LB).comp φ.toRingHom =
      eB.symm.toRingHom.comp (eγ.toRingHom.comp
        ((CX.rationalLocalizationHom TC sC hTC).toRingHom.comp
          (β.toRingHom.comp ιA.toRingHom))) := by
    rw [← heB, RingHom.comp_assoc, ← Pair.Hom.toRingHom_comp, ← hpath]
    simp only [eγ, RingEquiv.toRingHom_eq_coe, coe_ringEquivOfIso, Iso.symm_hom,
      Pair.Hom.toRingHom_comp, α]
  refine ⟨TB, sB, mem_spaBasicOpen.mp hyR, ?_⟩
  rw [heq]
  have hRA : R ιA.toRingHom := by
    dsimp only [ιA]
    rw [toRationalLocalizationHom_def, toRingHom_toCompletionLocHom]
    exact P.ringHom_prop_toCompletionLoc_of_discreteTopology hiso hloc (TA : Set A) sA
      (Localization.Away sA) (P.hasDenominatorPower_of_isOpen_span TA sA (Localization.Away sA) hTA)
  have hRC : R (CX.rationalLocalizationHom TC sC hTC).toRingHom := by
    rw [rationalLocalizationHom, toRationalLocalizationHom_def, toRingHom_toCompletionLocHom]
    exact CX.pairOfDefinition.ringHom_prop_toCompletionLoc_of_discreteTopology hiso hloc
      (TC : Set CX.Ring) sC (Localization.Away sC)
      (CX.pairOfDefinition.hasDenominatorPower_of_isOpen_span TC sC (Localization.Away sC) hTC)
  exact hiso.1 _ eB.symm (hiso.1 _ eγ (hcomp _ _ (hcomp _ _ hRA hRβ) hRC))

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
      (presentationLimitPresheaf P' T.plus))
    (φ : Pair.Hom S T)
    (hchart : ∀ y : presentationLimitPreAdicSpace P' T.plus
        T.isRingOfIntegralElements.isPowerBounded_of_mem hP',
      ∃ (TA : Finset A) (sA : A) (hTA : IsOpen (Ideal.span (TA : Set A) : Set A)),
        let CY₁ := ofRationalLocalization P hP hsheafA (𝟙 _) TA sA hTA
        ∃ (CX : CompleteAffinoidOpen (presentationLimitPreAdicSpace P' T.plus
            T.isRingOfIntegralElements.isPowerBounded_of_mem hP'))
          (_ : DiscreteTopology CX.Ring)
          (β : Pair.Hom CY₁.pair CX.pair) (_ : R β.toRingHom) (c₀ : CX.space),
          CX.hom.base c₀ = y ∧
          CY₁.pairComap CX β ≫ CY₁.hom =
            CX.hom ≫ presentationLimitPreAdicSpacePairComap P P' hP hP' hsheafB φ) :
    R φ.toRingHom := by
  classical
  have hpt (y : spa T.plus) : ∃ (TB : Finset B) (sB : B),
      y.1 ∈ rationalSubset T.plus TB sB ∧
      R ((algebraMap B (Localization.Away sB)).comp φ.toRingHom) := by
    obtain ⟨TA, sA, hTA, CX, _, β, hRβ, c₀, hc₀, hsq⟩ := hchart y
    exact exists_away_comp_of_rational_chart_discrete hcomp hiso hloc P hP hsheafA P' hP' hsheafB
      φ y TA sA hTA CX β hRβ c₀ hc₀ hsq
  choose TB sB hyR hR using hpt
  have : IsLocalization.Away (1 : B) B := IsLocalization.self (by rintro _ ⟨n, rfl⟩; simp)
  have hcov : rationalSubset T.plus ({1} : Finset B) 1 ⊆
      ⋃ y : spa T.plus, rationalSubset T.plus (TB y) (sB y) := fun v hv ↦ by
    rw [rationalSubset_singleton_one] at hv
    exact Set.mem_iUnion.mpr ⟨⟨v, hv⟩, hyR ⟨v, hv⟩⟩
  have hspan_top : Ideal.span (Set.range sB) = ⊤ := by
    simpa using span_eq_top_of_rationalSubset_subset_iUnion (Aplus := T.plus) (T := {1}) (s := 1) B
      (fun _ _ ↦ isOpen_discrete _) hcov
  exact hspan φ.toRingHom (Set.range sB) hspan_top (by rintro ⟨_, y, rfl⟩; exact hR y)

end DiscreteDescent

section CompleteCharts

open CompleteAffinoidOpen

/-- **Upgrading a `chartLocally Q` chart to complete Hausdorff rings on both sides**: if a
Huber-pair morphism property `Q` is preserved by `{1} / 1` rational base change
(`PairOfDefinition.completionLocPairMap`), and `f : X ⟶ Y` is `chartLocally Q` into a sheafy
pre-adic space `Y`, then every point `x : X` admits a `Q`-chart whose target and source rings are
both complete and Hausdorff. -/
theorem chartLocally.exists_complete_chart
    {Q : ∀ {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
      {B : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B]
      {S : Pair A} {T : Pair B}, Pair.Hom S T → Prop}
    (hQ : ∀ {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
      {B : Type u} [CommRing B] [DecidableEq B] [UniformSpace B] [IsUniformAddGroup B]
      [IsTopologicalRing B] [CompleteSpace B] [T2Space B] [IsHuberRing B]
      {S : Pair A} {T : Pair B} (P : PairOfDefinition A) (hP : P.ringOfDefinition ≤ S.plus)
      (P' : PairOfDefinition B) (hP' : P'.ringOfDefinition ≤ T.plus)
      (φ : Pair.Hom S T) (_ : Q φ),
      let L := Localization.Away (1 : A)
      let T' : Finset B := ({1} : Finset A).image φ.toRingHom
      let s' : B := φ.toRingHom 1
      let L' := Localization.Away s'
      have hT1' : IsOpen (Ideal.span (T' : Set B) : Set B) := by simp [T']
      let hden := P.hasDenominatorPower_denom_one ({1} : Finset A) L
      let hden' := P'.hasDenominatorPower_of_isOpen_span T' s' L' hT1'
      letI := P.locUniformSpace ({1} : Finset A) 1 L hden
      letI := P.isUniformAddGroup_locUniformSpace ({1} : Finset A) 1 L hden
      letI := P.isTopologicalRing_locUniformSpace ({1} : Finset A) 1 L hden
      letI := P.isHuberRing_completion_locTopology ({1} : Finset A) 1 L hden
      letI := P'.locUniformSpace T' s' L' hden'
      letI := P'.isUniformAddGroup_locUniformSpace T' s' L' hden'
      letI := P'.isTopologicalRing_locUniformSpace T' s' L' hden'
      letI := P'.isHuberRing_completion_locTopology T' s' L' hden'
      Q (P.completionLocPairMap S hP ({1} : Finset A) 1 L hden P' T hP' φ T' s' L' hden' rfl
        (fun _ ht ↦ Finset.mem_image_of_mem _ ht)))
    {X Y : PreAdicSpace.{u}} (hY : isSheafy Y) {f : X ⟶ Y} (hf : chartLocally Q f) (x : X) :
    ∃ (U : Opens X) (_ : x ∈ U) (V : Opens Y) (_ : U ≤ (Opens.map f.base).obj V)
      (A : Type u) (_ : CommRing A) (_ : UniformSpace A) (_ : IsUniformAddGroup A)
      (_ : IsTopologicalRing A) (_ : CompleteSpace A) (_ : T2Space A) (_ : IsHuberRing A)
      (S : Pair A) (P : PairOfDefinition A) (hP : P.ringOfDefinition ≤ S.plus)
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
          φ.map_mem_plus S.isRingOfIntegralElements.isPowerBounded_of_mem
          T.isRingOfIntegralElements.isPowerBounded_of_mem hP hP' hsheaf ≫
          eV.inv ≫ Y.ofRestrict _ := by
  classical
  obtain ⟨U, hxU, V, hUV, A, _, _, _, _, S, P, hP, B, _, _, _, _, _, _, _, T, P', hP', φ, hφ,
    hsheafB, eU, eV, hfac⟩ := (chartLocally_iff f).mp hf x
  have hT1 : IsOpen (Ideal.span (({1} : Finset A) : Set A) : Set A) := by simp
  let T' : Finset B := ({1} : Finset A).image φ.toRingHom
  let s' : B := φ.toRingHom 1
  have hT1' : IsOpen (Ideal.span (T' : Set B) : Set B) := by simp [T']
  let L := Localization.Away (1 : A)
  let L' := Localization.Away s'
  have hden := P.hasDenominatorPower_denom_one ({1} : Finset A) L
  have hden' := P'.hasDenominatorPower_of_isOpen_span T' s' L' hT1'
  let _ := P.locUniformSpace ({1} : Finset A) 1 L hden
  have _ := P.isUniformAddGroup_locUniformSpace ({1} : Finset A) 1 L hden
  have _ := P.isTopologicalRing_locUniformSpace ({1} : Finset A) 1 L hden
  have _ := P.isHuberRing_completion_locTopology ({1} : Finset A) 1 L hden
  let _ := P'.locUniformSpace T' s' L' hden'
  have _ := P'.isUniformAddGroup_locUniformSpace T' s' L' hden'
  have _ := P'.isTopologicalRing_locUniformSpace T' s' L' hden'
  have _ := P'.isHuberRing_completion_locTopology T' s' L' hden'
  let S₁ := P.rationalLocalizationPair S hP ({1} : Finset A) 1 L hden
  let P₁ := P.completionLocalization ({1} : Finset A) 1 L hden
  let T₁ := P'.rationalLocalizationPair T hP' T' s' L' hden'
  let P₁' := P'.completionLocalization T' s' L' hden'
  have hP₁ : P₁.ringOfDefinition ≤ S₁.plus := by
    rw [rationalLocalizationPair_plus]
    exact P.completionLocalization_ringOfDefinition_le_completedPlusSubring S.plus hP _ _ L hden
  have hP₁' : P₁'.ringOfDefinition ≤ T₁.plus := by
    rw [rationalLocalizationPair_plus]
    exact P'.completionLocalization_ringOfDefinition_le_completedPlusSubring T.plus hP' _ _ L' hden'
  have hsheafA := ObjectProperty.prop_of_iso isSheafy eV (isSheafy_restrict _ hY)
  have hsheafA₁ : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa S₁.plus))
      (presentationLimitPresheaf P₁ S₁.plus) :=
    isSheaf_presentationLimitPresheaf_rationalLocalizationPair P S hP _ _ L hden hT1 hsheafA
  have hsheafB₁ : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa T₁.plus))
      (presentationLimitPresheaf P₁' T₁.plus) :=
    isSheaf_presentationLimitPresheaf_rationalLocalizationPair P' T hP' _ _ L' hden' hT1' hsheafB
  let φ₁ := P.completionLocPairMap S hP ({1} : Finset A) 1 L hden P' T hP' φ T' s' L' hden' rfl
    (fun _ ht ↦ Finset.mem_image_of_mem _ ht)
  have hφ₁ : Q φ₁ := hQ P hP P' hP' φ hφ
  obtain ⟨eA, heA⟩ :=
    exists_iso_presentationLimitPreAdicSpaceComap_toCompletionLocHom_of_forall_mem P hP
      ({1} : Finset A) 1 L hden hT1 (fun y ↦ by rw [rationalSubset_singleton_one]; exact y.2)
      hsheafA₁
  obtain ⟨eB, heB⟩ :=
    exists_iso_presentationLimitPreAdicSpaceComap_toCompletionLocHom_of_forall_mem P' hP' T' s' L'
      hden' hT1' (fun y ↦ by
        simp only [T', s', Finset.image_singleton, map_one, rationalSubset_singleton_one]
        exact y.2) hsheafB₁
  have hcomm := presentationLimitPreAdicSpaceComap_completionLocPairMap_comp P P' hP hP' φ
    hsheafB ({1} : Finset A) 1 L hden L' hden' hsheafA₁ hsheafB₁
  refine ⟨U, hxU, V, hUV, UniformSpace.Completion L, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, S₁, P₁, hP₁,
    UniformSpace.Completion L', inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, T₁, P₁', hP₁', φ₁, hφ₁, hsheafB₁,
    eU ≪≫ eB.symm, eV ≪≫ eA.symm, ?_⟩
  rw [Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Iso.symm_inv, hfac]
  simp only [Category.assoc]
  congr 1
  have hcomm' : presentationLimitPreAdicSpaceComap φ₁.toRingHom φ₁.continuous_toRingHom
      φ₁.map_mem_plus S₁.isRingOfIntegralElements.isPowerBounded_of_mem
      T₁.isRingOfIntegralElements.isPowerBounded_of_mem hP₁ hP₁' hsheafB₁ ≫ eA.hom =
      eB.hom ≫ presentationLimitPreAdicSpaceComap φ.toRingHom φ.continuous_toRingHom
        φ.map_mem_plus S.isRingOfIntegralElements.isPowerBounded_of_mem
        T.isRingOfIntegralElements.isPowerBounded_of_mem hP hP' hsheafB := by
    rw [heA, heB]
    exact hcomm
  rw [← Category.assoc _ eA.hom, hcomm', Category.assoc, Iso.inv_hom_id_assoc]

/-- **Complete affinoid open-immersion chart extraction for `chartLocally Q`**: packages
`chartLocally.exists_complete_chart` into a pair of `CompleteAffinoidOpen`s `CY`, `CX` with a
commuting open-immersion square `CY.pairComap CX φ ≫ CY.hom = CX.hom ≫ f`. -/
theorem chartLocally.exists_complete_openImmersion_chart
    {Q : ∀ {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
      {B : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B]
      {S : Pair A} {T : Pair B}, Pair.Hom S T → Prop}
    (hQ : ∀ {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
      {B : Type u} [CommRing B] [DecidableEq B] [UniformSpace B] [IsUniformAddGroup B]
      [IsTopologicalRing B] [CompleteSpace B] [T2Space B] [IsHuberRing B]
      {S : Pair A} {T : Pair B} (P : PairOfDefinition A) (hP : P.ringOfDefinition ≤ S.plus)
      (P' : PairOfDefinition B) (hP' : P'.ringOfDefinition ≤ T.plus)
      (φ : Pair.Hom S T) (_ : Q φ),
      let L := Localization.Away (1 : A)
      let T' : Finset B := ({1} : Finset A).image φ.toRingHom
      let s' : B := φ.toRingHom 1
      let L' := Localization.Away s'
      have hT1' : IsOpen (Ideal.span (T' : Set B) : Set B) := by simp [T']
      let hden := P.hasDenominatorPower_denom_one ({1} : Finset A) L
      let hden' := P'.hasDenominatorPower_of_isOpen_span T' s' L' hT1'
      letI := P.locUniformSpace ({1} : Finset A) 1 L hden
      letI := P.isUniformAddGroup_locUniformSpace ({1} : Finset A) 1 L hden
      letI := P.isTopologicalRing_locUniformSpace ({1} : Finset A) 1 L hden
      letI := P.isHuberRing_completion_locTopology ({1} : Finset A) 1 L hden
      letI := P'.locUniformSpace T' s' L' hden'
      letI := P'.isUniformAddGroup_locUniformSpace T' s' L' hden'
      letI := P'.isTopologicalRing_locUniformSpace T' s' L' hden'
      letI := P'.isHuberRing_completion_locTopology T' s' L' hden'
      Q (P.completionLocPairMap S hP ({1} : Finset A) 1 L hden P' T hP' φ T' s' L' hden' rfl
        (fun _ ht ↦ Finset.mem_image_of_mem _ ht)))
    {X Y : PreAdicSpace.{u}} (hY : isSheafy Y) {f : X ⟶ Y} (hf : chartLocally Q f) (x : X) :
    ∃ (CY : CompleteAffinoidOpen Y) (CX : CompleteAffinoidOpen X)
      (φ : Pair.Hom CY.pair CX.pair) (_ : Q φ) (b₀ : CX.space),
      CX.hom.base b₀ = x ∧ CY.pairComap CX φ ≫ CY.hom = CX.hom ≫ f := by
  obtain ⟨U, hxU, V, -, A, _, _, _, _, _, _, _, S, P, hP, B, _, _, _, _, _, _, _, T, P', hP',
    φ, hφ, hsheafB, eU, eV, hfac⟩ := hf.exists_complete_chart hQ hY x
  have hsheafA : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa S.plus))
      (presentationLimitPresheaf P S.plus) :=
    ObjectProperty.prop_of_iso isSheafy eV (isSheafy_restrict _ hY)
  exact ⟨ofRestrictIso S P hP hsheafA eV, ofRestrictIso T P' hP' hsheafB eU, φ, hφ,
    eU.hom.base ⟨x, hxU⟩, ofRestrictIso_hom_base T P' hP' hsheafB eU hxU,
    ofRestrictIso_pairComap_comp_hom S P hP hsheafA eV T P' hP' hsheafB eU φ hfac⟩

end CompleteCharts

end TauCeti.PreAdicSpace
