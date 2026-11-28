/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Morphisms.FinitePresentation.Basic
public import TauCeti.AlgebraicGeometry.AdicSpace.Morphisms.FiniteType
public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.LocallyHuberStandard

import TauCeti.RingTheory.Huber.NoetherianType.TopologicallyFiniteType
import TauCeti.RingTheory.Huber.TopologicallyFiniteType.Cancel
import TauCeti.RingTheory.Huber.TopologicallyFiniteType.Comp

/-!
# Chart refinement and composition for morphisms locally of finite presentation

A morphism `f : X ⟶ Y` of adic spaces is *locally of finite presentation*
(`TauCeti.AdicSpace.LocallyOfFinitePresentation`, defined in
`TauCeti.AlgebraicGeometry.AdicSpace.Morphisms.FinitePresentation.Basic`; Huber 1996, (1.1.1) and
Definition 1.2.1(v); Wedhorn, Remark 6.37 and Definition 8.48) when locally on affinoid charts
`X|_U ≅ Spa(B, B⁺)` (`B` complete and Hausdorff) and `Y|_V ≅ Spa(A, A⁺)`, `f` is induced by
`φ : (A, A⁺) → (B, B⁺)` such that `IsHuberStandard A`, `φ.IsTopologicallyFiniteType`, and
`DiscreteTopology A → φ.toRingHom.FinitePresentation`. By completing the target chart via `{1} / 1`,
this is equivalent to the pointwise complete Hausdorff chart condition
`TauCeti.AdicSpace.LocallyOfFinitePresentationAt`.

## Main definitions

* `TauCeti.AdicSpace.LocallyOfFinitePresentationAt`: the pointwise complete Hausdorff chart
  condition at `x : X.obj`.

## Main results

* `locallyOfFinitePresentation_iff`: equivalence between `LocallyOfFinitePresentation` and
  `∀ x, LocallyOfFinitePresentationAt f x`.
* `LocallyOfFinitePresentation.locallyOfPlusWeaklyFiniteType`,
  `.locallyOfWeaklyFiniteType`, `.isAdic`: implications down Huber's hierarchy.
* `LocallyOfFinitePresentation.isLocallyNoetherian_source`: unconditional locally noetherian
  source.
* `LocallyOfFinitePresentationAt.exists_openImmersion_chart`,
  `locallyOfFinitePresentationAt_of_openImmersion_sq`,
  `locallyOfFinitePresentationAt_iff_exists_openImmersion_chart`,
  `LocallyOfFinitePresentation.exists_openImmersion_chart`,
  `locallyOfFinitePresentation_iff_forall_exists_openImmersion_chart`: open-immersion charts.
* `locallyOfFinitePresentation_id_iff`: characterisation of when `𝟙 X` is locally of finite
  presentation.
* `LocallyOfFinitePresentation.exists_openImmersion_over_rationalLocalization`, `.comp`,
  `.isStableUnderComposition`: rational chart refinement and composition closure.

## References

* R. Huber, *Étale cohomology of rigid analytic varieties and adic spaces*, Aspects of
  Mathematics E30 (1996), (1.1.1) and Definition 1.2.1(v).
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Remark 6.37 and Definition 8.48.
-/

public section

open CategoryTheory TopologicalSpace Topology

namespace TauCeti

open Huber ValuationSpectrum

universe u

namespace AdicSpace

open PreAdicSpace CompleteAffinoidOpen

variable {X Y Z : AdicSpace.{u}}

/-- **Pointwise chart condition for `TauCeti.AdicSpace.LocallyOfFinitePresentation`** at
`x : X.obj`: there exist open neighbourhoods `U ⊆ X` of `x` and `V ⊆ Y` with `f(U) ⊆ V`, complete
Hausdorff Huber pairs `(A, A⁺)` and `(B, B⁺)` with `A` in Huber's standing class
(`IsHuberStandard A`), a morphism `φ : (A, A⁺) → (B, B⁺)` topologically of finite type whose ring
map is algebraically of finite presentation whenever `A` is discrete, and isomorphisms
`X|_U ≅ Spa(B, B⁺)` and `Y|_V ≅ Spa(A, A⁺)` identifying `f|_U` with the morphism induced by `φ`. -/
def LocallyOfFinitePresentationAt (f : X ⟶ Y) (x : X.obj) : Prop :=
  ∃ (U : Opens X.obj) (_ : x ∈ U) (V : Opens Y.obj) (_ : U ≤ (Opens.map f.hom.base).obj V)
    (A : Type u) (_ : CommRing A) (_ : UniformSpace A) (_ : IsUniformAddGroup A)
    (_ : IsTopologicalRing A) (_ : CompleteSpace A) (_ : T2Space A) (_ : IsHuberRing A)
    (_ : IsHuberStandard A) (S : Pair A) (P : PairOfDefinition A) (hP : P.ringOfDefinition ≤ S.plus)
    (B : Type u) (_ : CommRing B) (_ : UniformSpace B) (_ : IsUniformAddGroup B)
    (_ : IsTopologicalRing B) (_ : CompleteSpace B) (_ : T2Space B) (_ : IsHuberRing B)
    (T : Pair B) (P' : PairOfDefinition B) (hP' : P'.ringOfDefinition ≤ T.plus)
    (φ : Pair.Hom S T) (_ : φ.IsTopologicallyFiniteType)
    (_ : DiscreteTopology A → φ.toRingHom.FinitePresentation)
    (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa T.plus))
      (presentationLimitPresheaf P' T.plus)) (eU : X.obj.restrict U.isOpenEmbedding ≅
      presentationLimitPreAdicSpace P' T.plus T.isRingOfIntegralElements.isPowerBounded_of_mem hP')
    (eV : Y.obj.restrict V.isOpenEmbedding ≅
      presentationLimitPreAdicSpace P S.plus S.isRingOfIntegralElements.isPowerBounded_of_mem hP),
    X.obj.ofRestrict _ ≫ f.hom =
      eU.hom ≫ presentationLimitPreAdicSpaceComap φ.toRingHom φ.continuous_toRingHom
        φ.map_mem_plus S.isRingOfIntegralElements.isPowerBounded_of_mem
        T.isRingOfIntegralElements.isPowerBounded_of_mem hP hP' hsheaf ≫ eV.inv ≫ Y.obj.ofRestrict _

/-- **A morphism locally of finite presentation is locally of +weakly finite type.** -/
theorem LocallyOfFinitePresentation.locallyOfPlusWeaklyFiniteType {f : X ⟶ Y}
    (hf : LocallyOfFinitePresentation f) : LocallyOfPlusWeaklyFiniteType f :=
  hf.locallyOfFiniteType.locallyOfPlusWeaklyFiniteType

/-- **A morphism locally of finite presentation is locally of weakly finite type.** -/
theorem LocallyOfFinitePresentation.locallyOfWeaklyFiniteType {f : X ⟶ Y}
    (hf : LocallyOfFinitePresentation f) : LocallyOfWeaklyFiniteType f :=
  hf.locallyOfFiniteType.locallyOfWeaklyFiniteType

/-- **A morphism locally of finite presentation is adic** (Huber 1996, §1.2). -/
theorem LocallyOfFinitePresentation.isAdic {f : X ⟶ Y}
    (hf : LocallyOfFinitePresentation f) : IsAdic f :=
  hf.locallyOfFiniteType.isAdic

/-- **Unconditional locally noetherian source**: if `f : X ⟶ Y` is locally of finite presentation,
then `X` is locally noetherian (`X.IsLocallyNoetherian`), with no hypothesis on `Y`. -/
theorem LocallyOfFinitePresentation.isLocallyNoetherian_source {f : X ⟶ Y}
    (hf : LocallyOfFinitePresentation f) : X.IsLocallyNoetherian :=
  (IsLocallyHuberStandard.of_locallyOfFinitePresentation hf).isLocallyNoetherian

/-- **Pointwise open-immersion chart construction for `LocallyOfFinitePresentationAt`**: a
commuting open-immersion square `CY.pairComap CX φ ≫ CY.hom = CX.hom ≫ f.hom` covering `x ∈ X`
with `IsHuberStandard CY.Ring`, `φ.IsTopologicallyFiniteType`, and
`DiscreteTopology CY.Ring → φ.toRingHom.FinitePresentation` witnesses
`LocallyOfFinitePresentationAt f x`. -/
theorem locallyOfFinitePresentationAt_of_openImmersion_sq {f : X ⟶ Y} {x : X.obj}
    (CY : CompleteAffinoidOpen Y.obj) (CX : CompleteAffinoidOpen X.obj) [IsHuberStandard CY.Ring]
    (φ : Pair.Hom CY.pair CX.pair) (hφ : φ.IsTopologicallyFiniteType)
    (hfp : DiscreteTopology CY.Ring → φ.toRingHom.FinitePresentation) {b₀ : CX.space}
    (hb₀ : CX.hom.base b₀ = x) (hsq : CY.pairComap CX φ ≫ CY.hom = CX.hom ≫ f.hom) :
    LocallyOfFinitePresentationAt f x := by
  let U : Opens X.obj := ⟨Set.range CX.hom.base, CX.hom.isOpenEmbedding.isOpen_range⟩
  let V : Opens Y.obj := ⟨Set.range CY.hom.base, CY.hom.isOpenEmbedding.isOpen_range⟩
  have hUV : U ≤ (Opens.map f.hom.base).obj V := fun _ ⟨b, hb⟩ ↦
    hb ▸ ⟨(CY.pairComap CX φ).base b, CY.pairComap_comp_hom_base CX φ hsq b⟩
  let eU := IsOpenImmersion.isoOfRangeEq (X.obj.ofRestrict U.isOpenEmbedding) CX.hom
    (Opens.set_range_inclusion' U)
  let eV := IsOpenImmersion.isoOfRangeEq (Y.obj.ofRestrict V.isOpenEmbedding) CY.hom
    (Opens.set_range_inclusion' V)
  have heU := IsOpenImmersion.isoOfRangeEq_hom_comp (X.obj.ofRestrict U.isOpenEmbedding) CX.hom
    (Opens.set_range_inclusion' U)
  have heV := IsOpenImmersion.isoOfRangeEq_inv_comp (Y.obj.ofRestrict V.isOpenEmbedding) CY.hom
    (Opens.set_range_inclusion' V)
  refine ⟨U, ⟨b₀, hb₀⟩, V, hUV, CY.Ring, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, CY.pair, CY.pairOfDefinition,
    CY.le_plus, CX.Ring, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, CX.pair, CX.pairOfDefinition, CX.le_plus, φ, hφ,
    hfp, CX.isSheaf, eU, eV, ?_⟩
  rw [← presentationLimitPreAdicSpacePairComap_def]
  calc
    X.obj.ofRestrict U.isOpenEmbedding ≫ f.hom
      = eU.hom ≫ (CX.hom ≫ f.hom) := by rw [← Category.assoc, heU]
    _ = eU.hom ≫ (CY.pairComap CX φ ≫ CY.hom) := by rw [hsq]
    _ = eU.hom ≫ CY.pairComap CX φ ≫ eV.inv ≫ Y.obj.ofRestrict V.isOpenEmbedding := by rw [heV]

/-- **Pointwise open-immersion chart extraction for `LocallyOfFinitePresentationAt`**: if
`LocallyOfFinitePresentationAt f x`, then `x` admits complete affinoid opens `CY` of `Y` (with
`IsHuberStandard CY.Ring`) and `CX` of `X` covering `x`, together with a morphism
`φ : CY.pair → CX.pair` topologically of finite type and conditionally algebraically of finite
presentation when `CY.Ring` is discrete, making the open-immersion square commute. -/
theorem LocallyOfFinitePresentationAt.exists_openImmersion_chart {f : X ⟶ Y} {x : X.obj}
    (hf : LocallyOfFinitePresentationAt f x) :
    ∃ (CY : CompleteAffinoidOpen Y.obj) (CX : CompleteAffinoidOpen X.obj)
      (_ : IsHuberStandard CY.Ring) (φ : Pair.Hom CY.pair CX.pair) (_ : φ.IsTopologicallyFiniteType)
      (_ : DiscreteTopology CY.Ring → φ.toRingHom.FinitePresentation) (b₀ : CX.space),
      CX.hom.base b₀ = x ∧ CY.pairComap CX φ ≫ CY.hom = CX.hom ≫ f.hom := by
  obtain ⟨U, hxU, V, -, A, _, _, _, _, _, _, _, _, S, P, hP, B, _, _, _, _, _, _, _, T, P', hP',
    φ, hφ, hfp, hsheafB, eU, eV, hfac⟩ := hf
  have hsheafA := isSheaf_of_restrict_iso P hP eV
  exact ⟨ofRestrictIso S P hP hsheafA eV, ofRestrictIso T P' hP' hsheafB eU,
    (inferInstance : IsHuberStandard A), φ, hφ, hfp, eU.hom.base ⟨x, hxU⟩,
    ofRestrictIso_hom_base .., ofRestrictIso_pairComap_comp_hom _ _ _ _ _ _ _ _ _ _ φ hfac⟩

/-- **Pointwise open-immersion chart characterisation of `LocallyOfFinitePresentationAt`**:
`LocallyOfFinitePresentationAt f x` holds if and only if `x` is covered by a commuting
open-immersion square between complete affinoid opens with `IsHuberStandard CY.Ring`,
`φ.IsTopologicallyFiniteType`, and `DiscreteTopology CY.Ring → φ.toRingHom.FinitePresentation`. -/
theorem locallyOfFinitePresentationAt_iff_exists_openImmersion_chart (f : X ⟶ Y) (x : X.obj) :
    LocallyOfFinitePresentationAt f x ↔
      ∃ (CY : CompleteAffinoidOpen Y.obj) (CX : CompleteAffinoidOpen X.obj)
        (_ : IsHuberStandard CY.Ring) (φ : Pair.Hom CY.pair CX.pair)
        (_ : φ.IsTopologicallyFiniteType)
        (_ : DiscreteTopology CY.Ring → φ.toRingHom.FinitePresentation) (b₀ : CX.space),
        CX.hom.base b₀ = x ∧ CY.pairComap CX φ ≫ CY.hom = CX.hom ≫ f.hom :=
  ⟨fun hf ↦ hf.exists_openImmersion_chart, fun ⟨CY, CX, _, φ, hφ, hfp, _, hb₀, hsq⟩ ↦
    locallyOfFinitePresentationAt_of_openImmersion_sq CY CX φ hφ hfp hb₀ hsq⟩

/-- Characterisation of `TauCeti.AdicSpace.LocallyOfFinitePresentation` in terms of complete
Hausdorff pointwise charts `LocallyOfFinitePresentationAt`. -/
theorem locallyOfFinitePresentation_iff (f : X ⟶ Y) :
    LocallyOfFinitePresentation f ↔ ∀ x : X.obj, LocallyOfFinitePresentationAt f x := by
  constructor
  · intro hf x
    obtain ⟨U, hxU, V, hUV, A, _, _, _, _, _, _, _, S, P, hP, B, _, _, _, _, _, _, _, T, P',
      hP', φ, ⟨hφ, hStdA, hfp⟩, hsheaf, eU, eV, hfac⟩ :=
      exists_complete_chart_of_chartLocally
        (@fun A _ _ _ _ _ _ _ _ _ _ _ φ ↦ φ.IsTopologicallyFiniteType ∧
          IsHuberStandard A ∧ (DiscreteTopology A → φ.toRingHom.FinitePresentation))
        (fun hιA ⟨hcomp, hStdA, hfp⟩ ↦ by
          have _ := hStdA
          have hφ₁ := Pair.Hom.IsTopologicallyFiniteType.of_comp hcomp
          exact ⟨hφ₁, .of_isTopologicallyFiniteType hιA.isTopologicallyFiniteType_toRingHom,
            fun _ ↦ hιA.isTopologicallyFiniteType_toRingHom.finitePresentation_of_comp
              hφ₁.isTopologicallyFiniteType_toRingHom
              (fun hDisc ↦ by rw [← Pair.Hom.toRingHom_comp]; exact hfp hDisc)⟩)
        ((locallyOfFinitePresentation_iff_chartLocally f).mp hf) x
    exact ⟨U, hxU, V, hUV, A, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, inferInstance, inferInstance, inferInstance, S, P, hP, B, inferInstance,
      inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      T, P', hP', φ, hφ, hfp, hsheaf, eU, eV, hfac⟩
  · intro hf
    rw [locallyOfFinitePresentation_iff_chartLocally, chartLocally_iff]
    intro x
    obtain ⟨U, hxU, V, hUV, A, _, _, _, _, _, _, _, _, S, P, hP, B, _, _, _, _, _, _, _, T, P',
      hP', φ, hφ, hfp, hsheaf, eU, eV, hfac⟩ := hf x
    exact ⟨U, hxU, V, hUV, A, inferInstance, inferInstance, inferInstance, inferInstance, S, P, hP,
      B, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, T, P', hP', φ, ⟨hφ, inferInstance, hfp⟩, hsheaf, eU, eV, hfac⟩

/-- **Open-immersion chart extraction for `LocallyOfFinitePresentation`**: if `f : X ⟶ Y` is
locally of finite presentation, every `x ∈ X` admits complete affinoid opens `CY` of `Y` (with
`IsHuberStandard CY.Ring`) and `CX` of `X` covering `x`, together with a morphism
`φ : CY.pair → CX.pair` topologically of finite type and conditionally algebraically of finite
presentation when `CY.Ring` is discrete, making the open-immersion square commute. -/
theorem LocallyOfFinitePresentation.exists_openImmersion_chart {f : X ⟶ Y}
    (hf : LocallyOfFinitePresentation f) (x : X.obj) :
    ∃ (CY : CompleteAffinoidOpen Y.obj) (CX : CompleteAffinoidOpen X.obj)
      (_ : IsHuberStandard CY.Ring) (φ : Pair.Hom CY.pair CX.pair) (_ : φ.IsTopologicallyFiniteType)
      (_ : DiscreteTopology CY.Ring → φ.toRingHom.FinitePresentation) (b₀ : CX.space),
      CX.hom.base b₀ = x ∧ CY.pairComap CX φ ≫ CY.hom = CX.hom ≫ f.hom :=
  ((locallyOfFinitePresentation_iff f).mp hf x).exists_openImmersion_chart

/-- **Open-immersion chart characterisation of `LocallyOfFinitePresentation`**: a morphism
`f : X ⟶ Y` of adic spaces is locally of finite presentation if and only if every `x ∈ X` is
covered by a commuting open-immersion square between complete affinoid opens with
`IsHuberStandard CY.Ring`, `φ.IsTopologicallyFiniteType`, and
`DiscreteTopology CY.Ring → φ.toRingHom.FinitePresentation`. -/
theorem locallyOfFinitePresentation_iff_forall_exists_openImmersion_chart (f : X ⟶ Y) :
    LocallyOfFinitePresentation f ↔
      ∀ x : X.obj, ∃ (CY : CompleteAffinoidOpen Y.obj) (CX : CompleteAffinoidOpen X.obj)
        (_ : IsHuberStandard CY.Ring) (φ : Pair.Hom CY.pair CX.pair)
        (_ : φ.IsTopologicallyFiniteType)
        (_ : DiscreteTopology CY.Ring → φ.toRingHom.FinitePresentation) (b₀ : CX.space),
        CX.hom.base b₀ = x ∧ CY.pairComap CX φ ≫ CY.hom = CX.hom ≫ f.hom :=
  (locallyOfFinitePresentation_iff f).trans
    (forall_congr' (locallyOfFinitePresentationAt_iff_exists_openImmersion_chart f))

/-- **Characterisation of when an identity morphism is locally of finite presentation**:
`LocallyOfFinitePresentation (𝟙 X) ↔ X.IsLocallyHuberStandard`. -/
theorem locallyOfFinitePresentation_id_iff :
    LocallyOfFinitePresentation (𝟙 X) ↔ X.IsLocallyHuberStandard :=
  locallyOfFinitePresentation_iff_of_isOpenImmersion (𝟙 X)

/-- Transfer of topological finite type and conditional algebraic finite presentation along a
chart factorisation `φ.comp ψ = (CX₀.rationalLocalizationHom TC sC hTC).comp χ` obtained after
rationally shrinking the source chart `CX₀`: assuming `CZ.Ring` is in Huber's standing class
(`IsHuberStandard CZ.Ring`), `ψ` and `χ` are topologically of finite type, and `χ.toRingHom` is
algebraically of finite presentation whenever `CZ.Ring` is discrete, the morphism `φ` is
topologically of finite type and `φ.toRingHom` is algebraically of finite presentation whenever
`CY.Ring` is discrete. -/
theorem isTopologicallyFiniteType_and_finitePresentation_of_comp_rationalLocalization
    {X₀ Y₀ Z₀ : PreAdicSpace.{u}} {CZ : CompleteAffinoidOpen Z₀} [IsHuberStandard CZ.Ring]
    {CY : CompleteAffinoidOpen Y₀} {CX₀ : CompleteAffinoidOpen X₀} {TC : Finset CX₀.Ring}
    {sC : CX₀.Ring} {hTC : IsOpen (Ideal.span (TC : Set CX₀.Ring) : Set CX₀.Ring)}
    {ψ : Pair.Hom CZ.pair CY.pair} (hψ : ψ.IsTopologicallyFiniteType)
    {χ : Pair.Hom CZ.pair CX₀.pair} (hχ : χ.IsTopologicallyFiniteType)
    (hχ_fp : DiscreteTopology CZ.Ring → χ.toRingHom.FinitePresentation)
    {φ : Pair.Hom CY.pair (CX₀.rationalLocalization TC sC hTC).pair}
    (hcomp : φ.comp ψ = (CX₀.rationalLocalizationHom TC sC hTC).comp χ) :
    φ.IsTopologicallyFiniteType ∧ (DiscreteTopology CY.Ring → φ.toRingHom.FinitePresentation) := by
  have hφ_tft : φ.IsTopologicallyFiniteType :=
    .of_comp (hcomp ▸ (CX₀.isTopologicallyFiniteType_rationalLocalizationHom TC sC hTC).comp hχ)
  refine ⟨hφ_tft, fun _ ↦ hψ.isTopologicallyFiniteType_toRingHom.finitePresentation_of_comp
    hφ_tft.isTopologicallyFiniteType_toRingHom fun hDiscA ↦ ?_⟩
  have : DiscreteTopology CX₀.Ring := hχ.isTopologicallyFiniteType_toRingHom.discreteTopology
  rw [← Pair.Hom.toRingHom_comp, hcomp, Pair.Hom.toRingHom_comp]
  exact (CX₀.finitePresentation_rationalLocalizationHom TC sC hTC).comp (hχ_fp hDiscA)

/-- **Chart refinement over a prescribed target open for `LocallyOfFinitePresentation`**: given
`f : X ⟶ Y` locally of finite presentation, an arbitrary complete affinoid open `CY` of `Y` (not
assumed to satisfy `IsHuberStandard`), and a point `x ∈ X` whose image `f(x)` is hit by
`a₀ ∈ CY.space`, there exists a rational localisation `CY₁ = CY.rationalLocalization TA sA hTA`
containing `a₀` such that `IsHuberStandard CY₁.Ring` and a complete affinoid open `CX` of `X`
covering `x` over `CY₁` via a Huber-pair morphism `β` topologically of finite type whose ring map is
algebraically of finite presentation whenever `CY₁.Ring` is discrete. -/
theorem LocallyOfFinitePresentation.exists_openImmersion_over_rationalLocalization {f : X ⟶ Y}
    (hf : LocallyOfFinitePresentation f) (CY : CompleteAffinoidOpen Y.obj) (x : X.obj)
    {a₀ : CY.space} (ha₀ : CY.hom.base a₀ = f.hom.base x) : ∃ (TA : Finset CY.Ring) (sA : CY.Ring)
      (hTA : IsOpen (Ideal.span (TA : Set CY.Ring) : Set CY.Ring)),
      a₀ ∈ spaBasicOpen CY.pair.plus TA sA ∧
      let CY₁ := CY.rationalLocalization TA sA hTA; IsHuberStandard CY₁.Ring ∧
      ∃ (CX : CompleteAffinoidOpen X.obj) (β : Pair.Hom CY₁.pair CX.pair)
        (_ : β.IsTopologicallyFiniteType)
        (_ : DiscreteTopology CY₁.Ring → β.toRingHom.FinitePresentation) (c₀ : CX.space),
        CX.hom.base c₀ = x ∧ CY₁.pairComap CX β ≫ CY₁.hom = CX.hom ≫ f.hom := by
  obtain ⟨CY', CX₀, _, φ', hφ', hfp', c₀₀, hc₀₀, hsq'⟩ := hf.exists_openImmersion_chart x
  have had₀ : CY'.hom.base ((CY'.pairComap CX₀ φ').base c₀₀) = CY.hom.base a₀ := by
    rw [CY'.pairComap_comp_hom_base CX₀ φ' hsq' c₀₀, hc₀₀, ha₀]
  obtain ⟨TA', sA', hTA', -, a'₁, α₀, ha'₁, hsq_α₀⟩ :=
    exists_ofRationalLocalization_lift CY'.pairOfDefinition CY'.le_plus CY'.isSheaf CY'.hom CY
      (𝟙 Y.obj) (by rw [Category.comp_id]; exact had₀)
  let CY'₁ := CY'.rationalLocalization TA' sA' hTA'
  have had₁ : (CY.hom ≫ 𝟙 Y.obj).base a₀ = CY'₁.hom.base a'₁ := by
    rw [Category.comp_id]; exact had₀.symm.trans ha'₁.symm
  obtain ⟨TA, sA, hTA, ha₀R, a₁, α₁, ha₁, hsq_α₁⟩ :=
    exists_ofRationalLocalization_lift CY.pairOfDefinition CY.le_plus CY.isSheaf CY.hom CY'₁
      (𝟙 Y.obj) had₁
  let CY₁ := CY.rationalLocalization TA sA hTA
  have hα₁α₀ : α₁.comp α₀ = CY.rationalLocalizationHom TA sA hTA := CY.pairComap_injective CY₁ <| by
    rw [← cancel_mono CY.hom]
    calc
      CY.pairComap CY₁ (α₁.comp α₀) ≫ CY.hom
        = CY'₁.pairComap CY₁ α₁ ≫ (CY.pairComap CY'₁ α₀ ≫ CY.hom) := by
            simp only [pairComap_comp_assoc]
      _ = CY'₁.pairComap CY₁ α₁ ≫ CY'₁.hom := by rw [hsq_α₀, Category.comp_id]
      _ = CY₁.hom := by simp only [hsq_α₁, Category.comp_id, CY₁]
      _ = CY.pairComap CY₁ (CY.rationalLocalizationHom TA sA hTA) ≫ CY.hom :=
            (CY.rationalLocalization_hom TA sA hTA).symm
  have hα₁_tft : α₁.IsTopologicallyFiniteType :=
    .of_comp (hα₁α₀ ▸ CY.isTopologicallyFiniteType_rationalLocalizationHom TA sA hTA)
  let ψ₀ := α₁.comp (CY'.rationalLocalizationHom TA' sA' hTA')
  have hψ₀_tft := hα₁_tft.comp (CY'.isTopologicallyFiniteType_rationalLocalizationHom TA' sA' hTA')
  have hsq_ψ₀ : CY'.pairComap CY₁ ψ₀ ≫ CY'.hom = CY₁.hom ≫ 𝟙 Y.obj :=
    (CY'.pairComap_comp_rationalLocalizationHom_comp_hom CY₁ α₁).trans hsq_α₁
  obtain ⟨TC, sC, hTC, β, c₁, hc₁, hsq, hβψ₀⟩ :=
    exists_rationalLocalization_lift_sq CY' CY₁ CX₀ ψ₀ φ'
      (ha₁.trans ha₀) hc₀₀ hsq_ψ₀ (by simpa using hsq')
  obtain ⟨hβ_tft, hβ_fp⟩ :=
    isTopologicallyFiniteType_and_finitePresentation_of_comp_rationalLocalization
      hψ₀_tft hφ' hfp' hβψ₀
  exact ⟨TA, sA, hTA, ha₀R,
    .of_isTopologicallyFiniteType hψ₀_tft.isTopologicallyFiniteType_toRingHom,
    CX₀.rationalLocalization TC sC hTC, β, hβ_tft, hβ_fp, c₁, hc₁, hsq⟩

/-- **Composition of morphisms locally of finite presentation** (Huber 1996, §1.2): if `f : X ⟶ Y`
and `g : Y ⟶ Z` are locally of finite presentation, then `f ≫ g` is locally of finite
presentation. -/
theorem LocallyOfFinitePresentation.comp {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : LocallyOfFinitePresentation f) (hg : LocallyOfFinitePresentation g) :
    LocallyOfFinitePresentation (f ≫ g) := (locallyOfFinitePresentation_iff (f ≫ g)).mpr fun x ↦ by
  obtain ⟨CZ, CY, _, ψ, hψ, hψ_fp, b₀, hb₀, hsq_g⟩ := hg.exists_openImmersion_chart (f.hom.base x)
  obtain ⟨TB, sB, hTB, -, -, CX, β, hβ, hβ_fp, c₀, hc₀, hsq_f⟩ :=
    hf.exists_openImmersion_over_rationalLocalization CY x hb₀
  let ψ₁ := (CY.rationalLocalizationHom TB sB hTB).comp ψ
  have hψ₁_tft := (CY.isTopologicallyFiniteType_rationalLocalizationHom TB sB hTB).comp hψ
  have hfp : DiscreteTopology CZ.Ring → (β.comp ψ₁).toRingHom.FinitePresentation := fun hDiscA ↦ by
    have : DiscreteTopology CY.Ring := hψ.isTopologicallyFiniteType_toRingHom.discreteTopology
    have : DiscreteTopology (CY.rationalLocalization TB sB hTB).Ring :=
      hψ₁_tft.isTopologicallyFiniteType_toRingHom.discreteTopology
    rw [Pair.Hom.toRingHom_comp, Pair.Hom.toRingHom_comp]
    exact (hβ_fp inferInstance).comp
      ((CY.finitePresentation_rationalLocalizationHom TB sB hTB).comp (hψ_fp hDiscA))
  refine locallyOfFinitePresentationAt_of_openImmersion_sq CZ CX (β.comp ψ₁)
    (hβ.comp hψ₁_tft) hfp hc₀ ?_
  rw [ObjectProperty.FullSubcategory.comp_hom]
  exact CZ.pairComap_comp_rationalLocalization_sq CY hTB CX ψ β hsq_g hsq_f

/-- `LocallyOfFinitePresentation` is stable under composition. -/
instance LocallyOfFinitePresentation.isStableUnderComposition :
    LocallyOfFinitePresentation.{u}.IsStableUnderComposition where comp_mem _ _ hf hg := hf.comp hg

end AdicSpace

end TauCeti
