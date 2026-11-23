/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Morphisms.WeaklyFiniteType

import TauCeti.RingTheory.Huber.NoetherianType.TopologicallyFiniteType

/-!
# Morphisms of adic spaces locally of finite presentation

A morphism `f : X ⟶ Y` of adic spaces is *locally of finite presentation* (Huber 1996,
Definition 1.2.1(v)) if every point of `X` has an open neighbourhood `U`, mapped by `f` into an
open `V` of `Y`, such that `U ≅ Spa(B, B⁺)` and `V ≅ Spa(A, A⁺)` for Huber pairs, `B` complete and
Hausdorff, under which `f` restricted to `U → V` is the morphism induced by a morphism of Huber
pairs `φ : (A, A⁺) → (B, B⁺)` with three properties:

* `φ` is topologically of finite type as a morphism of pairs
  (`TauCeti.Huber.Pair.Hom.IsTopologicallyFiniteType`), so `f` is locally of finite type;
* `A` belongs to Huber's standing class (`TauCeti.Huber.IsHuberStandard`): it is finite type over a
  noetherian ring of definition, a strongly noetherian Tate ring, or discrete;
* if `A` carries the discrete topology, then `B` is a finitely presented `A`-algebra
  (`RingHom.FinitePresentation`).

Huber states the definition for adic spaces all of whose affinoid rings lie in his standing class
(Huber 1996, (1.1.1)). Asking the witness chart of the target to be in the class keeps that reading
on arbitrary adic spaces; otherwise the discrete condition could be avoided through a target chart
that is neither discrete nor in the class. Over a discrete ring, topological finite type is finite
type (Wedhorn, Example 6.32), and the extra condition is algebraic finite presentation; over the
other two alternatives of the class no condition is added to local finite type.

Local finite presentation is the smallest class in Huber's hierarchy of finiteness conditions
(Huber 1996, §1.2): a morphism locally of finite presentation is locally of finite type. The
source of a morphism locally of finite presentation is always locally of Huber's standing class,
whatever the target: its source charts are topologically of finite type over rings of the class.
Conversely, an open immersion out of an adic space locally of Huber's standing class is locally of
finite presentation, so in particular identities of such spaces are.

## Main definitions

* `TauCeti.AdicSpace.LocallyOfFinitePresentation`: morphisms of adic spaces locally of finite
  presentation.

## Main results

* `TauCeti.AdicSpace.LocallyOfFinitePresentation.locallyOfFiniteType`: a morphism locally of
  finite presentation is locally of finite type.
* `TauCeti.AdicSpace.LocallyOfFinitePresentation.respectsIso`: the property is invariant under
  isomorphisms of the source and of the target.
* `TauCeti.AdicSpace.locallyOfFinitePresentation_presentationLimitPreAdicSpaceComap`: the morphism
  `Spa(B, B⁺) ⟶ Spa(A, A⁺)` induced by a morphism of Huber pairs topologically of finite type out
  of a ring of Huber's standing class, finitely presented when `A` is discrete, is locally of
  finite presentation.
* `TauCeti.AdicSpace.IsLocallyHuberStandard.of_locallyOfFinitePresentation`: the source of a
  morphism locally of finite presentation is locally of Huber's standing class.
* `TauCeti.AdicSpace.locallyOfFinitePresentation_iff_of_isOpenImmersion`: an open immersion is
  locally of finite presentation exactly when its source is locally of Huber's standing class; in
  particular so are identities of such spaces
  (`TauCeti.AdicSpace.LocallyOfFinitePresentation.id`).
* `TauCeti.AdicSpace.LocallyOfFinitePresentation.of_isEmpty`: morphisms out of the empty adic
  space are locally of finite presentation.

## Implementation notes

As in `TauCeti.PreAdicSpace.chartLocally`, the target ring `A` of a chart need not be complete:
`Spa(A, A⁺)` only sees the completion of `A`, and Huber's standing class passes to completions
(`TauCeti.Huber.IsHuberStandard.completion`).

## References

* R. Huber, *Étale cohomology of rigid analytic varieties and adic spaces*, Aspects of
  Mathematics E30 (1996), (1.1.1) and §1.2, Definition 1.2.1(v).
* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Example 6.32 and Definitions 8.42 and 8.48.
-/

public section

open CategoryTheory TopologicalSpace

namespace TauCeti

open Huber

universe u

namespace AdicSpace

open PreAdicSpace ValuationSpectrum

/-- **Morphisms locally of finite presentation** (Huber 1996, Definition 1.2.1(v)): a morphism
`f : X ⟶ Y` of adic spaces is *locally of finite presentation* when every point `x` of `X` has an
open neighbourhood `U`, mapped by `f` into an open `V` of `Y`, together with Huber pairs `(A, A⁺)`
and `(B, B⁺)`, `B` complete and Hausdorff with `Spa(B, B⁺)` having a sheaf as structure presheaf,
a morphism `φ : (A, A⁺) → (B, B⁺)`, and isomorphisms identifying `X` restricted to `U` with
`Spa(B, B⁺)` and `Y` restricted to `V` with `Spa(A, A⁺)`, under which `f` becomes the morphism
induced by `φ`, such that `φ` is topologically of finite type, `A` is in Huber's standing class,
and `φ` makes `B` a finitely presented `A`-algebra when `A` is discrete. -/
def LocallyOfFinitePresentation : MorphismProperty AdicSpace.{u} := fun _ _ f ↦
  chartLocally (@fun A _ _ _ _ _ _ _ _ _ _ _ φ ↦ φ.IsTopologicallyFiniteType ∧
    IsHuberStandard A ∧ (DiscreteTopology A → φ.toRingHom.FinitePresentation)) f.hom

variable {X Y : AdicSpace.{u}}

/-- Unfolding lemma for `TauCeti.AdicSpace.LocallyOfFinitePresentation`. -/
theorem locallyOfFinitePresentation_iff_chartLocally (f : X ⟶ Y) :
    LocallyOfFinitePresentation f ↔
      chartLocally (@fun A _ _ _ _ _ _ _ _ _ _ _ φ ↦ φ.IsTopologicallyFiniteType ∧
        IsHuberStandard A ∧ (DiscreteTopology A → φ.toRingHom.FinitePresentation)) f.hom :=
  Iff.rfl

/-- **A morphism locally of finite presentation is locally of finite type** (Huber 1996, §1.2):
on each chart it is induced by a morphism of Huber pairs topologically of finite type. -/
theorem LocallyOfFinitePresentation.locallyOfFiniteType {f : X ⟶ Y}
    (hf : LocallyOfFinitePresentation f) : PreAdicSpace.LocallyOfFiniteType f.hom :=
  (locallyOfFiniteType_iff f.hom).mpr <|
    chartLocally_mono (fun _ hφ ↦ hφ.1) ((locallyOfFinitePresentation_iff_chartLocally f).mp hf)

/-- **Being locally of finite presentation is invariant under isomorphisms** of the source and of
the target: it is the inverse image of a chart-local property along the inclusion of adic spaces
into pre-adic spaces. -/
instance LocallyOfFinitePresentation.respectsIso :
    MorphismProperty.RespectsIso (@LocallyOfFinitePresentation.{u}) :=
  MorphismProperty.RespectsIso.inverseImage
    (chartLocally @fun A _ _ _ _ _ _ _ _ _ _ _ φ ↦ φ.IsTopologicallyFiniteType ∧
      IsHuberStandard A ∧ (DiscreteTopology A → φ.toRingHom.FinitePresentation))
    (ObjectProperty.ι PreAdicSpace.isAdic)

/-- **Affinoid morphisms**: let `φ : (A, A⁺) → (B, B⁺)` be a morphism of Huber pairs topologically
of finite type, with `A` in Huber's standing class, `B` complete and Hausdorff, both adic spectra
adic spaces, and `φ` finitely presented on rings when `A` is discrete. Then the morphism
`Spa(B, B⁺) ⟶ Spa(A, A⁺)` induced by `φ` is locally of finite presentation, witnessed over the
whole of both spectra. -/
theorem locallyOfFinitePresentation_presentationLimitPreAdicSpaceComap {A : Type u} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A] [IsHuberStandard A] {B : Type u}
    [CommRing B] [UniformSpace B] [IsUniformAddGroup B] [IsTopologicalRing B] [CompleteSpace B]
    [T2Space B] [IsHuberRing B] {S : Pair A} {T : Pair B} (P : PairOfDefinition A)
    (P' : PairOfDefinition B) (hP : P.ringOfDefinition ≤ S.plus)
    (hP' : P'.ringOfDefinition ≤ T.plus)
    (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa T.plus))
      (presentationLimitPresheaf P' T.plus))
    (hA : PreAdicSpace.isAdic (presentationLimitPreAdicSpace P S.plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem hP)) (φ : Pair.Hom S T)
    (hφ : φ.IsTopologicallyFiniteType)
    (hfp : DiscreteTopology A → φ.toRingHom.FinitePresentation) :
    LocallyOfFinitePresentation (X := ⟨_, isAdic_presentationLimitPreAdicSpace P' T.plus
        T.isRingOfIntegralElements.isPowerBounded_of_mem hP' hsheaf⟩) (Y := ⟨_, hA⟩)
      (ObjectProperty.homMk (presentationLimitPreAdicSpaceComap φ.toRingHom
        φ.continuous_toRingHom φ.map_mem_plus S.isRingOfIntegralElements.isPowerBounded_of_mem
        T.isRingOfIntegralElements.isPowerBounded_of_mem hP hP' hsheaf)) := by
  rw [locallyOfFinitePresentation_iff_chartLocally, ObjectProperty.homMk_hom]
  exact chartLocally_presentationLimitPreAdicSpaceComap P P' hP hP' hsheaf φ
    ⟨hφ, inferInstance, hfp⟩

/-- **The source of a morphism locally of finite presentation is locally of Huber's standing
class**, with no hypothesis on the target: each source chart `Spa(B, B⁺)` is topologically of
finite type over a ring `A` of Huber's standing class, so `B` is in Huber's standing class
(`TauCeti.Huber.IsHuberStandard.of_isTopologicallyFiniteType`). -/
theorem IsLocallyHuberStandard.of_locallyOfFinitePresentation {f : X ⟶ Y}
    (hf : LocallyOfFinitePresentation f) : X.IsLocallyHuberStandard := by
  refine isLocallyHuberStandard_iff.mpr fun x ↦ ?_
  obtain ⟨U, hxU, -, -, A, _, _, _, _, S, P, hP, B, _, _, _, _, _, _, _, T, P', hP', φ,
    ⟨hφ, _, -⟩, -, eU, -, -⟩ :=
    (chartLocally_iff _).mp ((locallyOfFinitePresentation_iff_chartLocally f).mp hf) x
  have := IsHuberStandard.of_isTopologicallyFiniteType hφ.isTopologicallyFiniteType_toRingHom
  refine ⟨U, (mem_propOpens_iff _).mpr <| (isHuberStandardAffinoid_iff _).mpr ?_, hxU⟩
  exact ⟨B, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, T, P', hP', ⟨eU⟩⟩

/-- **Open immersions out of adic spaces locally of Huber's standing class are locally of finite
presentation**: over each open affinoid `f(U) ≅ U ≅ Spa(A, A⁺)` with `A` in Huber's standing class,
`f` is the identity of `Spa(A, A⁺)`. No condition on `Y` is needed. -/
theorem LocallyOfFinitePresentation.of_isOpenImmersion (f : X ⟶ Y)
    [PreAdicSpace.IsOpenImmersion f.hom] (hX : X.IsLocallyHuberStandard) :
    LocallyOfFinitePresentation f := by
  refine (locallyOfFinitePresentation_iff_chartLocally f).mpr <| (chartLocally_iff _).mpr
    fun x ↦ ?_
  obtain ⟨U, hU, hxU⟩ := isLocallyHuberStandard_iff.mp hX x
  obtain ⟨A, _, _, _, _, _, _, _, _, S, P, hP, ⟨eU⟩⟩ :=
    (isHuberStandardAffinoid_iff _).mp ((mem_propOpens_iff _).mp hU)
  have hsheaf := (isSheafy_presentationLimitPreAdicSpace_iff P S.plus
    S.isRingOfIntegralElements.isPowerBounded_of_mem hP).mp <|
      ObjectProperty.prop_of_iso isSheafy eU
        (isSheafy_restrict U.isOpenEmbedding X.property.isSheafy)
  -- `f` identifies `U` with the open `f(U)` of `Y`
  let V : Opens Y.obj := f.hom.isOpenEmbedding.isOpenMap.functor.obj U
  let e := IsOpenImmersion.isoOfRangeEq _ _ (IsOpenImmersion.range_ofRestrict_comp_base f.hom U)
  refine ⟨U, hxU, V, fun y hy ↦ ⟨y, hy, rfl⟩, A, inferInstance, inferInstance, inferInstance,
    inferInstance, S, P, hP, A, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, S, P, hP, Pair.Hom.id S,
    ⟨Pair.Hom.isTopologicallyFiniteType_id S, inferInstance, fun _ ↦ by
      rw [Pair.Hom.toRingHom_id]
      exact RingHom.FinitePresentation.id A⟩,
    hsheaf, eU, e.symm ≪≫ eU, ?_⟩
  simp [e]

/-- **An open immersion is locally of finite presentation exactly when its source is locally of
Huber's standing class.** -/
theorem locallyOfFinitePresentation_iff_of_isOpenImmersion (f : X ⟶ Y)
    [PreAdicSpace.IsOpenImmersion f.hom] :
    LocallyOfFinitePresentation f ↔ X.IsLocallyHuberStandard :=
  ⟨IsLocallyHuberStandard.of_locallyOfFinitePresentation,
    LocallyOfFinitePresentation.of_isOpenImmersion f⟩

/-- **Identities of adic spaces locally of Huber's standing class are locally of finite
presentation.** -/
theorem LocallyOfFinitePresentation.id (hX : X.IsLocallyHuberStandard) :
    LocallyOfFinitePresentation (𝟙 X) :=
  of_isOpenImmersion (𝟙 X) hX

/-- **Morphisms out of the empty adic space are locally of finite presentation**: the condition
quantifies over the points of the source. -/
theorem LocallyOfFinitePresentation.of_isEmpty (f : X ⟶ Y) [IsEmpty X.obj] :
    LocallyOfFinitePresentation f :=
  (locallyOfFinitePresentation_iff_chartLocally f).mpr <| (chartLocally_iff _).mpr isEmptyElim

end AdicSpace

end TauCeti
