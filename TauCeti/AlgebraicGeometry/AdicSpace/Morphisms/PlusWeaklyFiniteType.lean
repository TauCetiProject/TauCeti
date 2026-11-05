/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Morphisms.WeaklyFiniteType
public import TauCeti.RingTheory.Huber.TopologicallyFiniteType.PlusWeak

/-!
# Morphisms of adic spaces locally of +weakly finite type

A morphism `f : X ⟶ Y` of adic spaces is *locally of +weakly finite type* (Huber 1996,
Definition 1.2.1(ii)) if every point of `X` has an open neighbourhood `U`, mapped by `f` into an
open `V` of `Y`, such that `U ≅ Spa(B, B⁺)` and `V ≅ Spa(A, A⁺)` for Huber pairs, `B` complete and
Hausdorff, under which `f` restricted to `U → V` is the morphism induced by a morphism of Huber
pairs `φ : (A, A⁺) → (B, B⁺)` of +weakly finite type
(`TauCeti.Huber.Pair.Hom.IsPlusWeaklyFiniteType`): `A → B` is topologically of finite type, and
`B⁺` is the smallest ring of integral elements of `B` containing `φ(A⁺)` and a finite set.

This is the finiteness condition in Huber's definitions of proper morphisms (of +weakly finite
type, separated and universally closed) and of partially proper morphisms (locally of +weakly
finite type, separated and universally specializing). It sits in Huber's hierarchy of finiteness
conditions (Huber 1996, §1.2) between local finite type and local weak finite type: a morphism
locally of finite type is locally of +weakly finite type, since a morphism of Huber pairs
topologically of finite type is of +weakly finite type, and a morphism locally of +weakly finite
type is locally of weakly finite type, by forgetting the condition on the plus rings. Identities,
open immersions and isomorphisms are locally of +weakly finite type, as is the morphism of
affinoid adic spaces induced by a morphism of Huber pairs of +weakly finite type.

## Main definitions

* `TauCeti.AdicSpace.LocallyOfPlusWeaklyFiniteType`: morphisms of adic spaces locally of
  +weakly finite type.

## Main results

* `TauCeti.AdicSpace.LocallyOfPlusWeaklyFiniteType.locallyOfWeaklyFiniteType`: a morphism locally
  of +weakly finite type is locally of weakly finite type.
* `TauCeti.PreAdicSpace.LocallyOfFiniteType.locallyOfPlusWeaklyFiniteType`: a morphism of adic
  spaces locally of finite type is locally of +weakly finite type.
* `TauCeti.AdicSpace.LocallyOfPlusWeaklyFiniteType.of_isOpenImmersion`: open immersions are
  locally of +weakly finite type.
* `TauCeti.AdicSpace.LocallyOfPlusWeaklyFiniteType.containsIdentities`,
  `TauCeti.AdicSpace.LocallyOfPlusWeaklyFiniteType.respectsIso`: identities are locally of
  +weakly finite type, and the property is invariant under isomorphisms of the source and of the
  target; so isomorphisms are locally of +weakly finite type
  (`CategoryTheory.MorphismProperty.of_isIso`).
* `TauCeti.AdicSpace.locallyOfPlusWeaklyFiniteType_presentationLimitPreAdicSpaceComap`: the
  morphism `Spa(B, B⁺) ⟶ Spa(A, A⁺)` induced by a morphism of Huber pairs of +weakly finite type
  is locally of +weakly finite type.

## References

* R. Huber, *Étale cohomology of rigid analytic varieties and adic spaces*, Aspects of
  Mathematics E30 (1996), §1.2, Definition 1.2.1(ii), and §1.3, Definitions 1.3.2 and 1.3.3.
* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Definitions 8.42 and 8.48.
-/

public section

open CategoryTheory TopologicalSpace

namespace TauCeti

open Huber

universe u

namespace AdicSpace

open PreAdicSpace ValuationSpectrum

/-- **Morphisms locally of +weakly finite type** (Huber 1996, Definition 1.2.1(ii)): a morphism
`f : X ⟶ Y` of adic spaces is *locally of +weakly finite type* when every point `x` of `X` has an
open neighbourhood `U`, mapped by `f` into an open `V` of `Y`, together with Huber pairs `(A, A⁺)`
and `(B, B⁺)`, `B` complete and Hausdorff with `Spa(B, B⁺)` having a sheaf as structure presheaf,
a morphism `φ : (A, A⁺) → (B, B⁺)` of +weakly finite type, and isomorphisms identifying `X`
restricted to `U` with `Spa(B, B⁺)` and `Y` restricted to `V` with `Spa(A, A⁺)`, under which `f`
becomes the morphism induced by `φ`; that is, `f` is chart-locally of +weakly finite type
(`TauCeti.PreAdicSpace.chartLocally`). -/
def LocallyOfPlusWeaklyFiniteType : MorphismProperty AdicSpace.{u} := fun _ _ f ↦
  chartLocally (fun φ ↦ φ.IsPlusWeaklyFiniteType) f.hom

variable {X Y : AdicSpace.{u}}

/-- Unfolding lemma for `TauCeti.AdicSpace.LocallyOfPlusWeaklyFiniteType`. -/
theorem locallyOfPlusWeaklyFiniteType_iff_chartLocally (f : X ⟶ Y) :
    LocallyOfPlusWeaklyFiniteType f ↔ chartLocally (fun φ ↦ φ.IsPlusWeaklyFiniteType) f.hom :=
  Iff.rfl

/-- **A morphism locally of +weakly finite type is locally of weakly finite type** (Huber 1996,
§1.2): on each chart it is induced by a morphism of Huber pairs whose ring homomorphism is
topologically of finite type. -/
theorem LocallyOfPlusWeaklyFiniteType.locallyOfWeaklyFiniteType {f : X ⟶ Y}
    (hf : LocallyOfPlusWeaklyFiniteType f) : LocallyOfWeaklyFiniteType f :=
  (locallyOfWeaklyFiniteType_iff_chartLocally f).mpr <|
    chartLocally_mono (fun _ hφ ↦ hφ.isTopologicallyFiniteType_toRingHom)
      ((locallyOfPlusWeaklyFiniteType_iff_chartLocally f).mp hf)

end AdicSpace

/-- **A morphism of adic spaces locally of finite type is locally of +weakly finite type** (Huber
1996, §1.2): a morphism of Huber pairs topologically of finite type is of +weakly finite type. -/
theorem PreAdicSpace.LocallyOfFiniteType.locallyOfPlusWeaklyFiniteType {X Y : AdicSpace.{u}}
    {f : X ⟶ Y} (hf : PreAdicSpace.LocallyOfFiniteType f.hom) :
    AdicSpace.LocallyOfPlusWeaklyFiniteType f :=
  (AdicSpace.locallyOfPlusWeaklyFiniteType_iff_chartLocally f).mpr <|
    PreAdicSpace.chartLocally_mono (fun _ hφ ↦ hφ.isPlusWeaklyFiniteType)
      ((locallyOfFiniteType_iff f.hom).mp hf)

namespace AdicSpace

open PreAdicSpace ValuationSpectrum

variable {X Y : AdicSpace.{u}}

/-- **Open immersions are locally of +weakly finite type**: they are locally of finite type. -/
theorem LocallyOfPlusWeaklyFiniteType.of_isOpenImmersion (f : X ⟶ Y)
    [PreAdicSpace.IsOpenImmersion f.hom] : LocallyOfPlusWeaklyFiniteType f :=
  (locallyOfFiniteType_of_isOpenImmersion f.hom X.property).locallyOfPlusWeaklyFiniteType

/-- **Identities are locally of +weakly finite type.** -/
instance LocallyOfPlusWeaklyFiniteType.containsIdentities :
    LocallyOfPlusWeaklyFiniteType.{u}.ContainsIdentities where
  id_mem X := (locallyOfFiniteType_id X.property).locallyOfPlusWeaklyFiniteType

/-- **Being locally of +weakly finite type is invariant under isomorphisms** of the source and of
the target: it is the inverse image of a chart-local property along the inclusion of adic spaces
into pre-adic spaces. -/
instance LocallyOfPlusWeaklyFiniteType.respectsIso :
    MorphismProperty.RespectsIso (@LocallyOfPlusWeaklyFiniteType.{u}) :=
  MorphismProperty.RespectsIso.inverseImage
    (chartLocally fun φ ↦ φ.IsPlusWeaklyFiniteType) (ObjectProperty.ι PreAdicSpace.isAdic)

/-- **Affinoid morphisms**: for a morphism of Huber pairs `φ : (A, A⁺) → (B, B⁺)` of +weakly
finite type with `B` complete and Hausdorff, between pairs whose adic spectra are adic spaces, the
morphism `Spa(B, B⁺) ⟶ Spa(A, A⁺)` induced by `φ` is locally of +weakly finite type, witnessed over
the whole of both spectra. -/
theorem locallyOfPlusWeaklyFiniteType_presentationLimitPreAdicSpaceComap {A : Type u}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A] {B : Type u}
    [CommRing B] [UniformSpace B] [IsUniformAddGroup B] [IsTopologicalRing B] [CompleteSpace B]
    [T2Space B] [IsHuberRing B] {S : Pair A} {T : Pair B} (P : PairOfDefinition A)
    (P' : PairOfDefinition B) (hP : P.ringOfDefinition ≤ S.plus)
    (hP' : P'.ringOfDefinition ≤ T.plus)
    (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa T.plus))
      (presentationLimitPresheaf P' T.plus))
    (hA : PreAdicSpace.isAdic (presentationLimitPreAdicSpace P S.plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem hP)) (φ : Pair.Hom S T)
    (hφ : φ.IsPlusWeaklyFiniteType) :
    LocallyOfPlusWeaklyFiniteType (X := ⟨_, isAdic_presentationLimitPreAdicSpace P' T.plus
        T.isRingOfIntegralElements.isPowerBounded_of_mem hP' hsheaf⟩) (Y := ⟨_, hA⟩)
      (ObjectProperty.homMk (presentationLimitPreAdicSpaceComap φ.toRingHom
        φ.continuous_toRingHom φ.map_mem_plus S.isRingOfIntegralElements.isPowerBounded_of_mem
        T.isRingOfIntegralElements.isPowerBounded_of_mem hP hP' hsheaf)) := by
  rw [locallyOfPlusWeaklyFiniteType_iff_chartLocally, ObjectProperty.homMk_hom]
  exact chartLocally_presentationLimitPreAdicSpaceComap P P' hP hP' hsheaf φ hφ

end AdicSpace

end TauCeti
