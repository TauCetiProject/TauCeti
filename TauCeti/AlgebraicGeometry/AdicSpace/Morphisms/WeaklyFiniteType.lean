/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Morphisms.Adic
public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.LocallyOfFiniteType.OpenImmersion
public import TauCeti.RingTheory.Huber.TopologicallyFiniteType.Adic

/-!
# Morphisms of adic spaces locally of weakly finite type

A morphism `f : X ⟶ Y` of adic spaces is *locally of weakly finite type* (Wedhorn, Definition
8.48(1); Huber 1994, §3) if every point of `X` has an open neighbourhood `U`, mapped by `f` into
an open `V` of `Y`, such that `U ≅ Spa(B, B⁺)` and `V ≅ Spa(A, A⁺)` for Huber pairs, `B` complete
and Hausdorff, under which `f` restricted to `U → V` is the morphism induced by a morphism of
Huber pairs `(A, A⁺) → (B, B⁺)` whose ring homomorphism `A → B` is topologically of finite type
(`TauCeti.Huber.IsTopologicallyFiniteType`). No condition is put on the plus rings: this is what
distinguishes it from `TauCeti.PreAdicSpace.LocallyOfFiniteType`, which asks the morphism of
pairs itself to be topologically of finite type (Wedhorn, Definition 8.42).

The class sits in Huber's hierarchy of finiteness conditions (Huber 1996, §1.2): a morphism
locally of finite type is locally of weakly finite type, and a morphism locally of weakly finite
type is adic, because a homomorphism topologically of finite type is adic. Identities, open
immersions and isomorphisms are locally of weakly finite type, as is the morphism of affinoid adic
spaces induced by a morphism of Huber pairs whose ring homomorphism is topologically of finite
type. Being locally of weakly finite type is not a global condition on affinoids: the ring
homomorphism of an affinoid morphism locally of weakly finite type need not be topologically of
finite type (Wedhorn, Remark 8.52), so the last statement has no converse.

## Main definitions

* `TauCeti.AdicSpace.LocallyOfWeaklyFiniteType`: morphisms of adic spaces locally of weakly finite
  type.

## Main results

* `TauCeti.AdicSpace.LocallyOfWeaklyFiniteType.isAdic`: a morphism locally of weakly finite type
  is adic.
* `TauCeti.PreAdicSpace.LocallyOfFiniteType.locallyOfWeaklyFiniteType`: a morphism of adic spaces
  locally of finite type is locally of weakly finite type.
* `TauCeti.AdicSpace.LocallyOfWeaklyFiniteType.of_isOpenImmersion`: open immersions are locally of
  weakly finite type.
* `TauCeti.AdicSpace.LocallyOfWeaklyFiniteType.containsIdentities`,
  `TauCeti.AdicSpace.LocallyOfWeaklyFiniteType.respectsIso`: identities are locally of weakly finite
  type, and the property is invariant under isomorphisms of the source and of the target; so
  isomorphisms are locally of weakly finite type (`CategoryTheory.MorphismProperty.of_isIso`).
* `TauCeti.AdicSpace.locallyOfWeaklyFiniteType_presentationLimitPreAdicSpaceComap`: the morphism
  `Spa(B, B⁺) ⟶ Spa(A, A⁺)` induced by a morphism of Huber pairs whose ring homomorphism is
  topologically of finite type is locally of weakly finite type.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Definitions 8.42 and 8.48, Remark 8.52.
* R. Huber, *A generalization of formal schemes and rigid analytic varieties*, Math. Z. 217
  (1994), §3.
* R. Huber, *Étale cohomology of rigid analytic varieties and adic spaces*, Aspects of
  Mathematics E30 (1996), §1.2.
-/

public section

open CategoryTheory TopologicalSpace

namespace TauCeti

open Huber

universe u

namespace AdicSpace

open PreAdicSpace ValuationSpectrum

/-- **Morphisms locally of weakly finite type** (Wedhorn, Definition 8.48(1)): a morphism
`f : X ⟶ Y` of adic spaces is *locally of weakly finite type* when every point `x` of `X` has an
open neighbourhood `U`, mapped by `f` into an open `V` of `Y`, together with Huber pairs `(A, A⁺)`
and `(B, B⁺)`, `B` complete and Hausdorff with `Spa(B, B⁺)` having a sheaf as structure presheaf,
a morphism `φ : (A, A⁺) → (B, B⁺)` whose ring homomorphism is topologically of finite type, and
isomorphisms identifying `X` restricted to `U` with `Spa(B, B⁺)` and `Y` restricted to `V` with
`Spa(A, A⁺)`, under which `f` becomes the morphism induced by `φ`; that is, `f` is chart-locally
topologically of finite type on rings (`TauCeti.PreAdicSpace.chartLocally`). -/
def LocallyOfWeaklyFiniteType : MorphismProperty AdicSpace.{u} := fun _ _ f ↦
  chartLocally (fun φ ↦ IsTopologicallyFiniteType φ.toRingHom) f.hom

variable {X Y : AdicSpace.{u}}

/-- Unfolding lemma for `TauCeti.AdicSpace.LocallyOfWeaklyFiniteType`. -/
theorem locallyOfWeaklyFiniteType_iff_chartLocally (f : X ⟶ Y) :
    LocallyOfWeaklyFiniteType f ↔
      chartLocally (fun φ ↦ IsTopologicallyFiniteType φ.toRingHom) f.hom :=
  Iff.rfl

/-- **A morphism locally of weakly finite type is adic** (Huber 1996, §1.2): on each chart it is
induced by a homomorphism topologically of finite type, which is adic. -/
theorem LocallyOfWeaklyFiniteType.isAdic {f : X ⟶ Y} (hf : LocallyOfWeaklyFiniteType f) :
    IsAdic f :=
  (isAdic_iff_chartLocally f).mpr <| chartLocally_mono (fun _ hφ ↦ hφ.isAdicHom)
    ((locallyOfWeaklyFiniteType_iff_chartLocally f).mp hf)

end AdicSpace

/-- **A morphism of adic spaces locally of finite type is locally of weakly finite type**: the ring
homomorphism of a morphism of Huber pairs topologically of finite type is topologically of finite
type. -/
theorem PreAdicSpace.LocallyOfFiniteType.locallyOfWeaklyFiniteType {X Y : AdicSpace.{u}}
    {f : X ⟶ Y} (hf : PreAdicSpace.LocallyOfFiniteType f.hom) :
    AdicSpace.LocallyOfWeaklyFiniteType f :=
  (AdicSpace.locallyOfWeaklyFiniteType_iff_chartLocally f).mpr <|
    PreAdicSpace.chartLocally_mono (fun _ hφ ↦ hφ.isTopologicallyFiniteType_toRingHom)
      ((locallyOfFiniteType_iff f.hom).mp hf)

namespace AdicSpace

open PreAdicSpace ValuationSpectrum

variable {X Y : AdicSpace.{u}}

/-- **Open immersions are locally of weakly finite type**: they are locally of finite type. -/
theorem LocallyOfWeaklyFiniteType.of_isOpenImmersion (f : X ⟶ Y)
    [PreAdicSpace.IsOpenImmersion f.hom] : LocallyOfWeaklyFiniteType f :=
  (locallyOfFiniteType_of_isOpenImmersion f.hom X.property).locallyOfWeaklyFiniteType

/-- **Identities are locally of weakly finite type.** -/
instance LocallyOfWeaklyFiniteType.containsIdentities :
    LocallyOfWeaklyFiniteType.{u}.ContainsIdentities where
  id_mem X := (locallyOfFiniteType_id X.property).locallyOfWeaklyFiniteType

/-- **Being locally of weakly finite type is invariant under isomorphisms** of the source and of
the target: it is the inverse image of a chart-local property along the inclusion of adic spaces
into pre-adic spaces. -/
instance LocallyOfWeaklyFiniteType.respectsIso :
    MorphismProperty.RespectsIso (@LocallyOfWeaklyFiniteType.{u}) :=
  MorphismProperty.RespectsIso.inverseImage
    (chartLocally fun φ ↦ IsTopologicallyFiniteType φ.toRingHom)
    (ObjectProperty.ι PreAdicSpace.isAdic)

/-- **Affinoid morphisms**: for a morphism of Huber pairs `φ : (A, A⁺) → (B, B⁺)` with `B`
complete and Hausdorff, between pairs whose adic spectra are adic spaces, the morphism
`Spa(B, B⁺) ⟶ Spa(A, A⁺)` induced by `φ` is locally of weakly finite type as soon as the ring
homomorphism of `φ` is topologically of finite type, witnessed over the whole of both spectra.
The converse fails in general (Wedhorn, Remark 8.52). -/
theorem locallyOfWeaklyFiniteType_presentationLimitPreAdicSpaceComap {A : Type u} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A] {B : Type u} [CommRing B]
    [UniformSpace B] [IsUniformAddGroup B] [IsTopologicalRing B] [CompleteSpace B] [T2Space B]
    [IsHuberRing B] {S : Pair A} {T : Pair B} (P : PairOfDefinition A) (P' : PairOfDefinition B)
    (hP : P.ringOfDefinition ≤ S.plus) (hP' : P'.ringOfDefinition ≤ T.plus)
    (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa T.plus))
      (presentationLimitPresheaf P' T.plus))
    (hA : PreAdicSpace.isAdic (presentationLimitPreAdicSpace P S.plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem hP)) (φ : Pair.Hom S T)
    (hφ : IsTopologicallyFiniteType φ.toRingHom) :
    LocallyOfWeaklyFiniteType (X := ⟨_, isAdic_presentationLimitPreAdicSpace P' T.plus
        T.isRingOfIntegralElements.isPowerBounded_of_mem hP' hsheaf⟩) (Y := ⟨_, hA⟩)
      (ObjectProperty.homMk (presentationLimitPreAdicSpaceComap φ.toRingHom
        φ.continuous_toRingHom φ.map_mem_plus S.isRingOfIntegralElements.isPowerBounded_of_mem
        T.isRingOfIntegralElements.isPowerBounded_of_mem hP hP' hsheaf)) := by
  rw [locallyOfWeaklyFiniteType_iff_chartLocally, ObjectProperty.homMk_hom]
  exact chartLocally_presentationLimitPreAdicSpaceComap P P' hP hP' hsheaf φ hφ

end AdicSpace

end TauCeti
