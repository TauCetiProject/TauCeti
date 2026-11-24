/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.SheafyRing
public import TauCeti.RingTheory.Huber.TensorProduct.Plus
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.StablySheafy
import TauCeti.RingTheory.Huber.TensorProduct.TopologicallyFiniteType

/-!
# Sheafiness of completed tensor products over stably sheafy Huber rings

If `B` is a stably sheafy Huber ring (`TauCeti.Huber.IsStablySheafyRing`), `A → B` is an adic
homomorphism, and `A → C` is topologically of finite type
(`TauCeti.Huber.IsTopologicallyFiniteType`), then the left coprojection `B → B ⊗̂_A C` is
topologically of finite type (`TauCeti.Huber.CompletedTensor.isTopologicallyFiniteType_inl`), so the
completed tensor ring `B ⊗̂_A C` is again stably sheafy
(`TauCeti.Huber.isStablySheafyRing_completedTensor_of_isStablySheafyRing_left`), hence sheafy
(`TauCeti.Huber.IsSheafyRing`), and the completed tensor pair `(B, B⁺) ⊗̂_A (C, C⁺)` satisfies
`TauCeti.Huber.IsSheafyForEveryPresentation`. Symmetric statements hold when `C` is stably sheafy
and `A → B` is topologically of finite type.

This is the ring- and pair-level sheafiness input for unconditional fibre products of affinoid adic
spaces over a stably sheafy factor and for base-change permanence of stable sheafiness (Wedhorn,
Theorem 8.56).

## Main results

* `TauCeti.Huber.isStablySheafyRing_completedTensor_of_isStablySheafyRing_left`,
  `TauCeti.Huber.isStablySheafyRing_completedTensor_of_isStablySheafyRing_right`: `B ⊗̂_A C` is a
  stably sheafy Huber ring when one factor is stably sheafy and the opposite structure map is
  topologically of finite type (without completeness or Hausdorffness hypotheses on the stably
  sheafy factor).
* `TauCeti.Huber.isSheafyRing_completedTensor_of_isStablySheafyRing_left`,
  `TauCeti.Huber.isSheafyRing_completedTensor_of_isStablySheafyRing_right`: `B ⊗̂_A C` is a sheafy
  Huber ring when one factor is stably sheafy and the opposite structure map is topologically of
  finite type.
* `TauCeti.Huber.isSheafyForEveryPresentation_completedTensor_of_isStablySheafyRing_left`,
  `TauCeti.Huber.isSheafyForEveryPresentation_completedTensor_of_isStablySheafyRing_right`: the
  corresponding pair-level `IsSheafyForEveryPresentation` statements for `(B, B⁺) ⊗̂_A (C, C⁺)`.

## References

* R. Huber, *A generalization of formal schemes and rigid analytic varieties*, Math. Z. 217
  (1994), §3, Proposition 3.7.
* R. Huber, *Étale cohomology of rigid analytic varieties and adic spaces*, Aspects of
  Mathematics E30 (1996), §1.2, Proposition 1.2.2.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), §8.6, Theorem 8.56.
-/

public section

open UniformSpace

namespace TauCeti.Huber

universe u v w t

/-- **Completed base change preserves stable sheafiness over a stably sheafy left factor**: if `B`
is a stably sheafy Huber ring, `A → B` is adic, and `A → C` is topologically of finite type,
then `B ⊗̂_A C` is stably sheafy. Neither completeness nor Hausdorffness of `B` is required. -/
theorem isStablySheafyRing_completedTensor_of_isStablySheafyRing_left
    {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
    {B : Type v} [CommRing B] [UniformSpace B] [IsUniformAddGroup B] [IsTopologicalRing B]
    [IsHuberRing B]
    {C : Type w} [CommRing C] [TopologicalSpace C] [IsTopologicalRing C]
    [Algebra A B] [Algebra A C] [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap A C)]
    (hB : IsStablySheafyRing.{v, t} B)
    (hC : IsTopologicallyFiniteType (algebraMap A C)) :
    IsStablySheafyRing.{max v w, t} (CompletedTensor A B C) :=
  hB.of_isTopologicallyFiniteType (CompletedTensor.isTopologicallyFiniteType_inl hC)

/-- **Completed base change preserves stable sheafiness over a stably sheafy right factor**:
symmetric form of `isStablySheafyRing_completedTensor_of_isStablySheafyRing_left` when `C` is stably
sheafy and `A → B` is topologically of finite type. -/
theorem isStablySheafyRing_completedTensor_of_isStablySheafyRing_right
    {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
    {B : Type v} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    {C : Type w} [CommRing C] [UniformSpace C] [IsUniformAddGroup C] [IsTopologicalRing C]
    [IsHuberRing C]
    [Algebra A B] [Algebra A C] [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap A C)]
    (hC : IsStablySheafyRing.{w, t} C)
    (hB : IsTopologicallyFiniteType (algebraMap A B)) :
    IsStablySheafyRing.{max v w, t} (CompletedTensor A B C) :=
  hC.of_isTopologicallyFiniteType (CompletedTensor.isTopologicallyFiniteType_inr hB)

/-- **Sheafiness of a completed tensor product over a stably sheafy left factor** (local ring-level
step of Wedhorn, Theorem 8.56): if `B` is a stably sheafy Huber ring, `A → B` is adic, and
`A → C` is topologically of finite type, then the completed tensor ring `B ⊗̂_A C` is sheafy.
Neither completeness nor Hausdorffness of `B` is required. -/
theorem isSheafyRing_completedTensor_of_isStablySheafyRing_left
    {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
    {B : Type v} [CommRing B] [UniformSpace B] [IsUniformAddGroup B] [IsTopologicalRing B]
    [IsHuberRing B]
    {C : Type w} [CommRing C] [TopologicalSpace C] [IsTopologicalRing C]
    [Algebra A B] [Algebra A C] [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap A C)]
    (hB : IsStablySheafyRing.{v, max v w} B)
    (hC : IsTopologicallyFiniteType (algebraMap A C)) :
    IsSheafyRing (CompletedTensor A B C) :=
  (isStablySheafyRing_completedTensor_of_isStablySheafyRing_left hB hC).isSheafyRing

/-- **Sheafiness of a completed tensor product over a stably sheafy right factor**: symmetric form
of `isSheafyRing_completedTensor_of_isStablySheafyRing_left` when `C` is stably sheafy and `A → B`
is topologically of finite type. -/
theorem isSheafyRing_completedTensor_of_isStablySheafyRing_right
    {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
    {B : Type v} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    {C : Type w} [CommRing C] [UniformSpace C] [IsUniformAddGroup C] [IsTopologicalRing C]
    [IsHuberRing C]
    [Algebra A B] [Algebra A C] [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap A C)]
    (hC : IsStablySheafyRing.{w, max v w} C)
    (hB : IsTopologicallyFiniteType (algebraMap A B)) :
    IsSheafyRing (CompletedTensor A B C) :=
  (isStablySheafyRing_completedTensor_of_isStablySheafyRing_right hC hB).isSheafyRing

/-- **Pair-level sheafiness of `(B, B⁺) ⊗̂_A (C, C⁺)`** when `B` is stably sheafy and `A → C` is
topologically of finite type. -/
theorem isSheafyForEveryPresentation_completedTensor_of_isStablySheafyRing_left
    {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
    {B : Type v} [CommRing B] [UniformSpace B] [IsUniformAddGroup B] [IsTopologicalRing B]
    [IsHuberRing B]
    {C : Type w} [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsHuberRing C]
    [Algebra A B] [Algebra A C] [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap A C)]
    (T : Pair B) (U : Pair C)
    (hB : IsStablySheafyRing.{v, max v w} B)
    (hC : IsTopologicallyFiniteType (algebraMap A C)) :
    IsSheafyForEveryPresentation (T.completedTensor A U).plus :=
  (isSheafyRing_completedTensor_of_isStablySheafyRing_left hB hC).isSheafyForEveryPresentation
    (T.completedTensor A U).isRingOfIntegralElements

/-- **Pair-level sheafiness of `(B, B⁺) ⊗̂_A (C, C⁺)`** when `C` is stably sheafy and `A → B` is
topologically of finite type. -/
theorem isSheafyForEveryPresentation_completedTensor_of_isStablySheafyRing_right
    {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
    {B : Type v} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B]
    {C : Type w} [CommRing C] [UniformSpace C] [IsUniformAddGroup C] [IsTopologicalRing C]
    [IsHuberRing C]
    [Algebra A B] [Algebra A C] [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap A C)]
    (T : Pair B) (U : Pair C)
    (hC : IsStablySheafyRing.{w, max v w} C)
    (hB : IsTopologicallyFiniteType (algebraMap A B)) :
    IsSheafyForEveryPresentation (T.completedTensor A U).plus :=
  (isSheafyRing_completedTensor_of_isStablySheafyRing_right hC hB).isSheafyForEveryPresentation
    (T.completedTensor A U).isRingOfIntegralElements

end TauCeti.Huber
