/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.SheafyRing
public import TauCeti.RingTheory.Huber.TensorProduct.Plus
import TauCeti.RingTheory.Huber.TensorProduct.TopologicallyFiniteType

/-!
# Sheafiness of completed tensor products over stably sheafy Huber rings

If `B` is a complete Hausdorff stably sheafy Huber ring (`TauCeti.Huber.IsStablySheafyRing`),
`A → B` is an adic homomorphism, and `A → C` is topologically of finite type
(`TauCeti.Huber.IsTopologicallyFiniteType`), then the left coprojection `B → B ⊗̂_A C` is
topologically of finite type (`TauCeti.Huber.CompletedTensor.isTopologicallyFiniteType_inl`), so the
completed tensor ring `B ⊗̂_A C` is sheafy (`TauCeti.Huber.IsSheafyRing`) and the completed tensor
pair `(B, B⁺) ⊗̂_A (C, C⁺)` satisfies `TauCeti.Huber.IsSheafyForEveryPresentation`. Symmetric
statements hold when `C` is stably sheafy and `A → B` is topologically of finite type.

This is the ring- and pair-level sheafiness input for unconditional fibre products of affinoid adic
spaces over a stably sheafy factor (Wedhorn, Theorem 8.56).

## Main results

* `TauCeti.Huber.isSheafyRing_completedTensor_of_isStablySheafyRing_left`,
  `TauCeti.Huber.isSheafyRing_completedTensor_of_isStablySheafyRing_right`: `B ⊗̂_A C` is a sheafy
  Huber ring when one factor is complete, Hausdorff and stably sheafy and the opposite structure map
  is topologically of finite type.
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

universe u v w

/-- **Sheafiness of a completed tensor product over a stably sheafy left factor** (local ring-level
step of Wedhorn, Theorem 8.56): if `B` is complete, Hausdorff and stably sheafy, `A → B` is adic,
and `A → C` is topologically of finite type, then the completed tensor ring `B ⊗̂_A C` is sheafy. -/
theorem isSheafyRing_completedTensor_of_isStablySheafyRing_left
    {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
    {B : Type v} [CommRing B] [UniformSpace B] [IsUniformAddGroup B] [IsTopologicalRing B]
    [CompleteSpace B] [T0Space B] [IsHuberRing B]
    {C : Type w} [CommRing C] [TopologicalSpace C] [IsTopologicalRing C]
    [Algebra A B] [Algebra A C] [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap A C)]
    (hB : IsStablySheafyRing.{v, max v w} B)
    (hC : IsTopologicallyFiniteType (algebraMap A C)) :
    IsSheafyRing (CompletedTensor A B C) :=
  isStablySheafyRing_iff.mp hB (CompletedTensor A B C) _
    ((CompletedTensor.isTopologicallyFiniteType_inl hC).comp_ringEquiv
      (Completion.completeRingEquivSelf B)
      (Completion.uniformContinuous_completeRingEquivSelf B).continuous
      (Completion.uniformContinuous_completeRingEquivSelf_symm B).continuous)

/-- **Sheafiness of a completed tensor product over a stably sheafy right factor**: symmetric form
of `isSheafyRing_completedTensor_of_isStablySheafyRing_left` when `C` is stably sheafy and `A → B`
is topologically of finite type. -/
theorem isSheafyRing_completedTensor_of_isStablySheafyRing_right
    {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
    {B : Type v} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    {C : Type w} [CommRing C] [UniformSpace C] [IsUniformAddGroup C] [IsTopologicalRing C]
    [CompleteSpace C] [T0Space C] [IsHuberRing C]
    [Algebra A B] [Algebra A C] [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap A C)]
    (hC : IsStablySheafyRing.{w, max v w} C)
    (hB : IsTopologicallyFiniteType (algebraMap A B)) :
    IsSheafyRing (CompletedTensor A B C) :=
  isStablySheafyRing_iff.mp hC (CompletedTensor A B C) _
    ((CompletedTensor.isTopologicallyFiniteType_inr hB).comp_ringEquiv
      (Completion.completeRingEquivSelf C)
      (Completion.uniformContinuous_completeRingEquivSelf C).continuous
      (Completion.uniformContinuous_completeRingEquivSelf_symm C).continuous)

/-- **Pair-level sheafiness of `(B, B⁺) ⊗̂_A (C, C⁺)`** when `B` is complete, Hausdorff and stably
sheafy and `A → C` is topologically of finite type. -/
theorem isSheafyForEveryPresentation_completedTensor_of_isStablySheafyRing_left
    {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
    {B : Type v} [CommRing B] [UniformSpace B] [IsUniformAddGroup B] [IsTopologicalRing B]
    [CompleteSpace B] [T0Space B] [IsHuberRing B]
    {C : Type w} [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsHuberRing C]
    [Algebra A B] [Algebra A C] [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap A C)]
    (T : Pair B) (U : Pair C)
    (hB : IsStablySheafyRing.{v, max v w} B)
    (hC : IsTopologicallyFiniteType (algebraMap A C)) :
    IsSheafyForEveryPresentation (T.completedTensor A U).plus :=
  (isSheafyRing_completedTensor_of_isStablySheafyRing_left hB hC).isSheafyForEveryPresentation
    (T.completedTensor A U).isRingOfIntegralElements

/-- **Pair-level sheafiness of `(B, B⁺) ⊗̂_A (C, C⁺)`** when `C` is complete, Hausdorff and stably
sheafy and `A → B` is topologically of finite type. -/
theorem isSheafyForEveryPresentation_completedTensor_of_isStablySheafyRing_right
    {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
    {B : Type v} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B]
    {C : Type w} [CommRing C] [UniformSpace C] [IsUniformAddGroup C] [IsTopologicalRing C]
    [CompleteSpace C] [T0Space C] [IsHuberRing C]
    [Algebra A B] [Algebra A C] [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap A C)]
    (T : Pair B) (U : Pair C)
    (hC : IsStablySheafyRing.{w, max v w} C)
    (hB : IsTopologicallyFiniteType (algebraMap A B)) :
    IsSheafyForEveryPresentation (T.completedTensor A U).plus :=
  (isSheafyRing_completedTensor_of_isStablySheafyRing_right hC hB).isSheafyForEveryPresentation
    (T.completedTensor A U).isRingOfIntegralElements

end TauCeti.Huber
