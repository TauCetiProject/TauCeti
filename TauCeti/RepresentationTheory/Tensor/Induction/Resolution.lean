/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Resolution.Graded
public import TauCeti.RepresentationTheory.Tensor.Induction.Smooth

/-!
# Tensor induction of the total coinduced resolution

Let `U` be a compact open finite-index subgroup of a topological group `G`, and let `A` be a
smooth discrete `U`-representation.  The shifted coinduced resolution of `A` has a smooth
discrete total object, so it can itself be tensor-induced from `U` to `G`.  This file names that
object and its augmentation from the tensor induction of `A`.

On a pure tensor, the augmentation applies the ordinary coinduced-resolution augmentation in
every coset coordinate, and the construction is natural in `A`.  This augmented object is the
input for a resolution-level construction of the Evens norm.  Compatibility with changing the
transversal is the naturality of `TauCeti.smoothTensorInducedChangeTransversalIso`, applied to
the components of the augmentation.

## Main definitions

* `TauCeti.smoothTensorInducedGradedResolutionFunctor`: tensor induction of the total shifted
  coinduced resolution, functorially in the coefficients.
* `TauCeti.smoothTensorInducedGradedResolutionAugmentationApp`: the tensor-induced augmentation
  of a single coefficient object.
* `TauCeti.smoothTensorInducedGradedResolutionAugmentation`: the natural tensor-induced
  augmentation.

## References

* L. Evens, *A generalization of the transfer map in the cohomology of groups*,
  Transactions of the American Mathematical Society 108 (1963), Sections 2--5.
-/

public section

open CategoryTheory
open scoped TensorProduct

universe u v w

namespace TauCeti

variable {R : Type u} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (U : Subgroup G) (hU : IsOpen (U : Set G)) (s : U.LeftTransversal) [U.FiniteIndex]
  [CompactSpace U]

/-- Tensor induction from `U` to `G` of the total shifted coinduced resolution, functorially in
the smooth discrete coefficient object. -/
@[expose] noncomputable def smoothTensorInducedGradedResolutionFunctor :
    SmoothDiscreteTopRep.{u, v, max v w} R U ⥤
      SmoothDiscreteTopRep.{u, v, max u v w} R G :=
  smoothGradedResolutionFunctor ⋙ smoothTensorInductionFunctor R G U hU s

/-- The object map of the tensor-induced total resolution tensor-induces the total resolution of
the coefficient object.

This is not a simp lemma: rewriting the objects would take the pure-tensor evaluation lemma
`smoothTensorInducedGradedResolutionAugmentationApp_apply_tprod` out of simp-normal form. -/
theorem smoothTensorInducedGradedResolutionFunctor_obj
    (A : SmoothDiscreteTopRep.{u, v, max v w} R U) :
    (smoothTensorInducedGradedResolutionFunctor U hU s).obj A =
      (smoothTensorInductionFunctor R G U hU s).obj (smoothGradedResolutionFunctor.obj A) :=
  rfl

/-- The morphism map of the tensor-induced total resolution tensor-induces the induced map of
total resolutions. -/
@[simp]
theorem smoothTensorInducedGradedResolutionFunctor_map
    {A B : SmoothDiscreteTopRep.{u, v, max v w} R U} (f : A ⟶ B) :
    (smoothTensorInducedGradedResolutionFunctor U hU s).map f =
      (smoothTensorInductionFunctor R G U hU s).map (smoothGradedResolutionFunctor.map f) :=
  rfl

/-- Tensor induction of the coefficient augmentation into the total shifted coinduced
resolution.

The source is written in the simp-normal form produced by `smoothTensorInductionFunctor_obj`, so
that the pure-tensor computation rule below can be a simp lemma. -/
noncomputable def smoothTensorInducedGradedResolutionAugmentationApp
    (A : SmoothDiscreteTopRep.{u, v, max v w} R U) :
    (toSmoothDiscrete R G).obj
        (DiscreteRep.tensorInduced U hU s ((ofSmoothDiscrete R U).obj A)) ⟶
      (smoothTensorInducedGradedResolutionFunctor U hU s).obj A :=
  (smoothTensorInductionFunctor R G U hU s).map (smoothGradedResolutionAugmentationApp A)

/-- On a pure tensor, the tensor-induced augmentation applies the coinduced-resolution
augmentation in every coset coordinate. -/
@[simp]
theorem smoothTensorInducedGradedResolutionAugmentationApp_apply_tprod
    (A : SmoothDiscreteTopRep.{u, v, max v w} R U) (x : G ⧸ U → A.obj.V) :
    (smoothTensorInducedGradedResolutionAugmentationApp U hU s A).hom.hom
        (PiTensorProduct.tprod R x) =
      PiTensorProduct.tprod R fun i ↦ A.obj.gradedResolutionAugmentation (x i) :=
  -- The discrete functor is sandwiched between `ofSmoothDiscrete` and `toSmoothDiscrete`, whose
  -- round trips on maps are the identity by definition because `discreteRepEquivSmoothTopRep`
  -- has identity unit and counit components.
  (Representation.IntertwiningMap.tensorInduced_apply_tprod
    ((ofSmoothDiscrete R U).map (smoothGradedResolutionAugmentationApp A)) s x).trans <|
      congrArg (PiTensorProduct.tprod R) <| funext fun i ↦
        smoothGradedResolutionAugmentationApp_hom_apply A (x i)

/-- The tensor-induced coefficient augmentations, as a natural transformation into the
tensor-induced total resolution: the right whiskering of `smoothGradedResolutionAugmentation` by
smooth tensor induction. -/
noncomputable def smoothTensorInducedGradedResolutionAugmentation :
    smoothTensorInductionFunctor R G U hU s ⟶
      smoothTensorInducedGradedResolutionFunctor U hU s :=
  Functor.whiskerRight smoothGradedResolutionAugmentation
    (smoothTensorInductionFunctor R G U hU s)

/-- The component of the tensor-induced augmentation is the named tensor-induced augmentation. -/
@[simp]
theorem smoothTensorInducedGradedResolutionAugmentation_app
    (A : SmoothDiscreteTopRep.{u, v, max v w} R U) :
    (smoothTensorInducedGradedResolutionAugmentation U hU s).app A =
      smoothTensorInducedGradedResolutionAugmentationApp U hU s A := by
  rw [smoothTensorInducedGradedResolutionAugmentation, Functor.whiskerRight_app,
    smoothGradedResolutionAugmentation_app, smoothTensorInducedGradedResolutionAugmentationApp]

end TauCeti
