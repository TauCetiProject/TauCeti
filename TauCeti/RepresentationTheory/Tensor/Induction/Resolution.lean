/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Resolution.Graded
public import TauCeti.RepresentationTheory.Tensor.Induction.ChangeTransversal.Discrete

/-!
# Tensor induction of the total coinduced resolution

Let `U` be an open finite-index subgroup of a compact topological group `G`, and let `A` be a
smooth discrete `U`-representation.  The shifted coinduced resolution of `A` has a smooth
discrete total object, so it can itself be tensor-induced from `U` to `G`.  This file names that
object and its augmentation from the tensor induction of `A`.

On a pure tensor, the augmentation applies the ordinary coinduced-resolution augmentation in
every coset coordinate.  The construction is natural in `A` and is compatible with changing the
transversal.  These facts are the augmented-object input for the resolution-level construction
of the Evens norm: its tensor differential is defined on the target named here, while
transversal-independence uses the compatibility proved here.

## Main definitions

* `TauCeti.smoothTensorInducedGradedResolutionFunctor`: tensor induction of the total shifted
  coinduced resolution, functorially in the coefficients.
* `TauCeti.smoothTensorInducedGradedResolutionAugmentation`: the natural tensor-induced
  augmentation.
* `TauCeti.smoothTensorInducedGradedResolutionChangeTransversalIso`: independence of the chosen
  transversal at the level of augmented objects.

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
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  (U : Subgroup G) (hU : IsOpen (U : Set G)) (s : U.LeftTransversal) [U.FiniteIndex]

/-- Tensor induction from `U` to `G` of the total shifted coinduced resolution, functorially in
the smooth discrete coefficient object. -/
@[expose] noncomputable def smoothTensorInducedGradedResolutionFunctor :
    SmoothDiscreteTopRep.{u, v, max v w} R U ⥤
      SmoothDiscreteTopRep.{u, v, max u v w} R G := by
  letI : CompactSpace U :=
    isCompact_iff_compactSpace.mp (U.isClosed_of_isOpen hU).isCompact
  exact smoothGradedResolutionFunctor ⋙ smoothTensorInductionFunctor R G U hU s

/-- Tensor induction of the coefficient augmentation into the total shifted coinduced
resolution. -/
@[expose] noncomputable def smoothTensorInducedGradedResolutionAugmentationApp
    (A : SmoothDiscreteTopRep.{u, v, max v w} R U) :
    (toSmoothDiscrete R G).obj
        (DiscreteRep.tensorInduced U hU s ((ofSmoothDiscrete R U).obj A)) ⟶
      (smoothTensorInducedGradedResolutionFunctor U hU s).obj A := by
  letI : CompactSpace U :=
    isCompact_iff_compactSpace.mp (U.isClosed_of_isOpen hU).isCompact
  exact (smoothTensorInductionFunctor R G U hU s).map
    (smoothGradedResolutionAugmentationApp A)

/-- On a pure tensor, the tensor-induced augmentation applies the coinduced-resolution
augmentation in every coset coordinate. -/
@[simp]
theorem smoothTensorInducedGradedResolutionAugmentationApp_apply_tprod
    (A : SmoothDiscreteTopRep.{u, v, max v w} R U) (x : G ⧸ U → A.obj.V) :
    ((smoothTensorInducedGradedResolutionAugmentationApp U hU s A :
        (toSmoothDiscrete R G).obj
            (DiscreteRep.tensorInduced U hU s ((ofSmoothDiscrete R U).obj A)) ⟶
          (smoothTensorInducedGradedResolutionFunctor U hU s).obj A).hom.hom
      (PiTensorProduct.tprod R x)) =
      PiTensorProduct.tprod R fun i ↦ A.obj.gradedResolutionAugmentation (x i) := by
  let _ : CompactSpace U :=
    isCompact_iff_compactSpace.mp (U.isClosed_of_isOpen hU).isCompact
  calc
    _ = PiTensorProduct.tprod R fun i ↦
        ((ofSmoothDiscrete R U).map
          (smoothGradedResolutionAugmentationApp A)).toLinearMap (x i) :=
      Representation.IntertwiningMap.tensorInduced_apply_tprod
        ((ofSmoothDiscrete R U).map (smoothGradedResolutionAugmentationApp A)) s x
    _ = _ := by
      congr 1
      funext i
      exact smoothGradedResolutionAugmentationApp_hom_apply A (x i)

/-- The tensor-induced augmentation is natural in the coefficient object. -/
@[reassoc]
theorem smoothTensorInducedGradedResolutionAugmentationApp_naturality
    {A B : SmoothDiscreteTopRep.{u, v, max v w} R U} (f : A ⟶ B) :
    smoothTensorInducedGradedResolutionAugmentationApp U hU s A ≫
        (smoothTensorInducedGradedResolutionFunctor U hU s).map f =
      (smoothTensorInductionFunctor R G U hU s).map f ≫
        smoothTensorInducedGradedResolutionAugmentationApp U hU s B := by
  let _ : CompactSpace U :=
    isCompact_iff_compactSpace.mp (U.isClosed_of_isOpen hU).isCompact
  change (smoothTensorInductionFunctor R G U hU s).map
      (smoothGradedResolutionAugmentationApp A) ≫
        (smoothTensorInductionFunctor R G U hU s).map
          ((smoothGradedResolutionFunctor (R := R) (G := U)).map f) =
      (smoothTensorInductionFunctor R G U hU s).map f ≫
      (smoothTensorInductionFunctor R G U hU s).map
        (smoothGradedResolutionAugmentationApp B)
  rw [
    ← (smoothTensorInductionFunctor R G U hU s).map_comp,
    ← (smoothTensorInductionFunctor R G U hU s).map_comp]
  apply (smoothTensorInductionFunctor R G U hU s).congr_map
  exact smoothGradedResolutionAugmentationApp_naturality f

/-- The tensor-induced coefficient augmentations form a natural transformation into the
tensor-induced total resolution. -/
@[expose] noncomputable def smoothTensorInducedGradedResolutionAugmentation :
    smoothTensorInductionFunctor R G U hU s ⟶
      smoothTensorInducedGradedResolutionFunctor U hU s where
  app A := smoothTensorInducedGradedResolutionAugmentationApp U hU s A
  naturality := fun {_ _} f ↦
    (smoothTensorInducedGradedResolutionAugmentationApp_naturality U hU s f).symm

variable (t : U.LeftTransversal)

/-- Changing the transversal identifies the two tensor-induced total resolutions. -/
@[expose] noncomputable def smoothTensorInducedGradedResolutionChangeTransversalIso
    (A : SmoothDiscreteTopRep.{u, v, max v w} R U) :
    (smoothTensorInducedGradedResolutionFunctor U hU t).obj A ≅
      (smoothTensorInducedGradedResolutionFunctor U hU s).obj A := by
  letI : CompactSpace U :=
    isCompact_iff_compactSpace.mp (U.isClosed_of_isOpen hU).isCompact
  exact smoothTensorInducedChangeTransversalIso U hU s t
    ((smoothGradedResolutionFunctor (R := R) (G := U)).obj A)

/-- Changing the transversal commutes with the tensor-induced augmentation. -/
@[reassoc]
theorem smoothTensorInducedGradedResolutionAugmentationApp_changeTransversal
    (A : SmoothDiscreteTopRep.{u, v, max v w} R U) :
    smoothTensorInducedGradedResolutionAugmentationApp U hU t A ≫
        (smoothTensorInducedGradedResolutionChangeTransversalIso U hU s t A).hom =
      (smoothTensorInducedChangeTransversalIso U hU s t A).hom ≫
        smoothTensorInducedGradedResolutionAugmentationApp U hU s A := by
  let _ : CompactSpace U :=
    isCompact_iff_compactSpace.mp (U.isClosed_of_isOpen hU).isCompact
  change (smoothTensorInductionFunctor R G U hU t).map
      (smoothGradedResolutionAugmentationApp A) ≫
        (smoothTensorInducedChangeTransversalIso U hU s t
          ((smoothGradedResolutionFunctor (R := R) (G := U)).obj A)).hom =
    (smoothTensorInducedChangeTransversalIso U hU s t A).hom ≫
      (smoothTensorInductionFunctor R G U hU s).map
        (smoothGradedResolutionAugmentationApp A)
  exact smoothTensorInducedChangeTransversalIso_hom_naturality U hU s t
    (smoothGradedResolutionAugmentationApp A)

end TauCeti
