/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Tensor.Induction.Resolution
import TauCeti.RepresentationTheory.Homological.ContCohomology.Resolution.ChangeOfGroup

/-!
# Coefficient naturality of the tensor norm of a cocycle

A morphism `f : A ⟶ B` of smooth discrete representations of a compact open subgroup `U`
induces a map on their tensor-induced total resolutions. This map preserves total degree,
commutes with the slot-sum differentials, and carries diagonal tensors to diagonal tensors.
Consequently the norm of a cocycle commutes with coefficient maps, with tensor induction
applied to the coefficient map on the ambient group.

This allows a norm with tensor-induced coefficients to be normalized before taking a second
norm, as required when comparing direct tensor induction with tensor induction in stages.
No additivity of the norm is asserted. The coefficients need only satisfy `a + a = 0`;
the ring itself need not have characteristic two (in particular it can be `ℤ`).

## Main results

* `Subgroup.coeffMap_smoothTensorInducedDiagonalClass`: coefficient naturality of the norm of
  an invariant homogeneous cocycle, in every degree and for any transversal.

## References

* L. Evens, *A generalization of the transfer map in the cohomology of groups*,
  Trans. Amer. Math. Soc. **108** (1963), Sections 2–5 and §6, Proposition 1.
-/

public section

open CategoryTheory
open scoped TensorProduct

universe u v w

namespace Subgroup

open TauCeti

variable {R : Type u} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (U : Subgroup G) (hU : IsOpen (U : Set G)) (s : U.LeftTransversal)
  [U.FiniteIndex] [CompactSpace U]
  {A B : SmoothDiscreteTopRep.{u, v, max v w} R U} (f : A ⟶ B)

/-- On carriers, the induced morphism of tensor-induced total resolutions applies the total
resolution map in each tensor factor. -/
private theorem resolutionMap_apply (x : ⨂[R] _ : G ⧸ U, A.obj.gradedResolutionModule) :
    ((smoothTensorInducedGradedResolutionFunctor U hU s).map f).hom.hom x =
      PiTensorProduct.map (fun _ ↦
        TopRep.gradedResolutionMap (ContinuousMonoidHom.id U) f.hom) x := by
  have hg : (smoothGradedResolutionFunctor.map f).hom.hom.toLinearMap =
      TopRep.gradedResolutionMap (ContinuousMonoidHom.id U) f.hom := by
    rw [smoothGradedResolutionFunctor_map]
    exact LinearMap.ext (TopRep.gradedResolutionTopRepMap_apply f.hom)
  exact (smoothTensorInductionFunctor_map_hom_hom_apply R G U hU s
    (smoothGradedResolutionFunctor.map f) x).trans
      (congrArg (fun g ↦ PiTensorProduct.map (fun _ : G ⧸ U ↦ g) x) hg)

variable [Fintype (G ⧸ U)]

/-- The coefficient map on tensor-induced total resolutions preserves total degree. -/
theorem isHomogeneous_smoothTensorInducedGradedResolutionFunctor_map :
    TauCeti.LinearMap.IsHomogeneous
      ((smoothTensorInducedGradedResolutionFunctor U hU s).map f).hom.hom.toLinearMap
      (smoothTensorInducedGradedResolutionPiece U hU s A)
      (smoothTensorInducedGradedResolutionPiece U hU s B) 0 := by
  have h := PiTensorProduct.isHomogeneous_map (ι := G ⧸ U) (a := fun _ ↦ 0)
    (g := fun _ ↦ TopRep.gradedResolutionMap (ContinuousMonoidHom.id U) f.hom)
    (fun _ ↦ TopRep.isHomogeneous_gradedResolutionMap (ContinuousMonoidHom.id U) f.hom)
  rw [Finset.sum_const_zero] at h
  exact TauCeti.LinearMap.isHomogeneous_def.2 fun p x hx ↦
    (congrArg (· ∈ _) (resolutionMap_apply U hU s f x)).mpr (h.map_mem hx)

/-- The coefficient map on tensor-induced total resolutions commutes with the differentials. -/
@[reassoc]
theorem smoothTensorInducedGradedResolutionFunctor_map_differential :
    smoothTensorInducedGradedResolutionDifferential U hU s A ≫
        (smoothTensorInducedGradedResolutionFunctor U hU s).map f =
      (smoothTensorInducedGradedResolutionFunctor U hU s).map f ≫
        smoothTensorInducedGradedResolutionDifferential U hU s B := by
  classical
  have hd : B.obj.gradedResolutionDifferential ∘ₗ
      TopRep.gradedResolutionMap (ContinuousMonoidHom.id U) f.hom =
      TopRep.gradedResolutionMap (ContinuousMonoidHom.id U) f.hom ∘ₗ
        A.obj.gradedResolutionDifferential :=
    LinearMap.ext fun y ↦
      (TopRep.gradedResolutionMap_differential (ContinuousMonoidHom.id U) f.hom y).symm
  apply ObjectProperty.hom_ext
  refine TopRep.hom_ext (ContIntertwiningMap.ext (ContinuousLinearMap.ext fun x ↦ ?_))
  -- Evaluate the categorical composites before using the tensor-factor computation rules.
  change ((smoothTensorInducedGradedResolutionFunctor U hU s).map f).hom.hom
      ((smoothTensorInducedGradedResolutionDifferential U hU s A).hom.hom x) =
    (smoothTensorInducedGradedResolutionDifferential U hU s B).hom.hom
      (((smoothTensorInducedGradedResolutionFunctor U hU s).map f).hom.hom x)
  -- The sealed tensor-induction carriers prevent rewriting the map evaluation in place.
  refine (resolutionMap_apply U hU s f _).trans ?_
  refine (congrArg (PiTensorProduct.map fun _ : G ⧸ U ↦
    TopRep.gradedResolutionMap (ContinuousMonoidHom.id U) f.hom)
    (smoothTensorInducedGradedResolutionDifferential_apply U hU s A x)).trans ?_
  refine (LinearMap.congr_fun (PiTensorProduct.slotSum_comp_map _ fun _ ↦ hd) x).symm.trans ?_
  refine (congrArg (PiTensorProduct.slotSum (G ⧸ U)
    (fun _ ↦ B.obj.gradedResolutionDifferential))
    (resolutionMap_apply U hU s f x).symm).trans ?_
  exact (smoothTensorInducedGradedResolutionDifferential_apply U hU s B _).symm

omit [Fintype (G ⧸ U)] in
/-- The coefficient map carries the diagonal tensor to the diagonal tensor of the mapped
cocycle. -/
private theorem resolutionMap_tprod_const (z : A.obj.gradedResolutionModule) :
    ((smoothTensorInducedGradedResolutionFunctor U hU s).map f).hom.hom
        (PiTensorProduct.tprod R fun _ : G ⧸ U ↦ z) =
      PiTensorProduct.tprod R fun _ : G ⧸ U ↦
        TopRep.gradedResolutionMap (ContinuousMonoidHom.id U) f.hom z :=
  (resolutionMap_apply U hU s f _).trans (PiTensorProduct.map_tprod _ _)

/-- The coefficient map carries the tensor-induced augmentation to the augmentation of the
mapped coefficients. -/
private theorem resolutionMap_augmentation [LinearOrder (G ⧸ U)]
    (hA : ∀ a : A.obj.V, a + a = 0) (hB : ∀ b : B.obj.V, b + b = 0)
    (x : ((toSmoothDiscrete R G).obj
      (DiscreteRep.tensorInduced U hU s ((ofSmoothDiscrete R U).obj A))).obj.V) :
    ((smoothTensorInducedGradedResolutionFunctor U hU s).map f).hom.hom
        (((smoothTensorInducedGradedResolutionContraction U hU s A hA).ι.hom x).1) =
      (((smoothTensorInducedGradedResolutionContraction U hU s B hB).ι.hom
        (((smoothTensorInductionFunctor R G U hU s).map f).hom.hom x)).1) := by
  have h := (smoothTensorInducedGradedResolutionAugmentation U hU s).naturality f
  rw [smoothTensorInducedGradedResolutionAugmentation_app,
    smoothTensorInducedGradedResolutionAugmentation_app] at h
  have hx := ConcreteCategory.congr_hom (congrArg (fun g ↦ g.hom) h) x
  -- Both augmentations into degree zero are the tensor-induced coefficient augmentations.
  -- The dictionary preserves carriers; expose composition evaluations, which are hidden
  -- behind the full-subcategory and TopRep morphism projections in the naturality square.
  change (smoothTensorInducedGradedResolutionAugmentationApp U hU s B).hom.hom
      (((smoothTensorInductionFunctor R G U hU s).map f).hom.hom x) =
    ((smoothTensorInducedGradedResolutionFunctor U hU s).map f).hom.hom
      ((smoothTensorInducedGradedResolutionAugmentationApp U hU s A).hom.hom x) at hx
  refine (congrArg ((smoothTensorInducedGradedResolutionFunctor U hU s).map f).hom.hom
    ((smoothTensorInducedGradedResolutionContraction_ι_apply U hU s A hA x).trans
      (smoothTensorInducedGradedResolutionAugmentationApp_hom_apply U hU s A x).symm)).trans ?_
  exact hx.symm.trans
    ((smoothTensorInducedGradedResolutionAugmentationApp_hom_apply U hU s B _).trans
      (smoothTensorInducedGradedResolutionContraction_ι_apply U hU s B hB _).symm)

/-- **Coefficient naturality of the norm of a cocycle.** Mapping the norm along the tensor
induction of `f` gives the norm of the image under `f` on the total resolution. This holds in
every degree, including zero, without imposing characteristic two on the scalar ring. -/
theorem coeffMap_smoothTensorInducedDiagonalClass
    (hA : ∀ a : A.obj.V, a + a = 0) (hB : ∀ b : B.obj.V, b + b = 0) {n : ℕ}
    {z : A.obj.gradedResolutionModule} (hz : z ∈ A.obj.gradedResolutionPiece n)
    (hinv : ∀ a, A.obj.gradedResolutionTopRep.ρ a z = z)
    (hdz : A.obj.gradedResolutionDifferential z = 0) :
    ContinuousCohomology.coeffMap.{u, v, max u w}
        ((smoothTensorInductionFunctor R G U hU s).map f).hom
        (Fintype.card (G ⧸ U) * n)
        (smoothTensorInducedDiagonalClass.{u, v, w} U hU s A hA z hz hinv hdz) =
      smoothTensorInducedDiagonalClass.{u, v, w} U hU s B hB
        (TopRep.gradedResolutionMap (ContinuousMonoidHom.id U) f.hom z)
        (by
          have h := (TopRep.isHomogeneous_gradedResolutionMap
            (ContinuousMonoidHom.id U) f.hom).map_mem hz
          simpa only [add_zero] using h)
        (fun a ↦ (TopRep.gradedResolutionMap_equivariant
          (ContinuousMonoidHom.id U) f.hom a z).symm.trans
            (congrArg (TopRep.gradedResolutionMap (ContinuousMonoidHom.id U) f.hom) (hinv a)))
        (by
          exact (TopRep.gradedResolutionMap_differential
            (ContinuousMonoidHom.id U) f.hom z).symm.trans
              ((congrArg (TopRep.gradedResolutionMap (ContinuousMonoidHom.id U) f.hom)
                hdz).trans (map_zero _))) := by
  let : LinearOrder (G ⧸ U) := LinearOrder.lift' _ (Fintype.equivFin (G ⧸ U)).injective
  have : LocallyCompactSpace G :=
    (isCompact_iff_compactSpace.2 ‹CompactSpace U›).locallyCompactSpace_of_mem_nhds_of_group
      (hU.mem_nhds U.one_mem)
  -- The tensor-induced coefficient objects are sealed dictionary presentations; `erw`
  -- aligns these carriers and the identity restriction in the coefficient map.
  erw [ContinuousCohomology.coeffMap_def, smoothTensorInducedDiagonalClass_eq,
    smoothTensorInducedDiagonalClass_eq]
  refine (TopRep.ResolutionContraction.map_gradedCohomologyClass (ContinuousMonoidHom.id G)
    (smoothTensorInducedGradedResolutionContraction U hU s A hA)
    (smoothTensorInducedGradedResolutionContraction U hU s B hB)
    ((smoothTensorInductionFunctor R G U hU s).map f).hom
    ((smoothTensorInducedGradedResolutionFunctor U hU s).map f).hom
    (isHomogeneous_smoothTensorInducedGradedResolutionFunctor_map U hU s f)
    (congrArg (fun g ↦ g.hom)
      (smoothTensorInducedGradedResolutionFunctor_map_differential U hU s f))
    (resolutionMap_augmentation U hU s f hA hB) _ _ _).trans ?_
  congr 1
  exact resolutionMap_tprod_const U hU s f z

end Subgroup
