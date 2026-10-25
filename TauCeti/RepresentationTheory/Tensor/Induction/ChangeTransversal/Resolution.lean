/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Tensor.Induction.ChangeTransversal.Discrete
public import TauCeti.RepresentationTheory.Tensor.Induction.Resolution

/-!
# Changing the transversal in the tensor-induced resolution

The comparison between two tensor inductions preserves the total grading and commutes with the
slot-sum differential. It therefore compares the contracted tensor-induced resolutions over the
corresponding coefficient comparison. An invariant diagonal tensor is fixed by this comparison,
so its continuous cohomology class is independent of the transversal after transporting the
coefficients.

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
  (U : Subgroup G) (hU : IsOpen (U : Set G)) (s t : U.LeftTransversal) [U.FiniteIndex]
  [CompactSpace U] (A : SmoothDiscreteTopRep.{u, v, max v w} R U)

private noncomputable def resolutionChangeTotal :
    ((smoothTensorInducedGradedResolutionFunctor U hU t).obj A).obj ⟶
      ((smoothTensorInducedGradedResolutionFunctor U hU s).obj A).obj :=
  (smoothTensorInducedChangeTransversalIso.{u, v, max v w} U hU s t
    (smoothGradedResolutionFunctor.{u, v, w}.obj A)).hom.hom

private theorem resolutionChange_apply
    (x : ((smoothTensorInducedGradedResolutionFunctor U hU t).obj A).obj.V) :
    (resolutionChangeTotal U hU s t A).hom x =
      A.obj.gradedResolutionRepresentation.wreathTensor (G ⧸ U)
        (Subgroup.monomialChangeTransversal U s t) x := by
  have h : (resolutionChangeTotal U hU s t A).hom.toLinearMap =
      A.obj.gradedResolutionRepresentation.wreathTensor (G ⧸ U)
        (Subgroup.monomialChangeTransversal U s t) := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro m
    -- Evaluate the multilinear-map composite produced by tensor extensionality.
    change (resolutionChangeTotal U hU s t A).hom
      (PiTensorProduct.tprod R m) = _
    erw [resolutionChangeTotal, smoothTensorInducedChangeTransversalIso_hom_apply_tprod,
      Representation.wreathTensor_apply_tprod]
    congr 1
    funext i
    have hi : (Subgroup.monomialChangeTransversal U s t).right.symm i = i := by
      rw [Subgroup.monomialChangeTransversal_right]
      rfl
    erw [hi]
    exact (smoothGradedResolutionFunctor_obj_obj_ρ_apply A _ _).trans
      (A.obj.gradedResolutionTopRep_ρ_apply _ _)
  exact LinearMap.congr_fun h x

variable [Fintype (G ⧸ U)]

private theorem resolutionChange_mem (n : ℤ)
    (x : ((smoothTensorInducedGradedResolutionFunctor U hU t).obj A).obj.V)
    (hx : x ∈ smoothTensorInducedGradedResolutionPiece U hU t A n) :
    (resolutionChangeTotal U hU s t A).hom x ∈
      smoothTensorInducedGradedResolutionPiece U hU s A n := by
  have h := (A.obj.gradedResolutionRepresentation.isHomogeneous_wreathTensor
    A.obj.isHomogeneous_gradedResolutionRepresentation
    (Subgroup.monomialChangeTransversal U s t)).map_mem hx
  rw [add_zero] at h
  exact (congrArg (· ∈ smoothTensorInducedGradedResolutionPiece U hU s A n)
    (resolutionChange_apply U hU s t A x)).mpr h

private theorem resolutionChange_d
    (x : ((smoothTensorInducedGradedResolutionFunctor U hU t).obj A).obj.V) :
    (smoothTensorInducedGradedResolutionDifferential U hU s A).hom.hom
        ((resolutionChangeTotal U hU s t A).hom x) =
      (resolutionChangeTotal U hU s t A).hom
        ((smoothTensorInducedGradedResolutionDifferential U hU t A).hom.hom x) := by
  classical
  erw [smoothTensorInducedGradedResolutionDifferential_apply,
    resolutionChange_apply, resolutionChange_apply,
    smoothTensorInducedGradedResolutionDifferential_apply]
  exact LinearMap.congr_fun
    (A.obj.gradedResolutionRepresentation.slotSum_comp_wreathTensor
      (fun g ↦ LinearMap.ext (A.obj.gradedResolutionDifferential_equivariant g))
      (Subgroup.monomialChangeTransversal U s t)) x

private noncomputable abbrev tensorResolutionComplex (hA : ∀ a : A.obj.V, a + a = 0) :=
  ((smoothTensorInducedGradedResolutionFunctor U hU s).obj A).obj.gradedCochainComplex
    (smoothTensorInducedGradedResolutionPiece U hU s A)
    (smoothTensorInducedGradedResolutionPiece_ρ_mem U hU s A)
    (smoothTensorInducedGradedResolutionDifferential U hU s A).hom
    (isHomogeneous_smoothTensorInducedGradedResolutionDifferential U hU s A)
    (smoothTensorInducedGradedResolutionDifferential_sq U hU s A hA)

private noncomputable def resolutionChangeTerm (hA : ∀ a : A.obj.V, a + a = 0) (n : ℕ) :
    (tensorResolutionComplex U hU t A hA).X n ⟶
      (tensorResolutionComplex U hU s A hA).X n :=
  ((smoothTensorInducedGradedResolutionFunctor U hU s).obj A).obj.gradedCochainComplexLift
    _ _ _ _ _ n
    (((smoothTensorInducedGradedResolutionFunctor U hU t).obj A).obj.gradedCochainComplexι
      _ _ _ _ _ n ≫
        resolutionChangeTotal U hU s t A)
    (fun x ↦ by
      -- Evaluate composition before using the characteristic inclusion equation.
      change (resolutionChangeTotal U hU s t A).hom
        ((((smoothTensorInducedGradedResolutionFunctor U hU t).obj A).obj.gradedCochainComplexι
          _ _ _ _ _ n).hom x) ∈ _
      rw [TopRep.gradedCochainComplexι_apply]
      exact resolutionChange_mem U hU s t A n x.1 x.2)

private theorem resolutionChangeTerm_apply (hA : ∀ a : A.obj.V, a + a = 0) (n : ℕ)
    (x : ((tensorResolutionComplex U hU t A hA).X n).V) :
    ((resolutionChangeTerm U hU s t A hA n).hom x).1 =
      (resolutionChangeTotal U hU s t A).hom x.1 := by
  rw [resolutionChangeTerm, TopRep.gradedCochainComplexLift_apply]
  -- The source term is a subrepresentation, and composition evaluates in its ambient carrier.
  change (resolutionChangeTotal U hU s t A).hom
    ((((smoothTensorInducedGradedResolutionFunctor U hU t).obj A).obj.gradedCochainComplexι
      _ _ _ _ _ n).hom x) = _
  rw [TopRep.gradedCochainComplexι_apply]

private noncomputable def resolutionChange (hA : ∀ a : A.obj.V, a + a = 0) :
    tensorResolutionComplex U hU t A hA ⟶ tensorResolutionComplex U hU s A hA :=
  CochainComplex.ofHom (resolutionChangeTerm U hU s t A hA) fun n ↦ by
    apply TopRep.hom_ext
    apply ContIntertwiningMap.ext
    apply ContinuousLinearMap.ext
    intro x
    apply Subtype.ext
    simp only [TopRep.hom_comp, ContIntertwiningMap.toContinuousLinearMap_comp,
      ContinuousLinearMap.comp_apply, ContIntertwiningMap.toContinuousLinearMap_apply,
      resolutionChangeTerm_apply,
      TopRep.gradedCochainComplex_d_apply]
    exact resolutionChange_d U hU s t A x.1

private theorem resolutionChange_f_apply (hA : ∀ a : A.obj.V, a + a = 0) (n : ℕ)
    (x : ((tensorResolutionComplex U hU t A hA).X n).V) :
    (((resolutionChange U hU s t A hA).f n).hom x).1 =
      (resolutionChangeTotal U hU s t A).hom x.1 :=
  resolutionChangeTerm_apply U hU s t A hA n x

private theorem resolutionChange_augmentation [LinearOrder (G ⧸ U)]
    (hA : ∀ a : A.obj.V, a + a = 0) :
    (smoothTensorInducedGradedResolutionContraction U hU t A hA).ι ≫
        (resolutionChange U hU s t A hA).f 0 =
      (smoothTensorInducedChangeTransversalIso.{u, v, max v w} U hU s t A).hom.hom ≫
        (smoothTensorInducedGradedResolutionContraction U hU s A hA).ι := by
  apply TopRep.hom_ext
  apply ContIntertwiningMap.ext
  apply ContinuousLinearMap.ext
  intro x
  apply Subtype.ext
  have he : (resolutionChangeTotal U hU s t A).hom.toLinearMap ∘ₗ
      PiTensorProduct.map (fun _ : G ⧸ U ↦ A.obj.gradedResolutionAugmentation) =
      PiTensorProduct.map (fun _ : G ⧸ U ↦ A.obj.gradedResolutionAugmentation) ∘ₗ
        (smoothTensorInducedChangeTransversalIso.{u, v, max v w}
          U hU s t A).hom.hom.hom.toLinearMap := by
    have haug : (smoothGradedResolutionAugmentationApp A).hom.hom.toLinearMap =
        A.obj.gradedResolutionAugmentation :=
      LinearMap.ext (smoothGradedResolutionAugmentationApp_hom_apply A)
    have hmap (a : U.LeftTransversal) :
        ((smoothTensorInductionFunctor R G U hU a).map
          (smoothGradedResolutionAugmentationApp A)).hom.hom.toLinearMap =
        PiTensorProduct.map (fun _ : G ⧸ U ↦ A.obj.gradedResolutionAugmentation) := by
      change (((ofSmoothDiscrete R U).map
        (smoothGradedResolutionAugmentationApp A)).tensorInduced a).toLinearMap = _
      rw [Representation.IntertwiningMap.tensorInduced_toLinearMap,
        ofSmoothDiscrete_map_toLinearMap, haug]
      rfl
    have h := congrArg (fun f ↦ f.hom.hom.toLinearMap)
      (smoothTensorInducedChangeTransversalIso_hom_naturality U hU s t
        (smoothGradedResolutionAugmentationApp A))
    erw [ObjectProperty.FullSubcategory.comp_hom,
      ObjectProperty.FullSubcategory.comp_hom] at h
    change (smoothTensorInducedChangeTransversalIso U hU s t
        (smoothGradedResolutionFunctor.obj A)).hom.hom.hom.toLinearMap ∘ₗ
        ((smoothTensorInductionFunctor R G U hU t).map
          (smoothGradedResolutionAugmentationApp A)).hom.hom.toLinearMap =
      ((smoothTensorInductionFunctor R G U hU s).map
        (smoothGradedResolutionAugmentationApp A)).hom.hom.toLinearMap ∘ₗ
        (smoothTensorInducedChangeTransversalIso U hU s t A).hom.hom.hom.toLinearMap at h
    rw [hmap, hmap] at h
    exact h
  have hx := LinearMap.congr_fun he x
  -- Evaluate linear-map composition before comparing with the restricted augmentation.
  change (resolutionChangeTotal U hU s t A).hom
      (PiTensorProduct.map (fun _ : G ⧸ U ↦ A.obj.gradedResolutionAugmentation) x) =
    PiTensorProduct.map (fun _ : G ⧸ U ↦ A.obj.gradedResolutionAugmentation)
      ((smoothTensorInducedChangeTransversalIso.{u, v, max v w}
        U hU s t A).hom.hom.hom x) at hx
  simpa only [TopRep.hom_comp, ContIntertwiningMap.toContinuousLinearMap_comp,
    ContinuousLinearMap.comp_apply, ContIntertwiningMap.toContinuousLinearMap_apply,
    resolutionChange_f_apply, smoothTensorInducedGradedResolutionContraction_ι_apply] using hx

/-- Changing the transversal transports the class of an invariant diagonal cocycle along the
canonical comparison of tensor-induced coefficients. The comparison has source `t` and target
`s`, as does `smoothTensorInducedChangeTransversalIso U hU s t A`. -/
theorem coeffMap_smoothTensorInducedDiagonalClass_changeTransversal
    (hA : ∀ a : A.obj.V, a + a = 0) {n : ℕ} (z : A.obj.gradedResolutionModule)
    (hz : z ∈ A.obj.gradedResolutionPiece n)
    (hinv : ∀ u, A.obj.gradedResolutionTopRep.ρ u z = z)
    (hdz : A.obj.gradedResolutionDifferential z = 0) :
    ContinuousCohomology.coeffMap.{u, v, max u w}
        (smoothTensorInducedChangeTransversalIso.{u, v, max v w} U hU s t A).hom.hom
        (Fintype.card (G ⧸ U) * n)
        (smoothTensorInducedDiagonalClass.{u, v, w} U hU t A hA z hz hinv hdz) =
      smoothTensorInducedDiagonalClass.{u, v, w} U hU s A hA z hz hinv hdz := by
  let : LinearOrder (G ⧸ U) := LinearOrder.lift' _ (Fintype.equivFin (G ⧸ U)).injective
  have : LocallyCompactSpace G :=
    (isCompact_iff_compactSpace.2 ‹CompactSpace U›).locallyCompactSpace_of_mem_nhds_of_group
      (hU.mem_nhds U.one_mem)
  -- Dictionary carriers are opaque, so the class equations must also align their projections.
  erw [smoothTensorInducedDiagonalClass_eq, smoothTensorInducedDiagonalClass_eq,
    TopRep.ResolutionContraction.gradedCohomologyClass_def,
    TopRep.ResolutionContraction.gradedCohomologyClass_def,
    TopRep.ResolutionContraction.coeffMap_cohomologyClass _ _ _
      (resolutionChange U hU s t A hA) (resolutionChange_augmentation U hU s t A hA)]
  congr 1
  apply Subtype.ext
  apply Subtype.ext
  rw [ContIntertwiningMap.mapInvariants_apply]
  erw [resolutionChange_f_apply, TopRep.gradedCochainComplexInvariant_val,
    TopRep.gradedCochainComplexInvariant_val]
  erw [resolutionChangeTotal, smoothTensorInducedChangeTransversalIso_hom_apply_tprod]
  congr 1
  funext i
  exact (smoothGradedResolutionFunctor_obj_obj_ρ_apply A _ z).trans (hinv _)

/-- After identifying tensor-induced trivial `𝔽₂` coefficients with the ambient trivial
coefficient object, the class of an invariant diagonal cocycle does not depend on the transversal.
-/
theorem smoothTensorInducedDiagonalClass_trivialF2_changeTransversal
    (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U : Subgroup G) (hU : IsOpen (U : Set G)) (s t : U.LeftTransversal)
    [U.FiniteIndex] [CompactSpace U] [Fintype (G ⧸ U)] {n : ℕ}
    (z : (trivialF2 U).gradedResolutionModule)
    (hz : z ∈ (trivialF2 U).gradedResolutionPiece n)
    (hinv : ∀ u, (trivialF2 U).gradedResolutionTopRep.ρ u z = z)
    (hdz : (trivialF2 U).gradedResolutionDifferential z = 0) :
    ContinuousCohomology.coeffMap (smoothTensorInducedTrivialF2Iso G U hU t).hom.hom
        (Fintype.card (G ⧸ U) * n)
        (smoothTensorInducedDiagonalClass.{0, v, 0} U hU t
          ⟨trivialF2 U, isSmoothDiscrete_trivialF2 U⟩
          (fun a ↦ by simpa only [two_nsmul] using trivialF2_two_nsmul_eq_zero U a)
          z hz hinv hdz) =
      ContinuousCohomology.coeffMap (smoothTensorInducedTrivialF2Iso G U hU s).hom.hom
        (Fintype.card (G ⧸ U) * n)
        (smoothTensorInducedDiagonalClass.{0, v, 0} U hU s
          ⟨trivialF2 U, isSmoothDiscrete_trivialF2 U⟩
          (fun a ↦ by simpa only [two_nsmul] using trivialF2_two_nsmul_eq_zero U a)
          z hz hinv hdz) := by
  let A : SmoothDiscreteTopRep.{0, v, v} ℤ U :=
    ⟨trivialF2 U, isSmoothDiscrete_trivialF2 U⟩
  have hA (a : A.obj.V) : a + a = 0 := by
    simpa only [two_nsmul] using trivialF2_two_nsmul_eq_zero U a
  have h := coeffMap_smoothTensorInducedDiagonalClass_changeTransversal.{0, v, 0}
    U hU s t A hA z hz hinv hdz
  have hcoef := congrArg (fun f ↦ f.hom)
    (smoothTensorInducedTrivialF2Iso_changeTransversal_hom G U hU s t)
  erw [ObjectProperty.FullSubcategory.comp_hom] at hcoef
  have hclass := congrArg
    (fun c ↦ ContinuousCohomology.coeffMap
      (smoothTensorInducedTrivialF2Iso G U hU s).hom.hom
      (Fintype.card (G ⧸ U) * n) c) h
  erw [← ConcreteCategory.comp_apply, ← ContinuousCohomology.coeffMap_comp, hcoef] at hclass
  exact hclass

end TauCeti
