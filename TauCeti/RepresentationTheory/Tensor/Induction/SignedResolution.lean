/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.PiTensorProduct.SignedDifferential
public import TauCeti.RepresentationTheory.Tensor.Induction.Resolution

/-!
# The signed differential of a tensor-induced resolution

On the underlying tensor module of the tensor-induced coinduced resolution, an ordering
of the cosets specifies the Koszul signs for the differential. With these signs the
differential squares to zero over any commutative ring, and a diagonal tensor of a
cocycle is again a cocycle. In characteristic two it is the underlying linear map of
the usual tensor-induced differential.

`TopRep.gradedResolutionInternalGrading` packages the existing homogeneous pieces for
`PiTensorProduct.signedDifferential`, which supplies the pure-tensor formula for
`Subgroup.smoothTensorInducedGradedResolutionSignedDifferential`. Its coefficient naturality
uses `PiTensorProduct.signedDifferential_comp_map` and the comparison with the slot sum
uses `PiTensorProduct.signedDifferential_eq_slotSum`.

This is the underlying differential for the tensor resolution in Evens' construction
(*A generalization of the transfer map in the cohomology of groups*, Trans. Amer. Math. Soc.
**108** (1963), §§2–5).
-/

public section

open CategoryTheory
open scoped TensorProduct

open TauCeti

universe u v w

namespace Subgroup

variable {R : Type u} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (U : Subgroup G) (hU : IsOpen (U : Set G)) (s : U.LeftTransversal) [U.FiniteIndex]
  [CompactSpace U] (A : SmoothDiscreteTopRep.{u, v, max v w} R U)
  [Fintype (G ⧸ U)] [LinearOrder (G ⧸ U)]

/-- The signed tensor differential on the underlying module of the tensor-induced total
resolution, using the chosen ordering of the cosets. -/
noncomputable def smoothTensorInducedGradedResolutionSignedDifferential :
    Module.End R ((smoothTensorInducedGradedResolutionFunctor U hU s).obj A).obj.V :=
  PiTensorProduct.signedDifferential
    (fun _ : G ⧸ U ↦ A.obj.gradedResolutionInternalGrading)
    (fun _ ↦ A.obj.gradedResolutionDifferential)

/-- The underlying resolution differential is the signed tensor differential of the total
coinduced resolution in each coset slot. -/
theorem smoothTensorInducedGradedResolutionSignedDifferential_def :
    smoothTensorInducedGradedResolutionSignedDifferential U hU s A =
      PiTensorProduct.signedDifferential
        (fun _ : G ⧸ U ↦ A.obj.gradedResolutionInternalGrading)
        (fun _ ↦ A.obj.gradedResolutionDifferential) :=
  (rfl)

/-- On a pure tensor, the resolution differential sums over cosets, applying the Koszul twist
in the slots preceding the differentiated slot. -/
@[simp]
theorem smoothTensorInducedGradedResolutionSignedDifferential_tprod
    (x : G ⧸ U → A.obj.gradedResolutionModule) :
    smoothTensorInducedGradedResolutionSignedDifferential U hU s A
      (PiTensorProduct.tprod R x) = ∑ i, PiTensorProduct.tprod R
        (Function.update (fun j ↦ if j < i then
          A.obj.gradedResolutionInternalGrading.koszulTwist 1 (x j) else x j) i
          (A.obj.gradedResolutionDifferential (x i))) :=
  PiTensorProduct.signedDifferential_tprod _ _ x

/-- The signed differential raises the total degree by one. -/
theorem isHomogeneous_smoothTensorInducedGradedResolutionSignedDifferential :
    LinearMap.IsHomogeneous
      (smoothTensorInducedGradedResolutionSignedDifferential U hU s A)
      (smoothTensorInducedGradedResolutionPiece U hU s A)
      (smoothTensorInducedGradedResolutionPiece U hU s A) 1 := by
  have hpiece := funext A.obj.gradedResolutionInternalGrading_piece
  rw [smoothTensorInducedGradedResolutionSignedDifferential_def]
  have hd := PiTensorProduct.isHomogeneous_signedDifferential
    (fun _ : G ⧸ U ↦ A.obj.gradedResolutionInternalGrading)
    (fun _ ↦ A.obj.gradedResolutionDifferential)
    (fun _ ↦ by
      rw [hpiece]
      exact A.obj.isHomogeneous_gradedResolutionDifferential)
  rw [hpiece] at hd
  exact hd

/-- The map induced by a coefficient morphism intertwines the signed tensor differentials. -/
theorem smoothTensorInducedGradedResolutionSignedDifferential_comp_map
    {A B : SmoothDiscreteTopRep.{u, v, max v w} R U} (f : A ⟶ B) :
    smoothTensorInducedGradedResolutionSignedDifferential U hU s B ∘ₗ
        ((smoothTensorInducedGradedResolutionFunctor U hU s).map f).hom.hom.toLinearMap =
      ((smoothTensorInducedGradedResolutionFunctor U hU s).map f).hom.hom.toLinearMap ∘ₗ
        smoothTensorInducedGradedResolutionSignedDifferential U hU s A := by
  have hmap :
      ((smoothTensorInducedGradedResolutionFunctor U hU s).map f).hom.hom.toLinearMap =
        PiTensorProduct.map (fun _ : G ⧸ U ↦
          TopRep.gradedResolutionMap (ContinuousMonoidHom.id U) f.hom) :=
    LinearMap.ext (smoothTensorInducedGradedResolutionFunctor_map_hom_hom_apply U hU s f)
  rw [hmap, smoothTensorInducedGradedResolutionSignedDifferential_def,
    smoothTensorInducedGradedResolutionSignedDifferential_def]
  apply PiTensorProduct.signedDifferential_comp_map
  · intro i
    rw [funext A.obj.gradedResolutionInternalGrading_piece,
      funext B.obj.gradedResolutionInternalGrading_piece]
    exact TopRep.isHomogeneous_gradedResolutionMap (ContinuousMonoidHom.id U) f.hom
  · exact fun _ ↦ LinearMap.ext fun x ↦
      (TopRep.gradedResolutionMap_differential (ContinuousMonoidHom.id U) f.hom x).symm

/-- The signed differential squares to zero. -/
@[simp]
theorem smoothTensorInducedGradedResolutionSignedDifferential_sq
    (z : ((smoothTensorInducedGradedResolutionFunctor U hU s).obj A).obj.V) :
    smoothTensorInducedGradedResolutionSignedDifferential U hU s A
      (smoothTensorInducedGradedResolutionSignedDifferential U hU s A z) = 0 :=
  LinearMap.congr_fun (PiTensorProduct.signedDifferential_comp_self _ _
    (fun _ ↦ by
      rw [funext A.obj.gradedResolutionInternalGrading_piece]
      exact A.obj.isHomogeneous_gradedResolutionDifferential)
    (fun _ ↦ LinearMap.ext A.obj.gradedResolutionDifferential_sq)) z

/-- The diagonal tensor of a cocycle is killed by the signed differential. -/
theorem smoothTensorInducedGradedResolutionSignedDifferential_tprod_const_eq_zero
    {z : A.obj.gradedResolutionModule} (hz : A.obj.gradedResolutionDifferential z = 0) :
    smoothTensorInducedGradedResolutionSignedDifferential U hU s A
      (PiTensorProduct.tprod R (fun _ : G ⧸ U ↦ z)) = 0 :=
  PiTensorProduct.signedDifferential_tprod_eq_zero _ _ (fun _ ↦ hz)

/-- On coefficients killed by two, the signed differential agrees with the tensor-induced
differential defined using the ordinary slot sum. -/
theorem smoothTensorInducedGradedResolutionSignedDifferential_eq_differential
    (hA : ∀ a : A.obj.V, a + a = 0) :
    smoothTensorInducedGradedResolutionSignedDifferential U hU s A =
      (smoothTensorInducedGradedResolutionDifferential U hU s A).hom.hom.toLinearMap := by
  refine LinearMap.ext fun z ↦ Eq.trans ?_
    (smoothTensorInducedGradedResolutionDifferential_apply U hU s A z).symm
  exact LinearMap.congr_fun (PiTensorProduct.signedDifferential_eq_slotSum (ι := G ⧸ U) (R := R)
    (M := fun _ ↦ A.obj.gradedResolutionModule) _ _
    (fun _ ↦ A.obj.gradedResolutionModule_add_self_eq_zero hA)) z

end Subgroup
