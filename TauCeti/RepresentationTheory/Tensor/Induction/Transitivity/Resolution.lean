/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Tensor.Induction.Resolution
public import TauCeti.RepresentationTheory.Tensor.Induction.Transitivity.Discrete
public import TauCeti.RepresentationTheory.Tensor.Induction.Transitivity.Differential
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Resolution.Graded.Comparison
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Resolution.ChangeOfGroup

/-!
# Transitivity of the norm of a cocycle on tensor-induced resolutions

Let `V ≤ U ≤ G` be compact open subgroups of finite index in a topological group, and let `A` be a
smooth discrete `V`-representation in which every element is its own additive inverse. For a
`V`-invariant cocycle `z` of degree `n` of the total coinduced resolution of `A`, Evens' norm of
`z` from `V` to `G` is the class of the diagonal tensor `z ⊗ ⋯ ⊗ z` in the tensor-induced
resolution (`TauCeti.smoothTensorInducedDiagonalClass`). This file proves that the norm is
transitive at the level of cocycles: the norm from `V` to `G` is the norm from `U` to `G` of a
cocycle representing the norm from `V` to `U`.

To take the norm from `V` to `U`, the coefficients are restricted to `V.subgroupOf U ≃ V`
(`TauCeti.smoothResSubgroupOf`), together with the total resolution and the cocycle `z`
(`TauCeti.smoothGradedResolutionResSubgroupOf`). The norm from `V` to `U` lives on the
tensor-induced resolution, not on the total resolution of the intermediate coefficients
`Ind⊗_{V}^{U} A` (`TauCeti.smoothTensorInducedSubgroupOf`), which is where the norm from `U` to
`G` is computed. Both resolutions are contracted onto `Ind⊗_{V}^{U} A`, and the comparison
theorem gives a morphism of degree zero between them over the identity
(`TauCeti.smoothTensorInducedGradedResolutionComparison`), which preserves classes
(`TauCeti.gradedCohomologyClass_smoothTensorInducedGradedResolutionComparison`). So the norm from
`V` to `U` of `z` is represented on the total resolution by the image `y` of the diagonal tensor.

The main theorem `TauCeti.coeffMap_smoothTensorInducedDiagonalClass_transitivity` states that
transporting the norm from `V` to `G` of `z` along the transitivity isomorphism
`Ind⊗_{V}^{G} A ≅ Ind⊗_{U}^{G} Ind⊗_{V}^{U} A` (`TauCeti.smoothTensorInducedTransitivityIso`) gives
the norm from `U` to `G` of `y`, in the degree `[G : U] ([U : V] n) = [G : V] n`. Regrouping the
tensor factors, restricting each factor and applying the comparison in each factor is a morphism of
degree zero from the tensor-induced resolution for `V` to the one for `U`. It commutes with the
slot-sum differentials, lies over the inverse transitivity isomorphism of the coefficients, and
carries the diagonal tensor of `z` to the diagonal tensor of `y`, so it identifies the two classes.

The coefficient ring lives in `Type` and the coefficients in the universe of the group, which is
the setting of trivial `𝔽₂` coefficients over `ℤ`, on which the Evens norm is defined.

## Main definitions

* `TauCeti.smoothTensorInducedGradedResolutionComparison`: the comparison of the tensor-induced
  resolution with the total resolution of the tensor-induced coefficients.
* `TauCeti.smoothResSubgroupOf`, `TauCeti.smoothGradedResolutionResSubgroupOf`: restriction of
  coefficients and of their total resolution to `V.subgroupOf U`.
* `TauCeti.smoothTensorInducedSubgroupOf`: the intermediate tensor-induced coefficients.

## Main results

* `TauCeti.gradedCohomologyClass_smoothTensorInducedGradedResolutionComparison`: the comparison
  carries the diagonal tensor of a cocycle to a cocycle of the total resolution representing its
  norm.
* `TauCeti.coeffMap_smoothTensorInducedDiagonalClass_transitivity`: transitivity of the norm of a
  cocycle along `V ≤ U ≤ G`.

## References

* L. Evens, *A generalization of the transfer map in the cohomology of groups*,
  Trans. Amer. Math. Soc. **108** (1963), §6, Proposition 1.
-/

public section

open CategoryTheory
open scoped TensorProduct

universe v

namespace TauCeti

variable {R : Type} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]

/-! ### The comparison of the tensor-induced resolution with the total resolution -/

section Comparison

variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
  (W : Subgroup H) (hW : IsOpen (W : Set H)) (t : W.LeftTransversal) [W.FiniteIndex]
  [CompactSpace W] [Fintype (H ⧸ W)] [LinearOrder (H ⧸ W)]
  (B : SmoothDiscreteTopRep.{0, v, v} R W) (hB : ∀ b : B.obj.V, b + b = 0)

/-- **The comparison of the tensor-induced resolution with the total resolution** of the
tensor-induced coefficients: both are contracted onto `Ind⊗_W^H B`, and this is the morphism of
degree zero over the identity of `Ind⊗_W^H B` given by the comparison theorem
(`TopRep.ResolutionContraction.gradedComparison`), for the contraction of the tensor-induced
resolution through the order on `H ⧸ W`. -/
noncomputable def smoothTensorInducedGradedResolutionComparison :
    (smoothTensorInducedGradedResolutionFunctor W hW t).obj B ⟶
      smoothGradedResolutionFunctor.{0, v, v}.obj
        ((toSmoothDiscrete R H).obj
          (DiscreteRep.tensorInduced W hW t ((ofSmoothDiscrete R W).obj B))) :=
  ObjectProperty.homMk (smoothTensorInducedGradedResolutionContraction W hW t B hB).gradedComparison

/-- The comparison is the comparison of the contraction of the tensor-induced resolution with the
total resolution. -/
theorem smoothTensorInducedGradedResolutionComparison_hom :
    (smoothTensorInducedGradedResolutionComparison W hW t B hB).hom =
      (smoothTensorInducedGradedResolutionContraction W hW t B hB).gradedComparison :=
  (rfl)

/-- The comparison carries the total degree of the tensor-induced resolution to the degree of the
total resolution. -/
theorem isHomogeneous_smoothTensorInducedGradedResolutionComparison :
    LinearMap.IsHomogeneous
      (smoothTensorInducedGradedResolutionComparison W hW t B hB).hom.hom.toLinearMap
      (smoothTensorInducedGradedResolutionPiece W hW t B)
      (TopRep.gradedResolutionPiece.{0, v, v} ((toSmoothDiscrete R H).obj
          (DiscreteRep.tensorInduced W hW t ((ofSmoothDiscrete R W).obj B))).obj) 0 :=
  TopRep.ResolutionContraction.isHomogeneous_gradedComparison _

/-- The comparison commutes with the differentials: it carries the slot sum of the total
differential of `B` to the total differential of the tensor-induced coefficients. -/
theorem smoothTensorInducedGradedResolutionComparison_slotSum
    (y : ⨂[R] _ : H ⧸ W, B.obj.gradedResolutionModule) :
    (smoothTensorInducedGradedResolutionComparison W hW t B hB).hom.hom
        (PiTensorProduct.slotSum (H ⧸ W) (fun _ ↦ B.obj.gradedResolutionDifferential) y) =
      TopRep.gradedResolutionDifferential.{0, v, v}
          ((toSmoothDiscrete R H).obj
            (DiscreteRep.tensorInduced W hW t ((ofSmoothDiscrete R W).obj B))).obj
          ((smoothTensorInducedGradedResolutionComparison W hW t B hB).hom.hom y) := by
  -- The tensor-induced resolution has no pieces of negative total degree.
  have hneg : ∀ v ∈ smoothTensorInducedGradedResolutionPiece W hW t B (-1),
      (smoothTensorInducedGradedResolutionDifferential W hW t B).hom.hom v = 0 := by
    intro v hv
    have hbot : smoothTensorInducedGradedResolutionPiece W hW t B (-1) = ⊥ :=
      PiTensorProduct.totalDegreePiece_eq_bot_of_neg
        (fun _ _ hp ↦ B.obj.gradedResolutionPiece_of_neg hp) (by norm_num : (-1 : ℤ) < 0)
    rw [hbot, Submodule.mem_bot] at hv
    rw [hv, map_zero]
  have h := congrArg (fun f ↦ f.hom y)
    ((smoothTensorInducedGradedResolutionContraction W hW t B hB).gradedComparison_differential
      hneg)
  exact (congrArg _ (smoothTensorInducedGradedResolutionDifferential_apply W hW t B y).symm).trans
    (h.trans (TopRep.gradedResolutionTopRepDifferential_apply _ _))

/-- The comparison lies over the identity of the tensor-induced coefficients: it carries their
augmentation into the tensor-induced resolution to their augmentation into the total
resolution. -/
theorem smoothTensorInducedGradedResolutionComparison_augmentation
    (x : ((toSmoothDiscrete R H).obj
      (DiscreteRep.tensorInduced W hW t ((ofSmoothDiscrete R W).obj B))).obj.V) :
    (smoothTensorInducedGradedResolutionComparison W hW t B hB).hom.hom
        (PiTensorProduct.map (fun _ ↦ B.obj.gradedResolutionAugmentation) x) =
      TopRep.gradedResolutionAugmentation.{0, v, v}
        ((toSmoothDiscrete R H).obj
          (DiscreteRep.tensorInduced W hW t ((ofSmoothDiscrete R W).obj B))).obj x :=
  (congrArg _ (smoothTensorInducedGradedResolutionContraction_ι_apply W hW t B hB x).symm).trans
    (TopRep.ResolutionContraction.gradedComparison_ι_apply _ x)

/-- **The norm of a cocycle on the total resolution.** For a `W`-invariant cocycle `z` of degree
`n` of the total resolution of `B`, the image `y` under the comparison of the diagonal tensor
`z ⊗ ⋯ ⊗ z` is a cocycle of degree `[H : W] n` of the total resolution of `Ind⊗_W^H B` whose class
is the norm of `z`. -/
theorem gradedCohomologyClass_smoothTensorInducedGradedResolutionComparison {n : ℕ}
    {z : B.obj.gradedResolutionModule} (hz : z ∈ B.obj.gradedResolutionPiece n)
    (hinv : ∀ u, B.obj.gradedResolutionTopRep.ρ u z = z)
    (hdz : B.obj.gradedResolutionDifferential z = 0)
    {y : ((toSmoothDiscrete R H).obj
      (DiscreteRep.tensorInduced W hW t ((ofSmoothDiscrete R W).obj B))).obj.gradedResolutionModule}
    (hy : y ∈ ((toSmoothDiscrete R H).obj (DiscreteRep.tensorInduced W hW t
      ((ofSmoothDiscrete R W).obj B))).obj.gradedResolutionPiece (Fintype.card (H ⧸ W) * n : ℕ))
    (hyinv : ∀ h, ((toSmoothDiscrete R H).obj (DiscreteRep.tensorInduced W hW t
      ((ofSmoothDiscrete R W).obj B))).obj.gradedResolutionTopRep.ρ h y = y)
    (hdy : ((toSmoothDiscrete R H).obj (DiscreteRep.tensorInduced W hW t
      ((ofSmoothDiscrete R W).obj B))).obj.gradedResolutionTopRepDifferential.hom y = 0)
    (hyz : y = (smoothTensorInducedGradedResolutionComparison W hW t B hB).hom.hom
      (PiTensorProduct.tprod R fun _ : H ⧸ W ↦ z)) :
    (TopRep.gradedResolutionContraction ((toSmoothDiscrete R H).obj (DiscreteRep.tensorInduced W hW
      t ((ofSmoothDiscrete R W).obj B))).property).gradedCohomologyClass y hy hyinv hdy =
      smoothTensorInducedDiagonalClass W hW t B hB z hz hinv hdz := by
  subst hyz
  rw [smoothTensorInducedDiagonalClass_eq]
  exact TopRep.ResolutionContraction.gradedCohomologyClass_gradedComparison _ _ _ _ _

end Comparison

/-! ### Restriction to `V.subgroupOf U` and the intermediate coefficients -/

variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {U V : Subgroup G} (hVU : V ≤ U) (s : U.LeftTransversal)
  (t : (V.subgroupOf U).LeftTransversal) (hU : IsOpen (U : Set G)) (hV : IsOpen (V : Set G))

/-- The restriction of a smooth discrete `V`-representation to `V.subgroupOf U`, along the
canonical isomorphism `V.subgroupOf U ≃* V`: the coefficients that are tensor-induced from
`V.subgroupOf U` to `U` in the first step of the transitivity of tensor induction. -/
noncomputable abbrev smoothResSubgroupOf (A : SmoothDiscreteTopRep.{0, v, v} R V) :
    SmoothDiscreteTopRep.{0, v, v} R (V.subgroupOf U) :=
  (smoothResFunctor R (Subgroup.subgroupOfEquivOfLe hVU : V.subgroupOf U →* V)
    (Subgroup.continuous_subgroupOfEquivOfLe hVU)).obj A

section Restriction

variable [CompactSpace V] [CompactSpace (V.subgroupOf U)]

/-- The restriction to `V.subgroupOf U` of the total resolution of `A`, compared with the total
resolution of the restriction of `A`: it pulls back cochains along `V.subgroupOf U ≃* V`
(`TopRep.gradedResolutionTopRepResMap`). -/
noncomputable def smoothGradedResolutionResSubgroupOf (A : SmoothDiscreteTopRep.{0, v, v} R V) :
    smoothResSubgroupOf hVU (smoothGradedResolutionFunctor.obj A) ⟶
      smoothGradedResolutionFunctor.obj (smoothResSubgroupOf hVU A) :=
  ObjectProperty.homMk (TopRep.gradedResolutionTopRepResMap
    ⟨(Subgroup.subgroupOfEquivOfLe hVU : V.subgroupOf U →* V),
      Subgroup.continuous_subgroupOfEquivOfLe hVU⟩ (𝟙 _))

/-- The restriction of the total resolution pulls back cochains along `V.subgroupOf U ≃* V`. -/
theorem smoothGradedResolutionResSubgroupOf_hom_hom_apply (A : SmoothDiscreteTopRep.{0, v, v} R V)
    (x : A.obj.gradedResolutionModule) :
    (smoothGradedResolutionResSubgroupOf hVU A).hom.hom x =
      TopRep.gradedResolutionMap ⟨(Subgroup.subgroupOfEquivOfLe hVU : V.subgroupOf U →* V),
        Subgroup.continuous_subgroupOfEquivOfLe hVU⟩ (𝟙 _) x :=
  TopRep.gradedResolutionTopRepResMap_apply _ _ x

/-- The restriction of the total resolution preserves degrees. -/
theorem isHomogeneous_smoothGradedResolutionResSubgroupOf
    (A : SmoothDiscreteTopRep.{0, v, v} R V) :
    LinearMap.IsHomogeneous (smoothGradedResolutionResSubgroupOf hVU A).hom.hom.toLinearMap
      A.obj.gradedResolutionPiece (smoothResSubgroupOf hVU A).obj.gradedResolutionPiece 0 :=
  TopRep.isHomogeneous_gradedResolutionTopRepResMap _ _

/-- The restriction of the total resolution commutes with the total differentials. -/
theorem smoothGradedResolutionResSubgroupOf_differential (A : SmoothDiscreteTopRep.{0, v, v} R V)
    (x : A.obj.gradedResolutionModule) :
    (smoothGradedResolutionResSubgroupOf hVU A).hom.hom (A.obj.gradedResolutionDifferential x) =
      (smoothResSubgroupOf hVU A).obj.gradedResolutionDifferential
        ((smoothGradedResolutionResSubgroupOf hVU A).hom.hom x) :=
  (smoothGradedResolutionResSubgroupOf_hom_hom_apply hVU A _).trans
    ((TopRep.gradedResolutionMap_differential _ _ x).trans
      (congrArg _ (smoothGradedResolutionResSubgroupOf_hom_hom_apply hVU A x).symm))

/-- The restriction of the total resolution commutes with the augmentations. -/
theorem smoothGradedResolutionResSubgroupOf_augmentation (A : SmoothDiscreteTopRep.{0, v, v} R V)
    (x : A.obj.V) :
    (smoothGradedResolutionResSubgroupOf hVU A).hom.hom (A.obj.gradedResolutionAugmentation x) =
      (smoothResSubgroupOf hVU A).obj.gradedResolutionAugmentation x :=
  (smoothGradedResolutionResSubgroupOf_hom_hom_apply hVU A _).trans
    (TopRep.gradedResolutionMap_augmentation _ _ x)

end Restriction

variable [(V.subgroupOf U).FiniteIndex]

/-- The **intermediate tensor-induced coefficients** `Ind⊗_V^U A`, the tensor induction from
`V.subgroupOf U` to `U` of the restriction of `A`: the coefficients of the norm from `V` to `U`,
and the inner tensor induction of `TauCeti.smoothTensorInducedTransitivityIso`. -/
noncomputable abbrev smoothTensorInducedSubgroupOf (A : SmoothDiscreteTopRep.{0, v, v} R V) :
    SmoothDiscreteTopRep.{0, v, v} R U :=
  (toSmoothDiscrete R U).obj (DiscreteRep.tensorInduced (V.subgroupOf U)
    (U.subgroupOf_isOpen V hV) t ((ofSmoothDiscrete R _).obj (smoothResSubgroupOf hVU A)))

/-- If every element of `A` is its own additive inverse, so is every element of the intermediate
tensor-induced coefficients. -/
theorem smoothTensorInducedSubgroupOf_add_self (A : SmoothDiscreteTopRep.{0, v, v} R V)
    (hA : ∀ a : A.obj.V, a + a = 0) (a : (smoothTensorInducedSubgroupOf hVU t hV A).obj.V) :
    a + a = 0 :=
  PiTensorProduct.add_self_eq_zero a (QuotientGroup.mk 1) hA

/-! ### The comparison of the tensor-induced resolutions along `V ≤ U ≤ G` -/

variable [U.FiniteIndex] [CompactSpace U] [CompactSpace V] [CompactSpace (V.subgroupOf U)]
  [Fintype (U ⧸ V.subgroupOf U)] [LinearOrder (U ⧸ V.subgroupOf U)]

/-- The comparison of the tensor-induced resolution for `V` with the one for `U`, applied to the
intermediate coefficients: regroup the tensor factors along the inverse transitivity isomorphism,
restrict each factor to `V.subgroupOf U`, and apply the comparison
`TauCeti.smoothTensorInducedGradedResolutionComparison` in each factor over `G ⧸ U`. -/
private noncomputable def transitivityHom (A : SmoothDiscreteTopRep.{0, v, v} R V)
    (hA : ∀ a : A.obj.V, a + a = 0) :
    letI : V.FiniteIndex := Subgroup.finiteIndex_of_finiteIndex_subgroupOf V U
    (smoothTensorInducedGradedResolutionFunctor V hV
        (Subgroup.compositeLeftTransversal hVU s t)).obj A ⟶
      (smoothTensorInducedGradedResolutionFunctor U hU s).obj
        (smoothTensorInducedSubgroupOf hVU t hV A) :=
  letI : V.FiniteIndex := Subgroup.finiteIndex_of_finiteIndex_subgroupOf V U
  (smoothTensorInducedTransitivityIso hVU s t hU hV (smoothGradedResolutionFunctor.obj A)).inv ≫
    (smoothTensorInductionFunctor R G U hU s).map
      ((smoothTensorInductionFunctor R U (V.subgroupOf U) (U.subgroupOf_isOpen V hV) t).map
        (smoothGradedResolutionResSubgroupOf hVU A)) ≫
    (smoothTensorInductionFunctor R G U hU s).map
      (smoothTensorInducedGradedResolutionComparison (V.subgroupOf U) (U.subgroupOf_isOpen V hV) t
        (smoothResSubgroupOf hVU A) hA)

/-- The comparison regroups the tensor factors, restricts them and applies the comparison over
`G ⧸ U`. -/
private theorem transitivityHom_apply (A : SmoothDiscreteTopRep.{0, v, v} R V)
    (hA : ∀ a : A.obj.V, a + a = 0) (x : ⨂[R] _ : G ⧸ V, A.obj.gradedResolutionModule) :
    (transitivityHom hVU s t hU hV A hA).hom.hom x =
      PiTensorProduct.map (fun _ ↦ (smoothTensorInducedGradedResolutionComparison (V.subgroupOf U)
          (U.subgroupOf_isOpen V hV) t (smoothResSubgroupOf hVU A) hA).hom.hom.toLinearMap)
        (PiTensorProduct.map (fun _ ↦ PiTensorProduct.map
          (fun _ ↦ (smoothGradedResolutionResSubgroupOf hVU A).hom.hom.toLinearMap))
          ((Subgroup.tensorInducedTransitivityLinearEquiv hVU s).symm x)) := by
  let _ : V.FiniteIndex := Subgroup.finiteIndex_of_finiteIndex_subgroupOf V U
  have hinner : ((smoothTensorInductionFunctor R U (V.subgroupOf U) (U.subgroupOf_isOpen V hV)
      t).map (smoothGradedResolutionResSubgroupOf hVU A)).hom.hom.toLinearMap =
        PiTensorProduct.map (fun _ ↦
          (smoothGradedResolutionResSubgroupOf hVU A).hom.hom.toLinearMap) :=
    LinearMap.ext (smoothTensorInductionFunctor_map_hom_hom_apply R U _ _ t _)
  have h1 : (smoothTensorInducedTransitivityIso hVU s t hU hV
      (smoothGradedResolutionFunctor.obj A)).inv.hom.hom x =
        (Subgroup.tensorInducedTransitivityLinearEquiv hVU s).symm x := by
    let B := (ofSmoothDiscrete R V).obj (smoothGradedResolutionFunctor.obj A)
    let : Module R B.V := B.module
    have h : ((smoothTensorInducedTransitivityIso hVU s t hU hV
        (smoothGradedResolutionFunctor.obj A)).inv.hom.hom.toLinearMap :
          (⨂[R] _ : G ⧸ V, B.V) →ₗ[R] ⨂[R] _ : G ⧸ U, ⨂[R] _ : U ⧸ V.subgroupOf U, B.V) =
        (Subgroup.tensorInducedTransitivityLinearEquiv hVU s).symm.toLinearMap := by
      refine PiTensorProduct.ext (MultilinearMap.ext fun m ↦ ?_)
      exact (smoothTensorInducedTransitivityIso_inv_apply_tprod hVU s t hU hV _ m).trans
        (Subgroup.tensorInducedTransitivityLinearEquiv_symm_tprod hVU s m).symm
    exact LinearMap.congr_fun h x
  refine (smoothTensorInductionFunctor_map_hom_hom_apply R G U hU s _ _).trans ?_
  congr 1
  refine (smoothTensorInductionFunctor_map_hom_hom_apply R G U hU s _ _).trans ?_
  exact congrArg₂ (fun f y ↦ PiTensorProduct.map f y) (funext fun _ ↦ hinner) h1

/-- The comparison carries the diagonal tensor of `z` to the diagonal tensor of the image under
the comparison over `U` of the diagonal tensor of the restriction of `z`. -/
private theorem transitivityHom_tprod_const (A : SmoothDiscreteTopRep.{0, v, v} R V)
    (hA : ∀ a : A.obj.V, a + a = 0) (z : A.obj.gradedResolutionModule) :
    (transitivityHom hVU s t hU hV A hA).hom.hom
        (PiTensorProduct.tprod R fun _ : G ⧸ V ↦ z) =
      PiTensorProduct.tprod R fun _ : G ⧸ U ↦
        (smoothTensorInducedGradedResolutionComparison (V.subgroupOf U)
          (U.subgroupOf_isOpen V hV) t (smoothResSubgroupOf hVU A) hA).hom.hom
          (PiTensorProduct.tprod R fun _ : U ⧸ V.subgroupOf U ↦
            (smoothGradedResolutionResSubgroupOf hVU A).hom.hom z) := by
  refine (transitivityHom_apply hVU s t hU hV A hA _).trans ?_
  refine (congrArg (PiTensorProduct.map fun _ : G ⧸ U ↦
    (smoothTensorInducedGradedResolutionComparison (V.subgroupOf U)
      (U.subgroupOf_isOpen V hV) t (smoothResSubgroupOf hVU A) hA).hom.hom.toLinearMap)
    ((congrArg (PiTensorProduct.map fun _ : G ⧸ U ↦ PiTensorProduct.map
      fun _ : U ⧸ V.subgroupOf U ↦ (smoothGradedResolutionResSubgroupOf hVU A).hom.hom.toLinearMap)
      (Subgroup.tensorInducedTransitivityLinearEquiv_symm_tprod hVU s fun _ ↦ z)).trans
        (PiTensorProduct.map_tprod _ _))).trans ?_
  exact (PiTensorProduct.map_tprod _ _).trans
    (congrArg _ (funext fun _ ↦ congrArg _ (PiTensorProduct.map_tprod _ _)))

/-- The comparison lies over the inverse transitivity isomorphism of the coefficients. -/
private theorem transitivityHom_augmentation (A : SmoothDiscreteTopRep.{0, v, v} R V)
    (hA : ∀ a : A.obj.V, a + a = 0) :
    letI : V.FiniteIndex := Subgroup.finiteIndex_of_finiteIndex_subgroupOf V U
    ∀ x : ((toSmoothDiscrete R G).obj (DiscreteRep.tensorInduced V hV
      (Subgroup.compositeLeftTransversal hVU s t) ((ofSmoothDiscrete R V).obj A))).obj.V,
    (transitivityHom hVU s t hU hV A hA).hom.hom
        (PiTensorProduct.map (fun _ ↦ A.obj.gradedResolutionAugmentation) x) =
      PiTensorProduct.map (fun _ ↦
          (smoothTensorInducedSubgroupOf hVU t hV A).obj.gradedResolutionAugmentation)
        ((smoothTensorInducedTransitivityIso hVU s t hU hV A).inv.hom.hom x) := by
  let _ : V.FiniteIndex := Subgroup.finiteIndex_of_finiteIndex_subgroupOf V U
  let B := (ofSmoothDiscrete R V).obj A
  let : Module R B.V := B.module
  let C := (ofSmoothDiscrete R U).obj (smoothTensorInducedSubgroupOf hVU t hV A)
  let : Module R C.V := C.module
  have h : ((transitivityHom hVU s t hU hV A hA).hom.hom.toLinearMap ∘ₗ
      PiTensorProduct.map (fun _ ↦ A.obj.gradedResolutionAugmentation) :
        (⨂[R] _ : G ⧸ V, B.V) →ₗ[R] _) =
      PiTensorProduct.map (fun _ ↦
          (smoothTensorInducedSubgroupOf hVU t hV A).obj.gradedResolutionAugmentation) ∘ₗ
        ((smoothTensorInducedTransitivityIso hVU s t hU hV A).inv.hom.hom.toLinearMap :
          (⨂[R] _ : G ⧸ V, B.V) →ₗ[R] ⨂[R] _ : G ⧸ U, C.V) := by
    refine PiTensorProduct.ext (MultilinearMap.ext fun m ↦ ?_)
    let e := Subgroup.quotientEquivProdOfLE' hVU (Subgroup.leftTransversalRep U s)
      (Subgroup.leftTransversalRep_mk U s)
    refine Eq.trans ?_ ((LinearMap.compMultilinearMap_apply _ _ _).trans
      (LinearMap.comp_apply _ _ _)).symm
    refine (congrArg (transitivityHom hVU s t hU hV A hA).hom.hom
      (PiTensorProduct.map_tprod (fun _ : G ⧸ V ↦ A.obj.gradedResolutionAugmentation) m)).trans ?_
    refine (transitivityHom_apply hVU s t hU hV A hA _).trans ?_
    refine (congrArg _ ((congrArg _ (Subgroup.tensorInducedTransitivityLinearEquiv_symm_tprod hVU s
      _)).trans (PiTensorProduct.map_tprod _ _))).trans ?_
    refine (PiTensorProduct.map_tprod _ _).trans ?_
    refine Eq.trans ?_ ((congrArg _ (smoothTensorInducedTransitivityIso_inv_apply_tprod hVU s t hU
      hV A m)).trans (PiTensorProduct.map_tprod _ _)).symm
    refine congrArg _ (funext fun a ↦ ?_)
    refine (congrArg _ ((PiTensorProduct.map_tprod _ _).trans (congrArg _ (funext fun b ↦
      smoothGradedResolutionResSubgroupOf_augmentation hVU A (m (e.symm (a, b))))))).trans ?_
    exact (congrArg _ (PiTensorProduct.map_tprod _ _).symm).trans
      (smoothTensorInducedGradedResolutionComparison_augmentation (V.subgroupOf U)
        (U.subgroupOf_isOpen V hV) t (smoothResSubgroupOf hVU A) hA _)
  exact fun x ↦ LinearMap.congr_fun h x

variable [Fintype (G ⧸ U)] [Fintype (G ⧸ V)]

/-- The comparison preserves the total degree. -/
private theorem isHomogeneous_transitivityHom (A : SmoothDiscreteTopRep.{0, v, v} R V)
    (hA : ∀ a : A.obj.V, a + a = 0) :
    letI : V.FiniteIndex := Subgroup.finiteIndex_of_finiteIndex_subgroupOf V U
    LinearMap.IsHomogeneous (transitivityHom hVU s t hU hV A hA).hom.hom.toLinearMap
      (smoothTensorInducedGradedResolutionPiece V hV (Subgroup.compositeLeftTransversal hVU s t) A)
      (smoothTensorInducedGradedResolutionPiece U hU s
        (smoothTensorInducedSubgroupOf hVU t hV A)) 0 := by
  let _ : V.FiniteIndex := Subgroup.finiteIndex_of_finiteIndex_subgroupOf V U
  have hres := PiTensorProduct.isHomogeneous_map (ι := G ⧸ U) (a := fun _ ↦ 0)
    (g := fun _ ↦ PiTensorProduct.map
      (fun _ : U ⧸ V.subgroupOf U ↦
        (smoothGradedResolutionResSubgroupOf hVU A).hom.hom.toLinearMap))
    (𝒩 := fun _ ↦ PiTensorProduct.totalDegreePiece (U ⧸ V.subgroupOf U)
      (fun _ ↦ A.obj.gradedResolutionPiece))
    (ℳ := fun _ ↦ smoothTensorInducedGradedResolutionPiece (V.subgroupOf U)
      (U.subgroupOf_isOpen V hV) t (smoothResSubgroupOf hVU A)) fun _ ↦ by
    have h := PiTensorProduct.isHomogeneous_map (ι := U ⧸ V.subgroupOf U) (a := fun _ ↦ 0)
      fun _ ↦ isHomogeneous_smoothGradedResolutionResSubgroupOf hVU A
    rwa [Finset.sum_const_zero] at h
  have hcmp := PiTensorProduct.isHomogeneous_map (ι := G ⧸ U) (a := fun _ ↦ 0)
    (g := fun _ ↦ (smoothTensorInducedGradedResolutionComparison (V.subgroupOf U)
      (U.subgroupOf_isOpen V hV) t (smoothResSubgroupOf hVU A) hA).hom.hom.toLinearMap)
    (𝒩 := fun _ ↦ smoothTensorInducedGradedResolutionPiece (V.subgroupOf U)
      (U.subgroupOf_isOpen V hV) t (smoothResSubgroupOf hVU A)) fun _ ↦
    isHomogeneous_smoothTensorInducedGradedResolutionComparison (V.subgroupOf U)
      (U.subgroupOf_isOpen V hV) t (smoothResSubgroupOf hVU A) hA
  rw [Finset.sum_const_zero] at hres hcmp
  refine LinearMap.isHomogeneous_def.2 fun p x hx ↦ ?_
  rw [add_zero]
  have hx' : (Subgroup.tensorInducedTransitivityLinearEquiv hVU s).symm x ∈
      PiTensorProduct.totalDegreePiece (G ⧸ U) (fun _ ↦ PiTensorProduct.totalDegreePiece
        (U ⧸ V.subgroupOf U) (fun _ ↦ A.obj.gradedResolutionPiece)) p := by
    refine (Subgroup.tensorInducedTransitivityLinearEquiv_mem_totalDegreePiece_iff hVU s
      A.obj.gradedResolutionPiece p _).1 ?_
    exact (congrArg (· ∈ _) (LinearEquiv.apply_symm_apply _ x)).mpr hx
  have h := hcmp.map_mem (hres.map_mem hx')
  rw [add_zero, add_zero] at h
  exact (congrArg (· ∈ _) (transitivityHom_apply hVU s t hU hV A hA x)).mpr h

/-- The comparison commutes with the slot-sum differentials. -/
private theorem transitivityHom_differential (A : SmoothDiscreteTopRep.{0, v, v} R V)
    (hA : ∀ a : A.obj.V, a + a = 0) (x : ⨂[R] _ : G ⧸ V, A.obj.gradedResolutionModule) :
    letI : V.FiniteIndex := Subgroup.finiteIndex_of_finiteIndex_subgroupOf V U
    (transitivityHom hVU s t hU hV A hA).hom.hom
        ((smoothTensorInducedGradedResolutionDifferential V hV
          (Subgroup.compositeLeftTransversal hVU s t) A).hom.hom x) =
      (smoothTensorInducedGradedResolutionDifferential U hU s
        (smoothTensorInducedSubgroupOf hVU t hV A)).hom.hom
        ((transitivityHom hVU s t hU hV A hA).hom.hom x) := by
  let _ : V.FiniteIndex := Subgroup.finiteIndex_of_finiteIndex_subgroupOf V U
  let _ : DecidableEq (G ⧸ U) := Classical.decEq _
  let _ : DecidableEq (G ⧸ V) := Classical.decEq _
  let ρ := (smoothGradedResolutionResSubgroupOf hVU A).hom.hom.toLinearMap
  let κ := (smoothTensorInducedGradedResolutionComparison (V.subgroupOf U)
    (U.subgroupOf_isOpen V hV) t (smoothResSubgroupOf hVU A) hA).hom.hom.toLinearMap
  -- The restriction of the total resolution commutes with the total differentials, so its
  -- factorwise tensor power commutes with their slot sums.
  have hρ : (smoothResSubgroupOf hVU A).obj.gradedResolutionDifferential ∘ₗ ρ =
      ρ ∘ₗ A.obj.gradedResolutionDifferential :=
    LinearMap.ext fun y ↦ (smoothGradedResolutionResSubgroupOf_differential hVU A y).symm
  have hρρ : PiTensorProduct.slotSum (U ⧸ V.subgroupOf U)
        (fun _ ↦ (smoothResSubgroupOf hVU A).obj.gradedResolutionDifferential) ∘ₗ
        PiTensorProduct.map (fun _ ↦ ρ) =
      PiTensorProduct.map (fun _ ↦ ρ) ∘ₗ PiTensorProduct.slotSum (U ⧸ V.subgroupOf U)
        (fun _ ↦ A.obj.gradedResolutionDifferential) :=
    PiTensorProduct.slotSum_comp_map _ fun _ ↦ hρ
  have hκ : (smoothTensorInducedSubgroupOf hVU t hV A).obj.gradedResolutionDifferential ∘ₗ κ =
      κ ∘ₗ PiTensorProduct.slotSum (U ⧸ V.subgroupOf U)
        (fun _ ↦ (smoothResSubgroupOf hVU A).obj.gradedResolutionDifferential) :=
    LinearMap.ext fun y ↦ (smoothTensorInducedGradedResolutionComparison_slotSum (V.subgroupOf U)
      (U.subgroupOf_isOpen V hV) t (smoothResSubgroupOf hVU A) hA y).symm
  have hL : (Subgroup.tensorInducedTransitivityLinearEquiv hVU s).symm
      (PiTensorProduct.slotSum (G ⧸ V) (fun _ ↦ A.obj.gradedResolutionDifferential) x) =
        PiTensorProduct.slotSum (G ⧸ U) (fun _ ↦ PiTensorProduct.slotSum (U ⧸ V.subgroupOf U)
          (fun _ ↦ A.obj.gradedResolutionDifferential))
          ((Subgroup.tensorInducedTransitivityLinearEquiv hVU s).symm x) := by
    refine ((LinearEquiv.symm_apply_eq _).2 ?_)
    refine Eq.trans ?_ (Subgroup.tensorInducedTransitivityLinearEquiv_slotSum hVU s _ _).symm
    rw [LinearEquiv.apply_symm_apply]
  refine (transitivityHom_apply hVU s t hU hV A hA _).trans ?_
  refine Eq.trans ?_ (smoothTensorInducedGradedResolutionDifferential_apply.{0, v, v} U hU s
    _ _).symm
  refine Eq.trans ?_ (congrArg _ (transitivityHom_apply hVU s t hU hV A hA x).symm)
  refine (congrArg (PiTensorProduct.map fun _ : G ⧸ U ↦ κ) (congrArg (PiTensorProduct.map
    fun _ : G ⧸ U ↦ PiTensorProduct.map fun _ : U ⧸ V.subgroupOf U ↦ ρ)
      ((congrArg _ (smoothTensorInducedGradedResolutionDifferential_apply V hV _ A x)).trans
        hL))).trans ?_
  -- Restrict each factor, then compare it with the total resolution: both commute with the slot
  -- sums of the differentials.
  refine (congrArg (PiTensorProduct.map fun _ : G ⧸ U ↦ κ) (LinearMap.congr_fun
    (PiTensorProduct.slotSum_comp_map (fun _ ↦ PiTensorProduct.map fun _ ↦ ρ)
      fun _ ↦ hρρ).symm _)).trans ?_
  exact (LinearMap.congr_fun (PiTensorProduct.slotSum_comp_map (fun _ ↦ κ) fun _ ↦ hκ) _).symm

/-- **Transitivity of the norm of a cocycle.** Let `V ≤ U ≤ G` be compact open subgroups of finite
index and `z` a `V`-invariant cocycle of degree `n` of the total resolution of `A`, in which every
element is its own additive inverse. Let `y` be the cocycle of the total resolution of the
intermediate coefficients `Ind⊗_V^U A` representing the norm from `V` to `U` of `z`
(`TauCeti.gradedCohomologyClass_smoothTensorInducedGradedResolutionComparison`): the image under
the comparison of the diagonal tensor of the restriction of `z` to `V.subgroupOf U`. Then the norm
from `V` to `G` of `z`, transported along the transitivity isomorphism
`Ind⊗_V^G A ≅ Ind⊗_U^G Ind⊗_V^U A`, is the norm from `U` to `G` of `y`, after transporting the
degree `[G : U] ([U : V] n)` to `[G : V] n`. -/
theorem coeffMap_smoothTensorInducedDiagonalClass_transitivity
    (A : SmoothDiscreteTopRep.{0, v, v} R V) (hA : ∀ a : A.obj.V, a + a = 0) {n : ℕ}
    {z : A.obj.gradedResolutionModule} (hz : z ∈ A.obj.gradedResolutionPiece n)
    (hinv : ∀ u, A.obj.gradedResolutionTopRep.ρ u z = z)
    (hdz : A.obj.gradedResolutionDifferential z = 0)
    {y : (smoothTensorInducedSubgroupOf hVU t hV A).obj.gradedResolutionModule}
    (hy : y ∈ (smoothTensorInducedSubgroupOf hVU t hV A).obj.gradedResolutionPiece
      (Fintype.card (U ⧸ V.subgroupOf U) * n : ℕ))
    (hyinv : ∀ u, (smoothTensorInducedSubgroupOf hVU t hV A).obj.gradedResolutionTopRep.ρ u y = y)
    (hdy : (smoothTensorInducedSubgroupOf hVU t hV A).obj.gradedResolutionDifferential y = 0)
    (hyz : y = (smoothTensorInducedGradedResolutionComparison (V.subgroupOf U)
      (U.subgroupOf_isOpen V hV) t (smoothResSubgroupOf hVU A) hA).hom.hom
        (PiTensorProduct.tprod R fun _ : U ⧸ V.subgroupOf U ↦
          (smoothGradedResolutionResSubgroupOf hVU A).hom.hom z)) :
    letI : V.FiniteIndex := Subgroup.finiteIndex_of_finiteIndex_subgroupOf V U
    TauCeti.ContinuousCohomology.coeffMap
        (smoothTensorInducedTransitivityIso hVU s t hU hV A).inv.hom
        (Fintype.card (G ⧸ V) * n)
        (smoothTensorInducedDiagonalClass V hV (Subgroup.compositeLeftTransversal hVU s t) A hA z hz
          hinv hdz) =
      (TauCeti.ContinuousCohomology.degreeCast _ (by
        rw [Fintype.card_congr (Subgroup.quotientEquivProdOfLE hVU), Fintype.card_prod,
          mul_assoc])).hom
        (smoothTensorInducedDiagonalClass U hU s (smoothTensorInducedSubgroupOf hVU t hV A)
          (smoothTensorInducedSubgroupOf_add_self hVU t hV A hA) y hy hyinv hdy) := by
  let _ : V.FiniteIndex := Subgroup.finiteIndex_of_finiteIndex_subgroupOf V U
  let _ : LinearOrder (G ⧸ V) := LinearOrder.lift' _ (Fintype.equivFin (G ⧸ V)).injective
  let _ : LinearOrder (G ⧸ U) := LinearOrder.lift' _ (Fintype.equivFin (G ⧸ U)).injective
  have : LocallyCompactSpace G :=
    (isCompact_iff_compactSpace.2 ‹CompactSpace V›).locallyCompactSpace_of_mem_nhds_of_group
      (hV.mem_nhds V.one_mem)
  rw [smoothTensorInducedDiagonalClass_eq, smoothTensorInducedDiagonalClass_eq,
    TauCeti.ContinuousCohomology.coeffMap_def]
  refine (TopRep.ResolutionContraction.map_gradedCohomologyClass (ContinuousMonoidHom.id G)
    (smoothTensorInducedGradedResolutionContraction V hV (Subgroup.compositeLeftTransversal hVU s t)
      A hA)
    (smoothTensorInducedGradedResolutionContraction U hU s
      (smoothTensorInducedSubgroupOf hVU t hV A)
      (smoothTensorInducedSubgroupOf_add_self hVU t hV A hA))
    (smoothTensorInducedTransitivityIso hVU s t hU hV A).inv.hom
    (transitivityHom hVU s t hU hV A hA).hom
    (isHomogeneous_transitivityHom hVU s t hU hV A hA) ?_ ?_ _ _ _).trans ?_
  · refine TopRep.hom_ext (ContIntertwiningMap.ext (ContinuousLinearMap.ext fun x ↦ ?_))
    exact transitivityHom_differential hVU s t hU hV A hA x
  · intro x
    refine (congrArg _ (smoothTensorInducedGradedResolutionContraction_ι_apply V hV _ A hA x)).trans
      ((transitivityHom_augmentation hVU s t hU hV A hA x).trans ?_)
    exact (smoothTensorInducedGradedResolutionContraction_ι_apply U hU s _ _ _).symm
  · refine TopRep.ResolutionContraction.gradedCohomologyClass_degreeCast _ _ ?_ _ _ _ _ _ _
    exact (transitivityHom_tprod_const hVU s t hU hV A hA z).trans
      (congrArg _ (funext fun _ ↦ hyz.symm))

end TauCeti
