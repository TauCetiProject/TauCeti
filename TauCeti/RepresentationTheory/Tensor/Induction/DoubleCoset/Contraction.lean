/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Tensor.Induction.DoubleCoset.Complex
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Resolution.Transport
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Resolution.ChangeOfGroup

/-!
# Contracting the Mackey-decomposed tensor resolution

The orbitwise tensor complex in the Mackey decomposition is a resolution of the restriction
of the tensor-induced coefficients. Restrict the contraction of the ambient tensor resolution
and pull it back along the Mackey chain isomorphism. Its augmentation is the inverse coefficient
Mackey comparison followed by the orbitwise tensor augmentation in every factor.

When `V` is locally compact, an invariant cocycle in the orbitwise complex has a canonical
continuous cohomology class. Restriction of a class computed in the ambient tensor resolution can be
computed in the orbitwise complex via the Mackey comparison. This is
the additive comparison needed before identifying the orbitwise class with a cup product.

## References

* L. Evens, *A generalization of the transfer map in the cohomology of groups*, Trans. Amer.
  Math. Soc. **108** (1963), §6, Proposition 2.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti

universe u v w

variable {R : Type u} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (U V : Subgroup G) (hU : IsOpen (U : Set G)) [U.FiniteIndex] [CompactSpace U]
  (r : DoubleCoset.Quotient (V : Set G) (U : Set G) → G)
  (hr : ∀ D, DoubleCoset.mk V U (r D) = D)
  (t : ∀ D, ((mackeySubgroup (r D) U V).subgroupOf V).LeftTransversal)
  (s : U.LeftTransversal) (A : SmoothDiscreteTopRep.{u, v, max v w} R U)
  [Fintype (DoubleCoset.Quotient (V : Set G) (U : Set G))]
  [∀ D, Fintype (V ⧸ (mackeySubgroup (r D) U V).subgroupOf V)] [Fintype (G ⧸ U)]
  [LinearOrder (G ⧸ U)]
  (hA : ∀ a : A.obj.V, a + a = 0)

/-- The Mackey-decomposed tensor complex contracts onto the restriction to `V` of the
coefficients tensor induced from `U` to `G`. No compactness or openness of `V` is needed. -/
noncomputable def smoothTensorInducedMackeyResolutionContraction :
    TopRep.ResolutionContraction.{u, v, max u w}
      (TopRep.res V.subtype ((toSmoothDiscrete R G).obj
        (DiscreteRep.tensorInduced U hU s ((ofSmoothDiscrete R U).obj A))).obj)
      (smoothTensorInducedMackeyResolution U V hU r hr t s A hA) :=
  TopRep.ResolutionContraction.ofIso.{u, v, max u w}
    (TopRep.ResolutionContraction.res.{u, v, max u w}
      (ContinuousMonoidHom.subgroupSubtype V)
      (smoothTensorInducedGradedResolutionContraction U hU s A hA))
    (smoothTensorInducedMackeyResolutionResIso U V hU r hr t s A hA)

/-- The augmentation of the orbitwise contraction is the restricted ambient augmentation
followed by the inverse Mackey chain comparison. -/
theorem smoothTensorInducedMackeyResolutionContraction_ι :
    (smoothTensorInducedMackeyResolutionContraction U V hU r hr t s A hA).ι =
      (TopRep.resFunctor V.subtype).map
        (smoothTensorInducedGradedResolutionContraction U hU s A hA).ι ≫
          (smoothTensorInducedMackeyResolutionResIso U V hU r hr t s A hA).inv.f 0 := by
  unfold smoothTensorInducedMackeyResolutionContraction
  refine (TopRep.ResolutionContraction.ofIso_ι _ _).trans ?_
  rw [TopRep.ResolutionContraction.res_ι]
  -- Forgetting continuity of the subgroup inclusion gives precisely `V.subtype`.
  rfl

/-- Applying the Mackey chain comparison to the orbitwise augmentation recovers the
restricted ambient augmentation. -/
@[reassoc]
theorem smoothTensorInducedMackeyResolutionContraction_ι_comp_resolutionResIso_hom_f_zero :
    (smoothTensorInducedMackeyResolutionContraction U V hU r hr t s A hA).ι ≫
        (smoothTensorInducedMackeyResolutionResIso U V hU r hr t s A hA).hom.f 0 =
      (TopRep.resFunctor V.subtype).map
        (smoothTensorInducedGradedResolutionContraction U hU s A hA).ι := by
  rw [smoothTensorInducedMackeyResolutionContraction_ι, Category.assoc,
    ← HomologicalComplex.comp_f, Iso.inv_hom_id]
  simp

-- Not a simp rule: the restricted coefficient carrier and its tensor presentation agree only
-- at semireducible transparency, even when simplification runs top-down.
/-- On orbitwise coefficient tensors the augmentation applies the original augmentation in
every factor. The coefficient Mackey comparison identifies its input with the restricted
tensor-induced coefficients. -/
theorem smoothTensorInducedMackeyResolutionContraction_ι_apply_smoothTensorInducedMackeyIso_hom
    (x : ⨂[R] D : DoubleCoset.Quotient (V : Set G) (U : Set G),
      ⨂[R] _ : V ⧸ (mackeySubgroup (r D) U V).subgroupOf V, A.obj.V) :
    ((smoothTensorInducedMackeyResolutionContraction U V hU r hr t s A hA).ι.hom
        ((smoothTensorInducedMackeyIso U V hU r hr t s A).hom.hom.hom x)).1 =
      PiTensorProduct.map (fun _ ↦ PiTensorProduct.map
        (fun _ ↦ A.obj.gradedResolutionAugmentation)) x := by
  let e := (smoothDiscreteι R V).mapIso
    (smoothTensorInducedMackeyIso U V hU r hr t s (smoothGradedResolutionFunctor.obj A))
  apply (ConcreteCategory.bijective_of_isIso e.hom).injective
  have hc := congrArg Subtype.val (ConcreteCategory.congr_hom
    (smoothTensorInducedMackeyResolutionContraction_ι_comp_resolutionResIso_hom_f_zero
      U V hU r hr t s A hA)
    ((smoothTensorInducedMackeyIso U V hU r hr t s A).hom.hom.hom x))
  -- Use the restricted application formula to identify the homogeneous carriers explicitly.
  have hm := smoothTensorInducedMackeyResolutionResIso_hom_f_apply
    U V hU r hr t s A hA 0
    ((smoothTensorInducedMackeyResolutionContraction U V hU r hr t s A hA).ι.hom
      ((smoothTensorInducedMackeyIso U V hU r hr t s A).hom.hom.hom x))
  have hc := hm.symm.trans hc
  have hres := congrArg
    (fun f ↦ (f ((smoothTensorInducedMackeyIso U V hU r hr t s A).hom.hom.hom x)).1)
    (TopRep.resFunctor_map_hom V.subtype
      (smoothTensorInducedGradedResolutionContraction U hU s A hA).ι)
  have haug := smoothTensorInducedGradedResolutionContraction_ι_apply U hU s A hA
    ((smoothTensorInducedMackeyIso U V hU r hr t s A).hom.hom.hom x)
  exact (hc.trans (hres.trans haug)).trans
    (smoothTensorInducedMackeyIso_resolutionAugmentation U V hU r hr t s A x).symm

/-- On an arbitrary restricted coefficient vector, the augmentation first applies the inverse
coefficient Mackey comparison and then augments every orbit factor. -/
theorem smoothTensorInducedMackeyResolutionContraction_ι_apply
    (y : ((toSmoothDiscrete R G).obj
      (DiscreteRep.tensorInduced U hU s ((ofSmoothDiscrete R U).obj A))).obj.V) :
    ((smoothTensorInducedMackeyResolutionContraction U V hU r hr t s A hA).ι.hom y).1 =
      PiTensorProduct.map (fun _ ↦ PiTensorProduct.map
        (fun _ ↦ A.obj.gradedResolutionAugmentation))
        ((smoothTensorInducedMackeyIso U V hU r hr t s A).inv.hom.hom y) := by
  have h := smoothTensorInducedMackeyResolutionContraction_ι_apply_smoothTensorInducedMackeyIso_hom
    U V hU r hr t s A hA ((smoothTensorInducedMackeyIso U V hU r hr t s A).inv.hom.hom y)
  have he : (smoothTensorInducedMackeyIso U V hU r hr t s A).hom.hom.hom
      ((smoothTensorInducedMackeyIso U V hU r hr t s A).inv.hom.hom y) = y :=
    congrArg (fun f ↦ f.hom.hom y) (smoothTensorInducedMackeyIso U V hU r hr t s A).inv_hom_id
  rw [he] at h
  exact h

-- Not a simp rule: its coefficient-valued result crosses the same restricted/tensor carrier
-- identification as the augmentation. Use the computed equation explicitly.
/-- The retraction of the orbitwise resolution first regroups into the ambient resolution
and then applies its tensor projection. -/
theorem smoothTensorInducedMackeyResolutionContraction_proj_apply
    (z : ((smoothTensorInducedMackeyResolution U V hU r hr t s A hA).X 0).V) :
    (smoothTensorInducedMackeyResolutionContraction U V hU r hr t s A hA).proj z =
      smoothTensorInducedGradedResolutionProjection U A
        ((smoothTensorInducedMackeyIso U V hU r hr t s
          (smoothGradedResolutionFunctor.obj A)).hom.hom.hom z.1) := by
  unfold smoothTensorInducedMackeyResolutionContraction
  refine (TopRep.ResolutionContraction.ofIso_proj_apply _ _ z).trans ?_
  rw [TopRep.ResolutionContraction.res_proj]
  -- Restriction keeps the native homogeneous carrier and the ambient projection.
  exact (smoothTensorInducedGradedResolutionContraction_proj_apply U hU s A hA _).trans
    (congrArg _
      (smoothTensorInducedMackeyResolutionResIso_hom_f_apply U V hU r hr t s A hA 0 z))

/-- The orbitwise homotopy is the conjugate of the ambient tensor homotopy by the Mackey
comparison. -/
@[simp] theorem smoothTensorInducedMackeyResolutionContraction_hom_apply (n : ℕ)
    (z : ((smoothTensorInducedMackeyResolution U V hU r hr t s A hA).X (n + 1)).V) :
    ((smoothTensorInducedMackeyResolutionContraction U V hU r hr t s A hA).hom n z).1 =
      (smoothTensorInducedMackeyIso U V hU r hr t s
        (smoothGradedResolutionFunctor.obj A)).inv.hom.hom
        (smoothTensorInducedGradedResolutionHomotopy U A
          ((smoothTensorInducedMackeyIso U V hU r hr t s
            (smoothGradedResolutionFunctor.obj A)).hom.hom.hom z.1)) := by
  unfold smoothTensorInducedMackeyResolutionContraction
  refine (congrArg Subtype.val (TopRep.ResolutionContraction.ofIso_hom_apply _ _ n z)).trans ?_
  refine (smoothTensorInducedMackeyResolutionResIso_inv_f_apply
    U V hU r hr t s A hA n _).trans ?_
  rw [TopRep.ResolutionContraction.res_hom]
  -- Restriction keeps the native homogeneous carriers and the ambient homotopy.
  exact congrArg _ ((smoothTensorInducedGradedResolutionContraction_hom_apply U hU s A hA n
    _).trans (congrArg _ (smoothTensorInducedMackeyResolutionResIso_hom_f_apply
      U V hU r hr t s A hA (n + 1) z)))

/-- Restriction of a class computed on the ambient tensor resolution is computed on the
orbitwise tensor resolution by the inverse Mackey comparison. This holds in every degree
and for any number of double cosets. -/
theorem res_cohomologyClass_smoothTensorInducedGradedResolutionContraction_mackey
    [LocallyCompactSpace V]
    {n : ℕ}
    (z : ((((smoothTensorInducedGradedResolutionFunctor U hU s).obj A).obj.gradedCochainComplex
      (smoothTensorInducedGradedResolutionPiece U hU s A)
      (smoothTensorInducedGradedResolutionPiece_ρ_mem U hU s A)
      (smoothTensorInducedGradedResolutionDifferential U hU s A).hom
      (isHomogeneous_smoothTensorInducedGradedResolutionDifferential U hU s A)
      (smoothTensorInducedGradedResolutionDifferential_sq U hU s A hA)).X n).ρ.invariants)
    (hz) :
    ContinuousCohomology.res V _ n
        ((smoothTensorInducedGradedResolutionContraction U hU s A hA).cohomologyClass z hz) =
      (smoothTensorInducedMackeyResolutionContraction U V hU r hr t s A hA).cohomologyClass
        (((smoothTensorInducedMackeyResolutionResIso U V hU r hr t s A hA).inv.f n).hom
          |>.mapInvariants
            (Submodule.inclusion (ContRepresentation.invariants_le_invariants_restrict _
              V.subtype) z))
        (TopRep.d_mapInvariants_f_apply
          (smoothTensorInducedMackeyResolutionResIso U V hU r hr t s A hA).inv
          (Submodule.inclusion (ContRepresentation.invariants_le_invariants_restrict _
            V.subtype) z) hz) := by
  rw [TopRep.ResolutionContraction.res_cohomologyClass]
  symm
  exact TopRep.ResolutionContraction.cohomologyClass_map.{u, v, max u w}
    (TopRep.ResolutionContraction.res.{u, v, max u w}
      (ContinuousMonoidHom.subgroupSubtype V)
      (smoothTensorInducedGradedResolutionContraction U hU s A hA))
    (smoothTensorInducedMackeyResolutionContraction U V hU r hr t s A hA)
    (smoothTensorInducedMackeyResolutionResIso U V hU r hr t s A hA).inv
    (by
      rw [TopRep.ResolutionContraction.res_ι]
      exact (smoothTensorInducedMackeyResolutionContraction_ι U V hU r hr t s A hA).symm) _ _

/-- Restriction of the class of a homogeneous total-resolution cocycle is represented by its
inverse Mackey regrouping in the orbitwise total module. -/
theorem res_gradedCohomologyClass_smoothTensorInducedGradedResolutionContraction_mackey
    [LocallyCompactSpace V] {n : ℕ}
    (z : ((smoothTensorInducedGradedResolutionFunctor U hU s).obj A).obj.V)
    (hz : z ∈ smoothTensorInducedGradedResolutionPiece U hU s A n)
    (hinv : ∀ g, ((smoothTensorInducedGradedResolutionFunctor U hU s).obj A).obj.ρ g z = z)
    (hdz : (smoothTensorInducedGradedResolutionDifferential U hU s A).hom.hom z = 0) :
    ContinuousCohomology.res V _ n
        ((smoothTensorInducedGradedResolutionContraction U hU s A hA).gradedCohomologyClass
          z hz hinv hdz) =
      (smoothTensorInducedMackeyResolutionContraction U V hU r hr t s A hA).gradedCohomologyClass
        ((smoothTensorInducedMackeyIso U V hU r hr t s
          (smoothGradedResolutionFunctor.obj A)).inv.hom.hom z)
        (smoothTensorInducedMackeyIso_inv_mem_resolutionPiece U V hU r hr t s A n z hz)
        (fun g ↦ by
          let F := (smoothDiscreteι R V).map (smoothTensorInducedMackeyIso
            U V hU r hr t s (smoothGradedResolutionFunctor.obj A)).inv
          exact (TopRep.hom_comm_apply F g z).symm.trans (congrArg F.hom (hinv g.val)))
        (by
          refine
            (smoothTensorInducedMackeyResolutionDifferential_apply_smoothTensorInducedMackeyIso_inv
              U V hU r hr t s A z).trans ?_
          exact (congrArg (smoothTensorInducedMackeyIso U V hU r hr t s
            (smoothGradedResolutionFunctor.obj A)).inv.hom.hom hdz).trans (map_zero _)) := by
  rw [TopRep.ResolutionContraction.gradedCohomologyClass_def,
    res_cohomologyClass_smoothTensorInducedGradedResolutionContraction_mackey
      U V hU r hr t s A hA]
  rw [TopRep.ResolutionContraction.gradedCohomologyClass_def
    (smoothTensorInducedMackeyResolutionContraction U V hU r hr t s A hA)]
  congr 1
  apply Subtype.ext
  apply Subtype.ext
  rw [ContIntertwiningMap.mapInvariants_apply,
    smoothTensorInducedMackeyResolutionResIso_inv_f_apply,
    Submodule.coe_inclusion, TopRep.gradedCochainComplexInvariant_val,
    TopRep.gradedCochainComplexInvariant_val]

end TauCeti
